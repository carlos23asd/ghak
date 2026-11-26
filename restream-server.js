/**
 * restream-server.js
 * Servidor de restream IPTV con FFmpeg
 *
 * Lógica:
 * - Cada canal activo tiene UN solo proceso FFmpeg (copy) compartido entre todos los viewers
 * - Si el canal ya tiene FFmpeg activo, se reutiliza el stream
 * - Si pasan 20 min sin viewers, el FFmpeg se apaga solo
 * - Las listas tienen límite de 3 conexiones simultáneas al servidor IPTV
 * - Si una lista está llena (3 streams activos), se usa otra lista disponible con las mismas credenciales de contenido
 * - Los streams se sirven como HLS local
 */

const http = require('http');
const https = require('https');
const { spawn } = require('child_process');
const fs = require('fs');
const path = require('path');
const url = require('url');
const { validateToken } = require('./stream-token');
const crypto = require('crypto');
const optimizer = require('./restream-optimizer');

// Verificar token admin (mismo mecanismo que server.js)
function verifyAdminToken(token) {
  try {
    const decoded = Buffer.from(token, 'base64').toString('utf8');
    const [email, hash] = decoded.split(':');
    if (!email || !hash) return false;
    // Leer DB para verificar
    const initSqlJs = require('sql.js');
    const dbPath = require('path').join(__dirname, 'data', 'iptv.db');
    if (!require('fs').existsSync(dbPath)) return false;
    // Verificación síncrona simple — leer el hash del admin del archivo
    // Como sql.js es async, usamos una caché en memoria
    return _adminCache.has(`${email}:${hash}`);
  } catch { return false; }
}

// Caché de admins válidos — se llena al arrancar y se refresca cada 5 min
const _adminCache = new Set();
// Caché de usernames userId → username
const _usernameCache = new Map();
// Caché de max_dispositivos userId → número
const _maxDispCache = new Map();

async function refreshAdminCache() {
  try {
    const initSqlJs = require('sql.js');
    const fs = require('fs');
    const dbPath = require('path').join(__dirname, 'data', 'iptv.db');
    if (!fs.existsSync(dbPath)) return;
    const SQL = await initSqlJs();
    const db = new SQL.Database(fs.readFileSync(dbPath));
    const result = db.exec(`SELECT email, password_hash FROM usuarios WHERE es_admin=1 AND activo=1`);
    _adminCache.clear();
    if (result.length && result[0].values) {
      result[0].values.forEach(([email, hash]) => _adminCache.add(`${email}:${hash}`));
    }
    // Cargar usernames y max_dispositivos
    const uResult = db.exec(`SELECT id, username, max_dispositivos FROM usuarios`);
    if (uResult.length && uResult[0].values) {
      uResult[0].values.forEach(([id, username, maxDisp]) => {
        _usernameCache.set(String(id), username);
        _maxDispCache.set(String(id), maxDisp || 1);
      });
    }
    db.close();
  } catch (e) { console.error('[RESTREAM] Error cargando admins:', e.message); }
}

function getUsernameById(userId) {
  return _usernameCache.get(String(userId)) || `user_${userId}`;
}
refreshAdminCache();
setInterval(refreshAdminCache, 5 * 60 * 1000);

// ─── Verificación de firma de la app Android ─────────────────────────────────
const APP_SECRET = Buffer.from('4c7b5c655905841' + '18ee2698947bf76d' + '6bc55c10026396cd8');
const APP_SIG_WINDOW_SEC = 60;

function verifyAppSig(req) {
  const sig = req.headers['x-app-sig'];
  const ts  = req.headers['x-app-ts'];
  const did = req.headers['x-app-did'];
  if (!sig || !ts || !did) return false;
  const tsNum = parseInt(ts, 10);
  if (isNaN(tsNum)) return false;
  const diff = Math.abs(Math.floor(Date.now() / 1000) - tsNum);
  if (diff > APP_SIG_WINDOW_SEC) return false;
  const payload = `${did}:${ts}`;
  const expected = crypto.createHmac('sha256', APP_SECRET).update(payload).digest('hex');
  if (expected.length !== sig.length) return false;
  let diff2 = 0;
  for (let i = 0; i < expected.length; i++) {
    diff2 |= expected.charCodeAt(i) ^ sig.charCodeAt(i);
  }
  return diff2 === 0;
}

const RESTREAM_PORT = 8888;
const HLS_DIR = path.join(__dirname, 'hls');
const IDLE_TIMEOUT_MS = 120 * 1000; // 120 segundos sin viewers → apagar
const MAX_STREAMS_PER_LIST = 4;
const SEGMENT_DURATION = 4; // segundos por segmento — más granular, recuperación más rápida
const SEGMENT_COUNT = 8;   // 8 x 4s = 32s de playlist en servidor

// Límite de streams FFmpeg simultáneos — configurable desde el panel admin
let MAX_CONCURRENT_STREAMS = 5;

// Dominio autorizado — en producción cambia a tu dominio real, ej: 'midominio.com'
// En desarrollo se permite localhost automáticamente
// DESACTIVADO TEMPORALMENTE PARA PRUEBAS
const ALLOWED_HOST = process.env.ALLOWED_HOST || ''; // Vacío = permite todos los hosts

// ─── Sesiones de stream ───────────────────────────────────────────────────────
// El cliente valida el token UNA vez → recibe sessionKey
// Los segmentos .ts solo necesitan la sessionKey (no el token completo)
// sessionKey → { userId, deviceId, ip, expiresAt }
const streamSessions = new Map();
const SESSION_TTL_MS = 5 * 60 * 60 * 1000; // 5 horas

function createSession(userId, deviceId, ip, ua) {
  const key = crypto.randomBytes(16).toString('hex');
  // Guardar hash del UA para no exponer el string completo en memoria
  const uaHash = crypto.createHash('sha256').update(ua || '').digest('hex');
  streamSessions.set(key, { userId, deviceId, ip, uaHash, expiresAt: Date.now() + SESSION_TTL_MS });
  return key;
}

function validateSession(key, ip, deviceId, ua) {
  const s = streamSessions.get(key);
  if (!s) return { valid: false, reason: 'Sesión no encontrada' };
  if (Date.now() > s.expiresAt) { streamSessions.delete(key); return { valid: false, reason: 'Sesión expirada' }; }
  if (s.deviceId !== deviceId) return { valid: false, reason: 'Dispositivo no coincide' };
  // Sesiones M3U no validan IP (el proxy de server.js ya lo hizo)
  if (!s.isM3u && s.ip && ip !== s.ip && ip !== '127.0.0.1') {
    // Actualizar IP si cambió (puede cambiar de red)
    s.ip = ip;
  }
  return { valid: true, userId: s.userId };
}

// Limpiar sesiones expiradas cada hora
setInterval(() => {
  const now = Date.now();
  for (const [k, s] of streamSessions.entries()) {
    if (now > s.expiresAt) streamSessions.delete(k);
  }
}, 60 * 60 * 1000);

// Asegurar que exista el directorio HLS
if (!fs.existsSync(HLS_DIR)) fs.mkdirSync(HLS_DIR, { recursive: true });

// Mapa de channelKey opaco → URL original para canales custom
const customUrlMap = new Map();

// Mapa de channelKey → lista de URLs de respaldo para failover
// { urls: [url1, url2, ...], currentIdx: 0 }
const failoverMap = new Map();

// Timeouts de failover pendientes — para poder cancelarlos al detener manualmente
const _failoverTimers = new Map();

// Lock para evitar múltiples FFmpeg del mismo canal iniciando simultáneamente
const _startingStreams = new Map(); // channelKey → Promise

// Tokens de un solo uso para segmentos .ts: token → { segFile, viewerKey, expiresAt }
const segTokens = new Map();
const SEG_TOKEN_TTL = 120000; // 120 segundos para descargar el segmento

function createSegToken(segFile, viewerKey) {
  const token = crypto.randomBytes(12).toString('hex');
  segTokens.set(token, { segFile, viewerKey, expiresAt: Date.now() + SEG_TOKEN_TTL });
  return token;
}

function consumeSegToken(token) {
  const t = segTokens.get(token);
  if (!t) return null;
  // No eliminar — permitir múltiples descargas del mismo segmento hasta que expire
  if (Date.now() > t.expiresAt) { segTokens.delete(token); return null; }
  return t;
}

// Limpiar tokens expirados cada minuto
setInterval(() => {
  const now = Date.now();
  for (const [k, t] of segTokens.entries()) {
    if (now > t.expiresAt) segTokens.delete(k);
  }
}, 60000);

// ─── DB helpers (lee data/*.txt) ────────────────────────────────────────────
const DATA_DIR = path.join(__dirname, 'data');

function readTxt(file) {
  try {
    return fs.readFileSync(path.join(DATA_DIR, file), 'utf8')
      .split('\n')
      .filter(l => l && !l.startsWith('#'));
  } catch { return []; }
}

function getListas(categoria) {
  // Leer de SQLite via db.js
  try {
    const db = require('./db');
    // db._ready es una promesa, pero getListas se llama sincrónicamente
    // Usamos sql.js directamente para lectura síncrona
    const initSqlJs = require('sql.js');
    const fs = require('fs');
    const dbPath = require('path').join(__dirname, 'data', 'iptv.db');
    if (!fs.existsSync(dbPath)) return [];
    // Usar caché en memoria para no leer el archivo en cada request
    return _listasCache.filter(l => l.activa && (!categoria || l.categoria === categoria));
  } catch { return []; }
}

// Caché de listas — se refresca cada 2 minutos
let _listasCache = [];
async function refreshListasCache() {
  try {
    const initSqlJs = require('sql.js');
    const fs = require('fs');
    const dbPath = require('path').join(__dirname, 'data', 'iptv.db');
    if (!fs.existsSync(dbPath)) return;
    const SQL = await initSqlJs();
    const sqlDb = new SQL.Database(fs.readFileSync(dbPath));
    const result = sqlDb.exec(`SELECT id, nombre, servidor, usuario_xtream, password_xtream, activa, tipo, categoria FROM listas`);
    if (result.length && result[0].values) {
      _listasCache = result[0].values.map(([id, nombre, servidor, usuario_xtream, password_xtream, activa, tipo, categoria]) => {
        let srv = (servidor || '').trim().replace(/\/$/, '');
        if (srv && !srv.startsWith('http://') && !srv.startsWith('https://')) srv = 'http://' + srv;
        return { id: String(id), nombre, servidor: srv, usuario_xtream, password_xtream, activa: !!activa, tipo, categoria: categoria || 'tv' };
      });
    }
    sqlDb.close();
  } catch (e) { console.error('[RESTREAM] Error cargando listas:', e.message); }
}
refreshListasCache();
setInterval(refreshListasCache, 2 * 60 * 1000);
// Construye la URL de stream de un canal dado las credenciales Xtream
function buildStreamUrl(lista, streamId, streamType = 'live') {
  const base = lista.servidor; // ya viene normalizado desde getListas()
  if (streamType === 'live') return `${base}/live/${lista.usuario_xtream}/${lista.password_xtream}/${streamId}.ts`;
  if (streamType === 'movie') return `${base}/movie/${lista.usuario_xtream}/${lista.password_xtream}/${streamId}.mp4`;
  return `${base}/series/${lista.usuario_xtream}/${lista.password_xtream}/${streamId}.ts`;
}

// ─── Estado en memoria ───────────────────────────────────────────────────────

/**
 * activeStreams: Map<channelKey, StreamEntry>
 * channelKey = `${streamId}_${streamType}`
 *
 * StreamEntry = {
 *   channelKey,
 *   streamId,
 *   streamType,
 *   listaId,        // lista que está usando este stream
 *   ffmpeg,         // proceso child_process
 *   hlsPath,        // ruta al .m3u8
 *   viewers: Set<string>,  // IPs/tokens de viewers activos
 *   idleTimer,      // setTimeout para apagado
 *   startedAt,
 *   ready: bool     // true cuando el primer segmento HLS existe
 * }
 */
const activeStreams = new Map();

/**
 * listUsage: Map<listaId, Set<channelKey>>
 * Cuántos streams activos usa cada lista
 */
const listUsage = new Map();

function getListUsageCount(listaId) {
  return (listUsage.get(listaId) || new Set()).size;
}

function registerListUsage(listaId, channelKey) {
  if (!listUsage.has(listaId)) listUsage.set(listaId, new Set());
  listUsage.get(listaId).add(channelKey);
}

function unregisterListUsage(listaId, channelKey) {
  const s = listUsage.get(listaId);
  if (s) { s.delete(channelKey); if (s.size === 0) listUsage.delete(listaId); }
}

// Elige la lista TV disponible con menos uso (< MAX_STREAMS_PER_LIST)
function pickAvailableList() {
  const listas = getListas('tv');
  listas.sort((a, b) => getListUsageCount(a.id) - getListUsageCount(b.id));
  return listas.find(l => getListUsageCount(l.id) < MAX_STREAMS_PER_LIST) || null;
}

// ─── Gestión de FFmpeg ───────────────────────────────────────────────────────

function getHlsDir(channelKey) {
  const dir = path.join(HLS_DIR, channelKey);
  if (!fs.existsSync(dir)) fs.mkdirSync(dir, { recursive: true });
  return dir;
}

// Lista de User-Agents a rotar cuando un servidor bloquea FFmpeg
const UA_LIST = [
  'VLC/3.0.20 LibVLC/3.0.20',
  'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36',
  'Kodi/20.0 (Windows; Windows 10.0) App_Bitness/64 Version/20.0',
  'TiviMate/4.7.0 (Android 11; SM-G991B)',
  'okhttp/4.9.3',
];

// Contador de intentos por channelKey para rotar UA
const _uaIndex = new Map();

function getNextUA(channelKey) {
  const idx = (_uaIndex.get(channelKey) || 0) % UA_LIST.length;
  _uaIndex.set(channelKey, idx + 1);
  return UA_LIST[idx];
}

function startFFmpeg(channelKey, sourceUrl, transcode480p) {
  const dir = getHlsDir(channelKey);
  const playlistPath = path.join(dir, 'index.m3u8');

  try {
    fs.readdirSync(dir).forEach(f => {
      if (f.endsWith('.ts') || f.endsWith('.m3u8')) fs.unlinkSync(path.join(dir, f));
    });
  } catch {}

  const userAgent = getNextUA(channelKey);
  console.log(`[RESTREAM] Iniciando FFmpeg para ${channelKey}${transcode480p?' [480p]':''}`);
  console.log(`[RESTREAM] Fuente configurada para ${channelKey} | UA: ${userAgent.slice(0, 40)}...`);

  const videoArgs = transcode480p
    ? ['-c:v','libx264','-preset','ultrafast','-tune','zerolatency',
       '-threads','2',
       '-b:v','1200k','-maxrate','1400k','-bufsize','2800k',
       '-vf','scale=854:480','-r','30',
       '-g','60','-keyint_min','30','-sc_threshold','0',
       '-c:a','aac','-b:a','128k','-ar','48000','-ac','2',
       '-af','aresample=async=1:min_hard_comp=0.100000:first_pts=0']
    : ['-c', 'copy'];

  const args = [
    '-reconnect', '1',
    '-reconnect_streamed', '1',
    '-reconnect_delay_max', '30',
    '-timeout', '60000000',
    '-user_agent', userAgent,
    '-headers', 'Accept: */*\r\nAccept-Language: en-US,en;q=0.9\r\nCache-Control: no-cache\r\n',
    '-i', sourceUrl,
    ...videoArgs,
    '-f', 'hls',
    '-hls_time', transcode480p ? '4' : String(SEGMENT_DURATION),
    '-hls_list_size', String(SEGMENT_COUNT),
    '-hls_delete_threshold', '4',
    '-hls_flags', 'delete_segments+split_by_time',
    '-hls_segment_type', 'mpegts',
    '-hls_segment_filename', path.join(dir, 'seg%05d.ts'),
    playlistPath
  ];

  const proc = spawn('/usr/bin/ffmpeg', args, { stdio: ['ignore', 'pipe', 'pipe'] });

  proc.stderr.on('data', d => {
    const line = d.toString();
    if (line.includes('Error') && !line.includes('Opening')) {
      process.stdout.write(`[FFmpeg:${channelKey}] ${line}`);
    }
  });

  proc.on('exit', (code, signal) => {
    console.log(`[RESTREAM] FFmpeg ${channelKey} terminó (code=${code}, signal=${signal})`);
    const entry = activeStreams.get(channelKey);
    if (!entry || entry.ffmpeg !== proc) return;

    // ── FAILOVER: si hay backups disponibles, intentar siguiente URL ──────────
    // Se activa cuando FFmpeg falla rápido (error de apertura) con viewers esperando
    const failover = failoverMap.get(channelKey);
    const failedFast = signal === null && code !== 0 && (Date.now() - entry.startedAt) < 15000;
    if (failedFast && failover && failover.urls.length > 0) {
      const nextIdx = (failover.currentIdx + 1) % failover.urls.length;
      // Si ya dimos toda la vuelta, volver al índice 0 (URL principal) y esperar más
      if (nextIdx === 0 && failover.triedAll) {
        console.log(`[RESTREAM] Failover agotado para ${channelKey}, esperando 30s antes de reintentar desde URL principal...`);
        failover.currentIdx = 0;
        failover.triedAll = false;
        const t = setTimeout(() => {
          _failoverTimers.delete(channelKey);
          if (!activeStreams.has(channelKey) && entry.viewers.size > 0) {
            _tryStartWithUrl(channelKey, failover.urls[0], transcode480p, entry);
          }
        }, 30000);
        _failoverTimers.set(channelKey, t);
        return;
      }
      failover.currentIdx = nextIdx;
      if (nextIdx === failover.urls.length - 1) failover.triedAll = true;
      const nextUrl = failover.urls[nextIdx];
      console.log(`[RESTREAM] ⚡ Failover ${channelKey}: cambiando a URL ${nextIdx + 1}/${failover.urls.length}: ${nextUrl.slice(0, 60)}...`);
      activeStreams.delete(channelKey);
      try { fs.readdirSync(dir).forEach(f => { try { fs.unlinkSync(path.join(dir, f)); } catch {} }); } catch {}
      const ft = setTimeout(() => {
        _failoverTimers.delete(channelKey);
        if (!activeStreams.has(channelKey) && !_startingStreams.has(channelKey)) {
          _tryStartWithUrl(channelKey, nextUrl, transcode480p, entry);
        }
      }, 2000);
      _failoverTimers.set(channelKey, ft);
      return;
    }

    if (signal === null && code === 0 && entry.viewers.size > 0) {
      const reconnectCount = (entry._reconnectCount || 0) + 1;
      if (reconnectCount > 5) {
        console.log(`[RESTREAM] Demasiadas reconexiones para ${channelKey}, deteniendo.`);
        if (entry.listaId !== 'custom') unregisterListUsage(entry.listaId, channelKey);
        activeStreams.delete(channelKey);
        _uaIndex.delete(channelKey);
        return;
      }
      console.log(`[RESTREAM] Reconectando ${channelKey} (${entry.viewers.size} viewers, intento ${reconnectCount})...`);
      activeStreams.delete(channelKey);
      if (entry.listaId !== 'custom') unregisterListUsage(entry.listaId, channelKey);
      try { fs.readdirSync(dir).forEach(f => { try { fs.unlinkSync(path.join(dir, f)); } catch {} }); } catch {}
      
      setTimeout(() => {
        if (activeStreams.has(channelKey) || _startingStreams.has(channelKey)) return;
        const { proc: newProc, playlistPath: newPl } = startFFmpeg(channelKey, sourceUrl, transcode480p);
        const newEntry = {
          ...entry,
          ffmpeg: newProc,
          hlsPath: newPl,
          hlsDir: path.dirname(newPl),
          ready: false,
          startedAt: Date.now(),
          cacheKey: `${channelKey}_${newProc.pid}_${Date.now()}`,
          _reconnectCount: reconnectCount,
        };
        activeStreams.set(channelKey, newEntry);
        if (entry.listaId !== 'custom') registerListUsage(entry.listaId, channelKey);
        waitForHls(newPl).then(() => { newEntry.ready = true; }).catch(() => {
          console.log(`[RESTREAM] Reconexión fallida para ${channelKey}`);
          stopStream(channelKey);
        });
      }, 6000);
      return;
    }

    if (entry.listaId !== 'custom') unregisterListUsage(entry.listaId, channelKey);
    activeStreams.delete(channelKey);
    _uaIndex.delete(channelKey);
    try {
      fs.readdirSync(dir).forEach(f => fs.unlinkSync(path.join(dir, f)));
      fs.rmdirSync(dir);
    } catch {}
  });

  return { proc, playlistPath };
}

// FFmpeg directo (sin pipe) para URLs con tokens o redirecciones complejas
function _startFFmpegDirect(channelKey, sourceUrl, dir, playlistPath) {
  console.log(`[RESTREAM] Reintentando con FFmpeg directo para ${channelKey}`);
  const args = [
    '-user_agent', 'VLC/3.0.20 LibVLC/3.0.20',
    '-reconnect', '1',
    '-reconnect_streamed', '1',
    '-reconnect_delay_max', '30',
    '-timeout', '60000000',
    '-re', '-i', sourceUrl,
    '-c', 'copy',
    '-f', 'hls',
    '-hls_time', String(SEGMENT_DURATION),
    '-hls_list_size', String(SEGMENT_COUNT),
    '-hls_delete_threshold', '4',
    '-hls_flags', 'delete_segments+temp_file',
    '-hls_segment_filename', path.join(dir, 'seg%05d.ts'),
    playlistPath
  ];
  const proc2 = spawn('/usr/bin/ffmpeg', args, { stdio: ['ignore', 'pipe', 'pipe'] });
  proc2.stderr.on('data', d => {
    const line = d.toString();
    if (line.includes('Error') && !line.includes('Opening')) process.stdout.write(`[FFmpeg:${channelKey}] ${line}`);
  });
  proc2.on('exit', (code, signal) => {
    console.log(`[RESTREAM] FFmpeg directo ${channelKey} terminó (code=${code}, signal=${signal})`);
    const entry = activeStreams.get(channelKey);
    if (entry) {
      if (entry.listaId !== 'custom') unregisterListUsage(entry.listaId, channelKey);
      activeStreams.delete(channelKey);
    }
    try { fs.readdirSync(dir).forEach(f => fs.unlinkSync(path.join(dir, f))); fs.rmdirSync(dir); } catch {}
  });
  // Actualizar el proceso en el entry si existe
  const entry = activeStreams.get(channelKey);
  if (entry) entry.ffmpeg = proc2;
}

// Helper: iniciar stream con una URL específica (usado en failover)
function _tryStartWithUrl(channelKey, url, transcode480p, prevEntry) {
  const { proc, playlistPath } = startFFmpeg(channelKey, url, transcode480p);
  const dir = path.dirname(playlistPath);
  const newEntry = {
    ...prevEntry,
    ffmpeg: proc,
    hlsPath: playlistPath,
    hlsDir: dir,
    ready: false,
    startedAt: Date.now(),
    cacheKey: `${channelKey}_${proc.pid}_${Date.now()}`,
    _reconnectCount: 0,
  };
  activeStreams.set(channelKey, newEntry);
  if (prevEntry.listaId !== 'custom') registerListUsage(prevEntry.listaId, channelKey);
  resetIdleTimer(newEntry);
  waitForHls(playlistPath).then(() => { newEntry.ready = true; }).catch(() => {
    console.log(`[RESTREAM] Failover: inicio lento para ${channelKey}, continuando...`);
  });
}

function stopStream(channelKey) {
  // Cancelar cualquier timer de failover pendiente
  const ft = _failoverTimers.get(channelKey);
  if (ft) { clearTimeout(ft); _failoverTimers.delete(channelKey); }
  failoverMap.delete(channelKey);
  _uaIndex.delete(channelKey);

  const entry = activeStreams.get(channelKey);
  if (!entry) return;
  if (entry._stopping) return;
  entry._stopping = true;
  console.log(`[RESTREAM] Deteniendo stream ${channelKey}`);
  clearTimeout(entry.idleTimer);
  if (entry._viewerTimers) {
    for (const t of entry._viewerTimers.values()) clearTimeout(t);
  }
  entry.ffmpeg.kill('SIGTERM');
}

function resetIdleTimer(entry) {
  clearTimeout(entry.idleTimer);
  entry.idleTimer = setTimeout(() => {
    if (!activeStreams.has(entry.channelKey)) return; // ya fue eliminado
    if (entry.viewers.size === 0) stopStream(entry.channelKey);
  }, IDLE_TIMEOUT_MS);
}

// waitForHls: espera hasta que haya al menos 3 segmentos listos para reproducción limpia
function waitForHls(playlistPath, timeout = 60000) {
  return new Promise((resolve, reject) => {
    const start = Date.now();
    const check = () => {
      if (fs.existsSync(playlistPath)) {
        try {
          const content = fs.readFileSync(playlistPath, 'utf8');
          const segs = (content.match(/seg\d+\.ts/g) || []);
          if (segs.length >= 3) return resolve();
        } catch {}
      }
      if (Date.now() - start > timeout) return reject(new Error('HLS timeout'));
      setTimeout(check, 500);
    };
    check();
  });
}
// ─── Obtener o crear stream ──────────────────────────────────────────────────

async function getOrCreateStream(streamId, streamType, channelName) {
  // streamId puede ser: número xtream, URL directa, o channelKey opaco (custom_xxxx_live)
  let channelKey;
  let resolvedUrl = null;
  let resolvedTranscode = false;

  if (streamId.startsWith('custom_') && customUrlMap.has(streamId)) {
    channelKey = streamId;
    const mapData = customUrlMap.get(streamId);
    resolvedUrl = mapData.url || mapData; // compatibilidad con formato viejo
    resolvedTranscode = !!(mapData.transcode480p);
  } else if (streamId.startsWith('custom_')) {
    // channelKey opaco pero URL no está en memoria (servidor reiniciado) — error claro
    throw new Error('Sesión de canal expirada. Volvé a seleccionar el canal.');
  } else if (streamId.startsWith('http://') || streamId.startsWith('https://')) {
    // URL directa (legacy) — generar channelKey opaco
    channelKey = 'custom_' + crypto.createHash('md5').update(streamId).digest('hex').slice(0, 12) + '_' + streamType;
    resolvedUrl = streamId;
  } else {
    channelKey = `${streamId}_${streamType}`;
  }

  if (activeStreams.has(channelKey)) {
    const entry = activeStreams.get(channelKey);
    if (channelName) entry.channelName = channelName;
    return entry;
  }

  // Si ya hay un inicio en progreso para este canal, esperar a que termine
  if (_startingStreams.has(channelKey)) {
    return _startingStreams.get(channelKey);
  }

  let sourceUrl;
  let listaId = 'custom';
  if (resolvedUrl) {
    sourceUrl = resolvedUrl;
  } else {
    const lista = pickAvailableList();
    if (!lista) throw new Error('Todas las listas están llenas (máx ' + MAX_STREAMS_PER_LIST + ' streams por lista)');
    listaId = lista.id;
    sourceUrl = buildStreamUrl(lista, streamId, streamType);
  }

  // Verificar límite de streams simultáneos
  if (activeStreams.size >= MAX_CONCURRENT_STREAMS) {
    throw new Error('Servidor lleno. Hay ' + activeStreams.size + ' canales activos (máx ' + MAX_CONCURRENT_STREAMS + '). Intenta más tarde.');
  }

  // Crear la promesa y guardarla INMEDIATAMENTE ANTES de cualquier operación async
  let resolveStartPromise, rejectStartPromise;
  const startPromise = new Promise((resolve, reject) => {
    resolveStartPromise = resolve;
    rejectStartPromise = reject;
  });

  // Guardar la promesa INMEDIATAMENTE para bloquear race conditions
  _startingStreams.set(channelKey, startPromise);

  // Ahora sí ejecutar el trabajo async
  (async () => {
    try {
      const { proc, playlistPath } = startFFmpeg(channelKey, sourceUrl, resolvedTranscode);

      const entry = {
        channelKey,
        streamId,
        channelName: channelName || streamId,
        streamType,
        listaId: listaId,
        ffmpeg: proc,
        hlsPath: playlistPath,
        hlsDir: path.dirname(playlistPath),
        viewers: new Set(),
        viewerNames: new Map(),
        idleTimer: null,
        startedAt: Date.now(),
        cacheKey: `${channelKey}_${proc.pid}_${Date.now()}`,
        ready: false
      };

      activeStreams.set(channelKey, entry);
      if (listaId !== 'custom') registerListUsage(listaId, channelKey);

      // Iniciar timer de idle desde el arranque
      resetIdleTimer(entry);

      // Esperar a que HLS esté listo
      try {
        await waitForHls(playlistPath);
        entry.ready = true;
      } catch (e) {
        // No matar el stream — FFmpeg puede seguir intentando conectar
        console.log(`[RESTREAM] ⚠️ Inicio lento para ${channelKey}, continuando...`);
        entry.ready = false;
      }

      resolveStartPromise(entry);
    } catch (error) {
      rejectStartPromise(error);
    } finally {
      // Limpiar el lock cuando termine
      _startingStreams.delete(channelKey);
    }
  })();

  return startPromise;
}

// ─── Servidor HTTP ───────────────────────────────────────────────────────────

const server = http.createServer(async (req, res) => {
  const parsed = url.parse(req.url, true);
  const pathname = parsed.pathname;

  res.setHeader('Access-Control-Allow-Origin', '*');
  res.setHeader('Access-Control-Allow-Methods', 'GET, POST, OPTIONS');
  res.setHeader('Access-Control-Allow-Headers', 'Content-Type, x-admin-token');
  if (req.method === 'OPTIONS') { res.writeHead(204); res.end(); return; }

  // POST /auth-m3u — autenticación para cuentas M3U (sin token JWT)
  // Solo acepta conexiones desde localhost (server.js)
  if (pathname === '/auth-m3u' && req.method === 'POST') {
    const clientIp = getClientIp(req);
    if (clientIp !== '127.0.0.1' && clientIp !== '::1') {
      res.writeHead(403); res.end('{}'); return;
    }
    let body = '';
    req.on('data', d => body += d);
    req.on('end', () => {
      try {
        const { canalUrl, transcode480p, cuentaId, ip } = JSON.parse(body);
        if (!canalUrl) { res.writeHead(400); res.end('{}'); return; }

        // Generar channelKey opaco para este canal
        const transcodeFlag = transcode480p ? '_480p' : '';
        const channelKey = 'custom_' + crypto.createHash('md5').update(canalUrl).digest('hex').slice(0, 12) + '_live' + transcodeFlag;
        customUrlMap.set(channelKey, { url: canalUrl, transcode480p: !!transcode480p });

        // Crear sesión especial para esta cuenta M3U
        const sessionKey = crypto.randomBytes(16).toString('hex');
        const deviceId = `m3u_${cuentaId}_${ip.replace(/\./g, '_')}`;
        streamSessions.set(sessionKey, {
          userId: `m3u_${cuentaId}`,
          deviceId,
          ip: '127.0.0.1', // validar desde localhost
          uaHash: '',
          expiresAt: Date.now() + SESSION_TTL_MS,
          isM3u: true,
        });

        const streamUrl = `http://localhost:${RESTREAM_PORT}/stream/live/${encodeURIComponent(channelKey)}/index.m3u8?sk=${sessionKey}&did=${encodeURIComponent(deviceId)}`;
        res.writeHead(200, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ streamUrl, channelKey, sessionKey }));
      } catch (e) {
        res.writeHead(400); res.end('{}');
      }
    });
    return;
  }

  // POST /auth — intercambia token JWT por sessionKey de larga duración
  if (pathname === '/auth' && req.method === 'POST') {
    let body = '';
    req.on('data', d => body += d);
    req.on('end', () => {
      try {
        const { token, deviceId, customUrl, transcode480p, backupUrls } = JSON.parse(body);
        const clientIp = getClientIp(req);
        const ua = req.headers['user-agent'] || '';

        // ── Verificar firma de la app Android ──────────────────────────────
        // Solo se exige si viene con UA de la app Android
        const isAndroidApp = /DNStreaming\/Android/i.test(ua);
        if (isAndroidApp && !verifyAppSig(req)) {
          console.log(`[RESTREAM] Firma de app inválida IP:${clientIp}`);
          res.writeHead(403, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
          res.end(JSON.stringify({ error: 'App no autorizada' }));
          return;
        }
        const check = validateToken(token, clientIp, deviceId);
        if (!check.valid) {
          res.writeHead(403, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
          res.end(JSON.stringify({ error: check.reason }));
          return;
        }
        const sessionKey = createSession(check.userId, deviceId, clientIp, req.headers['user-agent'] || '');
        let channelKey = null;
        if (customUrl && (customUrl.startsWith('http://') || customUrl.startsWith('https://'))) {
          const transcodeFlag = transcode480p ? '_480p' : '';
          channelKey = 'custom_' + crypto.createHash('md5').update(customUrl).digest('hex').slice(0, 12) + '_live' + transcodeFlag;
          customUrlMap.set(channelKey, { url: customUrl, transcode480p: !!transcode480p });
          // Registrar backups para failover
          const validBackups = Array.isArray(backupUrls) ? backupUrls.filter(u => typeof u === 'string' && u.startsWith('http')) : [];
          if (validBackups.length > 0) {
            failoverMap.set(channelKey, { urls: [customUrl, ...validBackups], currentIdx: 0, triedAll: false });
            console.log(`[RESTREAM] Failover registrado para ${channelKey}: ${validBackups.length} backup(s)`);
          }
        }
        res.writeHead(200, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
        res.end(JSON.stringify({ sessionKey, channelKey }));
      } catch (e) {
        res.writeHead(400, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
        res.end(JSON.stringify({ error: 'Datos inválidos' }));
      }
    });
    return;
  }

  // POST /heartbeat — el frontend avisa que sigue viendo
  if (pathname === '/heartbeat' && req.method === 'POST') {
    let body = '';
    req.on('data', d => body += d);
    req.on('end', () => {
      try {
        const { sk, did, channelKey } = JSON.parse(body);
        const clientIp = getClientIp(req);
        const ua = req.headers['user-agent'] || '';
        const check = validateSession(sk, clientIp, did, ua);
        if (!check.valid) { res.writeHead(403); res.end('{}'); return; }
        const entry = activeStreams.get(channelKey);
        if (entry) {
          const viewerKey = `${check.userId}:${did}`;
          if (entry.viewers.has(viewerKey) && entry._viewerTimers) {
            clearTimeout(entry._viewerTimers.get(viewerKey));
            entry._viewerTimers.set(viewerKey, setTimeout(() => {
              entry.viewers.delete(viewerKey);
              entry.viewerNames.delete(viewerKey);
              entry._viewerTimers.delete(viewerKey);
              optimizer.removeViewer(entry.channelKey, viewerKey); // OPTIMIZER
              if (entry.viewers.size === 0) resetIdleTimer(entry);
            }, 20000)); // 20s — si no llega otro heartbeat, se fue
            resetIdleTimer(entry);
          }
        }
        res.writeHead(200, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
        res.end('{"ok":true}');
      } catch (e) { res.writeHead(400); res.end('{}'); }
    });
    return;
  }

  // GET /status — estado de todos los streams activos
  if (pathname === '/status') {
    const status = [];
    for (const [key, entry] of activeStreams.entries()) {
      status.push({
        channelKey: key,
        streamId: entry.streamId,
        streamType: entry.streamType,
        listaId: entry.listaId,
        viewers: entry.viewers.size,
        uptimeSec: Math.floor((Date.now() - entry.startedAt) / 1000),
        ready: entry.ready
      });
    }
    const listStats = {};
    for (const [listaId, keys] of listUsage.entries()) {
      listStats[listaId] = keys.size;
    }
    res.writeHead(200, { 'Content-Type': 'application/json' });
    res.end(JSON.stringify({ streams: status, listUsage: listStats }));
    return;
  }

  // GET /api/optimizer-stats — Estadísticas del optimizer
  if (pathname === '/api/optimizer-stats' && req.method === 'GET') {
    try {
      const stats = optimizer.getStats();
      res.writeHead(200, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
      res.end(JSON.stringify({ success: true, stats }));
    } catch (err) {
      res.writeHead(500, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
      res.end(JSON.stringify({ success: false, error: err.message }));
    }
    return;
  }

  // GET /optimizer-stats.html — Dashboard de estadísticas
  if (pathname === '/optimizer-stats.html' && req.method === 'GET') {
    try {
      const htmlPath = path.join(__dirname, 'panel-web', 'optimizer-stats.html');
      const html = fs.readFileSync(htmlPath, 'utf8');
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' });
      res.end(html);
    } catch (err) {
      res.writeHead(404, { 'Content-Type': 'text/plain' });
      res.end('Dashboard no encontrado');
    }
    return;
  }

  // GET /admin/streams — streams activos para el panel admin (requiere x-admin-token)
  if (pathname === '/admin/streams' && req.method === 'GET') {
    const adminToken = req.headers['x-admin-token'] || '';
    if (!verifyAdminToken(adminToken)) {
      res.writeHead(401, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
      res.end(JSON.stringify({ error: 'No autorizado' }));
      return;
    }
    const streams = [];
    for (const [key, entry] of activeStreams.entries()) {
      const mapData = customUrlMap.get(key);
      streams.push({
        channelKey: key,
        streamId: entry.streamId,
        channelName: entry.channelName || entry.streamId,
        streamType: entry.streamType,
        listaId: entry.listaId,
        viewers: entry.viewers.size,
        viewerList: [...entry.viewers].map(vk => entry.viewerNames.get(vk) || vk.split(':')[0]),
        uptimeSec: Math.floor((Date.now() - entry.startedAt) / 1000),
        ready: entry.ready,
        transcode480p: !!(mapData && mapData.transcode480p) || key.endsWith('_480p')
      });
    }
    streams.sort((a, b) => b.viewers - a.viewers);
    res.writeHead(200, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
    res.end(JSON.stringify({ streams, totalViewers: streams.reduce((s, x) => s + x.viewers, 0) }));
    return;
  }

  // GET /admin/config — obtener configuración
  // POST /admin/config — actualizar configuración
  if (pathname === '/admin/config') {
    const adminToken = req.headers['x-admin-token'] || '';
    if (!verifyAdminToken(adminToken)) {
      res.writeHead(401, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
      res.end(JSON.stringify({ error: 'No autorizado' }));
      return;
    }
    if (req.method === 'GET') {
      res.writeHead(200, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
      res.end(JSON.stringify({ maxConcurrentStreams: MAX_CONCURRENT_STREAMS, activeStreams: activeStreams.size }));
      return;
    }
    if (req.method === 'POST') {
      let body = '';
      req.on('data', d => body += d);
      req.on('end', () => {
        try {
          const { maxConcurrentStreams } = JSON.parse(body);
          if (typeof maxConcurrentStreams === 'number' && maxConcurrentStreams >= 1 && maxConcurrentStreams <= 50) {
            MAX_CONCURRENT_STREAMS = maxConcurrentStreams;
          }
          res.writeHead(200, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
          res.end(JSON.stringify({ ok: true, maxConcurrentStreams: MAX_CONCURRENT_STREAMS }));
        } catch (e) {
          res.writeHead(400); res.end('{}');
        }
      });
      return;
    }
  }

  // POST /admin/stop — detener un stream (solo si viewers === 0)
  if (pathname === '/admin/stop' && req.method === 'POST') {
    const adminToken = req.headers['x-admin-token'] || '';
    if (!verifyAdminToken(adminToken)) {
      res.writeHead(401, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
      res.end(JSON.stringify({ error: 'No autorizado' }));
      return;
    }
    let body = '';
    req.on('data', d => body += d);
    req.on('end', () => {
      try {
        const { channelKey } = JSON.parse(body);
        const entry = activeStreams.get(channelKey);
        // Si no está en activeStreams pero hay un timer de failover pendiente, cancelarlo
        if (!entry) {
          const ft = _failoverTimers.get(channelKey);
          if (ft) {
            clearTimeout(ft);
            _failoverTimers.delete(channelKey);
            failoverMap.delete(channelKey);
            _uaIndex.delete(channelKey);
            res.writeHead(200, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
            res.end(JSON.stringify({ ok: true, stopped: channelKey, note: 'failover cancelado' }));
          } else {
            res.writeHead(404, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
            res.end(JSON.stringify({ error: 'Stream no encontrado' }));
          }
          return;
        }
        if (entry.viewers.size > 0) { res.writeHead(409, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' }); res.end(JSON.stringify({ error: `Hay ${entry.viewers.size} viewer(s) activos` })); return; }
        stopStream(channelKey);
        res.writeHead(200, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
        res.end(JSON.stringify({ ok: true, stopped: channelKey }));
      } catch (e) {
        res.writeHead(400, { 'Content-Type': 'application/json', 'Access-Control-Allow-Origin': '*' });
        res.end(JSON.stringify({ error: 'Datos inválidos' }));
      }
    });
    return;
  }

  // GET /stream/:streamType/:streamId/index.m3u8  — playlist HLS
  // GET /stream/:streamType/:streamId/:segment    — segmento .ts
  const streamMatch = pathname.match(/^\/stream\/(live|movie|series)\/([^/]+)\/(.+)$/);
  if (streamMatch) {
    const [, streamType, streamId, file] = streamMatch;
    const decodedStreamId = decodeURIComponent(streamId);
    const clientIp = getClientIp(req);

    // Segmentos .ts usan token de un solo uso — no necesitan sk/did
    if (file.endsWith('.ts')) {
      const segToken = parsed.query.st;
      const tokenData = consumeSegToken(segToken);
      if (!tokenData) {
        res.writeHead(403, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ error: 'Token de segmento inválido o expirado' }));
        return;
      }
      // Buscar el entry por channelKey (streamId ya es el channelKey opaco)
      const entry = activeStreams.get(decodedStreamId);
      if (!entry) { res.writeHead(404); res.end(''); return; }

      // Renovar timer del viewer — el segmento confirma que sigue viendo
      const { segFile, viewerKey } = tokenData;
      if (viewerKey && entry._viewerTimers) {
        clearTimeout(entry._viewerTimers.get(viewerKey));
        entry._viewerTimers.set(viewerKey, setTimeout(() => {
          entry.viewers.delete(viewerKey);
          entry.viewerNames.delete(viewerKey);
          entry._viewerTimers.delete(viewerKey);
          optimizer.removeViewer(entry.channelKey, viewerKey); // OPTIMIZER
          if (entry.viewers.size === 0) resetIdleTimer(entry);
        }, 20000)); // 20s — renovado por heartbeat cada 15s
        resetIdleTimer(entry);
      }
      
      const filePath = path.join(entry.hlsDir, segFile);
      if (!fs.existsSync(filePath)) { res.writeHead(404); res.end(''); return; }
      
      // ========== OPTIMIZER INTEGRATION ==========
      // Extraer número de segmento del nombre de archivo
      const segMatch = segFile.match(/seg(\d+)\.ts$/);
      const segNumber = segMatch ? parseInt(segMatch[1]) : 0;
      
      try {
        // Intentar desde caché optimizada
        let segData = await optimizer.cache.get(entry.cacheKey, segNumber);
        
        if (!segData) {
          // No está en caché, leer del disco
          segData = await fs.promises.readFile(filePath);
          
          // Guardar en caché
          await optimizer.cache.set(entry.cacheKey, segNumber, segData);
          
          // Activar pre-fetching de próximos segmentos
          optimizer.prefetcher.onSegmentRequested(decodedStreamId, segNumber, async (nextSeg) => {
            const nextPath = path.join(entry.hlsDir, `seg${nextSeg}.ts`);
            if (fs.existsSync(nextPath)) {
              return await fs.promises.readFile(nextPath);
            }
            return null;
          });
        }
        
        // Registrar estadísticas
        optimizer.recordSegment(decodedStreamId, segData.length);
        
        // Enviar segmento
        res.writeHead(200, { 
          'Content-Type': 'video/MP2T', 
          'Cache-Control': 'no-cache', 
          'Access-Control-Allow-Origin': '*',
          'Content-Length': segData.length
        });
        res.end(segData);
      } catch (err) {
        console.error('[OPTIMIZER] Error sirviendo segmento:', err.message);
        // Fallback: streaming directo si falla el optimizer
        res.writeHead(200, { 'Content-Type': 'video/MP2T', 'Cache-Control': 'no-cache', 'Access-Control-Allow-Origin': '*' });
        const fileStream = fs.createReadStream(filePath);
        fileStream.pipe(res);
        res.on('close', () => fileStream.destroy());
        fileStream.on('end', () => res.end());
        fileStream.on('error', () => res.end());
      }
      // ========== END OPTIMIZER INTEGRATION ==========
      return;
    }

    // Para el m3u8 sí se requiere sesión válida
    const sessionKey = parsed.query.sk;
    const deviceId = parsed.query.did;
    const channelName = parsed.query.name ? decodeURIComponent(parsed.query.name) : streamId;
    const ua = req.headers['user-agent'] || '';
    const check = validateSession(sessionKey, clientIp, deviceId, ua);
    if (!check.valid) {
      console.log(`[RESTREAM] Acceso denegado (${check.reason}) IP:${clientIp}`);
      res.writeHead(403, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ error: check.reason }));
      return;
    }

    // ── Bloquear reproductores externos (VLC, Kodi, etc.) ──
    const referer  = req.headers['referer']  || req.headers['referrer'] || '';
    const origin   = req.headers['origin']   || '';

    // User-agents conocidos de reproductores externos
    const blockedUA = /vlc|kodi|mpv|mpc-|lavf|ffmpeg|libmpv|gstreamer|stagefright|python|curl|wget|libcurl/i;
    const isOfficialApp = /DNStreaming\/Android/i.test(ua);

    // Si el sessionKey ya fue validado arriba (check.valid === true),
    // la sesión es legítima — fue creada por nuestra app con token firmado.
    // No bloqueamos por UA porque VLC interno de la app usa su propio UA.
    // Sin sessionKey válido, sí bloqueamos.
    if (!check.valid) {
      // Nunca debería llegar aquí (ya se validó arriba), pero por seguridad:
      res.writeHead(403, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ error: 'Sesión inválida' }));
      return;
    }
    if (!isOfficialApp && blockedUA.test(ua) && !streamSessions.has(parsed.query.sk)) {
      console.log(`[RESTREAM] Bloqueado por UA sin sesión: ${ua.substring(0,60)} IP:${clientIp}`);
      res.writeHead(403, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ error: 'Reproductor no autorizado' }));
      return;
    }

    // Debe venir con Referer o Origin del mismo servidor (panel web)
    // DESACTIVADO TEMPORALMENTE PARA PRUEBAS — PERMITIR TODOS LOS ORÍGENES
    const isLocalhost = clientIp === '127.0.0.1' || clientIp === '::1';
    const allowedHost = ALLOWED_HOST || '';
    // Exigir que el referer/origin sea una URL HTTP válida del mismo host (no solo que contenga el string)
    const validOriginPattern = allowedHost
      ? new RegExp(`^https?://${allowedHost.replace('.', '\\.')}(:\\d+)?(/|$)`)
      : null;
    
    // MODO PRUEBAS: Permitir todos los referers
    const hasValidRef = true; // Desactivado para pruebas
    /*
    const hasValidRef = isLocalhost || isOfficialApp || check.valid ||
      (validOriginPattern && (validOriginPattern.test(referer) || validOriginPattern.test(origin)));
    */
    
    if (!hasValidRef) {
      console.log(`[RESTREAM] Bloqueado sin referer válido. Ref:${referer} Origin:${origin} IP:${clientIp}`);
      res.writeHead(403, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ error: 'Acceso no autorizado' }));
      return;
    }

    try {
      const entry = await getOrCreateStream(decodedStreamId, streamType, channelName);

      const viewerKey = `${check.userId}:${deviceId}`;

      // 1 stream por dispositivo — si este deviceId ya está viendo otro canal, quitarlo
      for (const [ck, e] of activeStreams) {
        if (ck !== entry.channelKey && e.viewers.has(viewerKey)) {
          e.viewers.delete(viewerKey);
          e.viewerNames.delete(viewerKey);
          if (e._viewerTimers) { clearTimeout(e._viewerTimers.get(viewerKey)); e._viewerTimers.delete(viewerKey); }
          if (e.viewers.size === 0) resetIdleTimer(e);
        }
      }

      // Verificar límite de dispositivos simultáneos por usuario
      const maxDisp = _maxDispCache.get(String(check.userId)) || 1;
      const streamsDelUsuario = new Set();
      for (const [, e] of activeStreams) {
        for (const vk of e.viewers) {
          const [uid, did] = vk.split(':');
          if (uid === String(check.userId) && did !== deviceId) streamsDelUsuario.add(did);
        }
      }
      if (streamsDelUsuario.size >= maxDisp && !entry.viewers.has(viewerKey)) {
        res.writeHead(403, { 'Content-Type': 'application/json' });
        res.end(JSON.stringify({ error: `Límite de ${maxDisp} pantalla(s) simultánea(s) alcanzado. Cerrá otra pestaña para continuar.` }));
        return;
      }

      // Registrar/renovar viewer con timeout — se elimina si no pide nada en 30s
      if (!entry.viewerNames.has(viewerKey)) {
        entry.viewerNames.set(viewerKey, getUsernameById(check.userId));
      }
      entry.viewers.add(viewerKey);
      
      // ========== OPTIMIZER: Registrar viewer ==========
      optimizer.addViewer(entry.channelKey, viewerKey);
      // =================================================
      
      resetIdleTimer(entry);

      // Cancelar timer anterior de este viewer si existe
      if (entry._viewerTimers) {
        clearTimeout(entry._viewerTimers.get(viewerKey));
      } else {
        entry._viewerTimers = new Map();
      }
      // Si no llega heartbeat en 20s, el viewer se fue
      entry._viewerTimers.set(viewerKey, setTimeout(() => {
        entry.viewers.delete(viewerKey);
        entry.viewerNames.delete(viewerKey);
        entry._viewerTimers.delete(viewerKey);
        optimizer.removeViewer(entry.channelKey, viewerKey); // OPTIMIZER
        if (entry.viewers.size === 0) resetIdleTimer(entry);
      }, 20000));

      // Reescribir el playlist — cada segmento recibe un token de un solo uso (30s TTL)
      if (file === 'index.m3u8') {
        const playlistPath = path.join(entry.hlsDir, 'index.m3u8');
        if (!fs.existsSync(playlistPath)) { res.writeHead(404); res.end(''); return; }
        const content = fs.readFileSync(playlistPath, 'utf8');
        const rewritten = content.split('\n').map(line => {
          line = line.trim();
          if (!line || line.startsWith('#')) return line;
          // Generar token de un solo uso para este segmento
          const originalSegName = line.split('?')[0];
          const segToken = createSegToken(originalSegName, viewerKey);
          return `${originalSegName}?st=${segToken}`;
        }).join('\n');
        res.writeHead(200, {
          'Content-Type': 'application/vnd.apple.mpegurl',
          'Cache-Control': 'no-cache',
          'Access-Control-Allow-Origin': '*'
        });
        res.end(rewritten);
        return;
      }

      // Segmento .ts — ya fue manejado arriba antes de la validación de sesión

    } catch (e) {
      // No loguear errores esperados como límite de streams
      if (!e.message.includes('Servidor lleno') && !e.message.includes('Sesión de canal')) {
        console.error(`[RESTREAM] Error: ${e.message}`);
      }
      res.writeHead(503, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify({ error: e.message }));
    }
    return;
  }

  // GET /stop/:channelKey — forzar parada (admin)
  if (pathname.startsWith('/stop/')) {
    const channelKey = pathname.replace('/stop/', '');
    stopStream(channelKey);
    res.writeHead(200, { 'Content-Type': 'application/json' });
    res.end(JSON.stringify({ ok: true, stopped: channelKey }));
    return;
  }

  res.writeHead(404); res.end('Not found');
});

function getClientIp(req) {
  const raw = (req.headers['x-forwarded-for'] || req.socket.remoteAddress || 'unknown').split(',')[0].trim();
  if (raw === '::1') return '127.0.0.1';
  if (raw.startsWith('::ffff:')) return raw.slice(7);
  return raw;
}

server.listen(RESTREAM_PORT, () => {
  console.log(`[RESTREAM] Servidor corriendo en http://localhost:${RESTREAM_PORT}`);
  console.log(`[RESTREAM] HLS dir: ${HLS_DIR}`);
  console.log(`[RESTREAM] Idle timeout: ${IDLE_TIMEOUT_MS / 60000} minutos`);
  console.log(`[RESTREAM] Max streams por lista: ${MAX_STREAMS_PER_LIST}`);
});

// LIMPIADOR DESACTIVADO — FFmpeg maneja el borrado con hls_delete_threshold
// Limpiador periódico: borra .ts que ya no están en el .m3u8 activo
/*
setInterval(() => {
  for (const [channelKey] of activeStreams) {
    const dir = path.join(HLS_DIR, channelKey);
    const playlist = path.join(dir, 'index.m3u8');
    try {
      const content = fs.readFileSync(playlist, 'utf8');
      const referenced = new Set(content.match(/seg\d+\.ts/g) || []);
      fs.readdirSync(dir).forEach(f => {
        if (f.endsWith('.ts') && !referenced.has(f)) {
          try { fs.unlinkSync(path.join(dir, f)); } catch {}
        }
      });
    } catch {}
  }
}, 10000); // cada 10 segundos
*/
