/**
 * RESTREAM OPTIMIZER
 * Módulo de optimización para restream-server.js
 * 
 * Mejoras implementadas:
 * 1. Pre-fetching inteligente de segmentos
 * 2. Caché multinivel (RAM + Disco)
 * 3. Compresión automática
 * 4. Limpieza automática de memoria
 * 5. Estadísticas en tiempo real
 */

const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const { promisify } = require('util');

const gzip = promisify(zlib.gzip);
const gunzip = promisify(zlib.gunzip);

// ============================================
// CONFIGURACIÓN
// ============================================
const config = {
  // Caché RAM
  maxRamCacheSizeMB: 12,
  maxRamCacheItems: 80,
  
  // Caché Disco
  maxDiskCacheSizeMB: 500,
  diskCacheDir: path.join(__dirname, 'cache'),
  
  // Pre-fetching
  prefetchEnabled: false,
  prefetchSegments: 0, // Descargar 2 segmentos por adelantado
  
  // Compresión
  compressionEnabled: false,
  compressionLevel: 6, // 1-9 (6 = balance velocidad/ratio)
  
  // Limpieza
  cleanupIntervalMs: 30000, // 30 segundos
  segmentMaxAgeSec: 60, // Eliminar segmentos de >60seg
  
  // Estadísticas
  statsEnabled: true
};

// ============================================
// CACHÉ MULTINIVEL
// ============================================
class MultiLevelCache {
  constructor() {
    // Nivel 1: RAM (Map)
    this.ramCache = new Map();
    this.ramCacheSize = 0;
    
    // Nivel 2: Disco
    this.diskCacheEnabled = false;
    this.initDiskCache();
    
    // Estadísticas
    this.stats = {
      ramHits: 0,
      diskHits: 0,
      misses: 0,
      evictions: 0,
      compressionSaved: 0
    };
  }
  
  initDiskCache() {
    try {
      if (!fs.existsSync(config.diskCacheDir)) {
        fs.mkdirSync(config.diskCacheDir, { recursive: true });
      }
      this.diskCacheEnabled = true;
      console.log('[OPTIMIZER] Caché de disco habilitado:', config.diskCacheDir);
    } catch (err) {
      console.error('[OPTIMIZER] Error inicializando caché disco:', err.message);
      this.diskCacheEnabled = false;
    }
  }
  
  // Generar clave de caché
  getCacheKey(channelKey, segmentNumber) {
    return `${channelKey}_seg${segmentNumber}`;
  }
  
  // Obtener del caché
  async get(channelKey, segmentNumber) {
    const key = this.getCacheKey(channelKey, segmentNumber);
    
    // Nivel 1: RAM
    if (this.ramCache.has(key)) {
      const entry = this.ramCache.get(key);
      entry.lastAccess = Date.now();
      entry.hitCount++;
      this.stats.ramHits++;
      
      // Devolver datos (descomprimir si es necesario)
      if (entry.compressed) {
        return await gunzip(entry.data);
      }
      return entry.data;
    }
    
    // Nivel 2: Disco
    if (this.diskCacheEnabled) {
      const diskPath = path.join(config.diskCacheDir, `${key}.cache`);
      if (fs.existsSync(diskPath)) {
        try {
          const data = await fs.promises.readFile(diskPath);
          this.stats.diskHits++;
          
          // Promover a RAM si hay espacio
          await this.set(channelKey, segmentNumber, data, { fromDisk: true });
          
          return data;
        } catch (err) {
          console.error('[OPTIMIZER] Error leyendo caché disco:', err.message);
        }
      }
    }
    
    // Miss
    this.stats.misses++;
    return null;
  }
  
  // Guardar en caché
  async set(channelKey, segmentNumber, data, options = {}) {
    const key = this.getCacheKey(channelKey, segmentNumber);
    const dataSize = Buffer.byteLength(data);
    
    // Comprimir si está habilitado y el dato es grande
    let finalData = data;
    let compressed = false;
    
    if (config.compressionEnabled && dataSize > 10240 && !options.fromDisk) {
      try {
        finalData = await gzip(data, { level: config.compressionLevel });
        const savedBytes = dataSize - Buffer.byteLength(finalData);
        if (savedBytes > 0) {
          compressed = true;
          this.stats.compressionSaved += savedBytes;
        }
      } catch (err) {
        console.error('[OPTIMIZER] Error comprimiendo:', err.message);
        finalData = data;
      }
    }
    
    const finalSize = Buffer.byteLength(finalData);
    
    // Limites de RAM y cantidad de segmentos
    const maxSizeBytes = config.maxRamCacheSizeMB * 1024 * 1024;

    // Descontar una entrada anterior con la misma clave
    const previous = this.ramCache.get(key);
    if (previous) {
      this.ramCacheSize -= previous.size;
      this.ramCache.delete(key);
    }

    // Respetar los limites configurados
    if (finalSize <= maxSizeBytes && config.maxRamCacheItems > 0) {
      while (
        this.ramCache.size > 0 &&
        (this.ramCacheSize + finalSize > maxSizeBytes ||
         this.ramCache.size >= config.maxRamCacheItems)
      ) {
        this.evictOldest();
      }

      this.ramCache.set(key, {
        data: finalData,
        size: finalSize,
        compressed,
        timestamp: Date.now(),
        lastAccess: Date.now(),
        hitCount: 0,
        channelKey,
        segmentNumber
      });

      this.ramCacheSize += finalSize;
    }

    // Guardar en disco (async, no bloqueante)
    if (this.diskCacheEnabled && !options.fromDisk) {
      const diskPath = path.join(config.diskCacheDir, `${key}.cache`);
      fs.promises.writeFile(diskPath, data).catch(err => {
        console.error('[OPTIMIZER] Error escribiendo caché disco:', err.message);
      });
    }
  }
  
  // Eliminar entrada más vieja
  evictOldest() {
    let oldest = null;
    let oldestTime = Infinity;
    
    for (const [key, entry] of this.ramCache.entries()) {
      if (entry.lastAccess < oldestTime) {
        oldestTime = entry.lastAccess;
        oldest = key;
      }
    }
    
    if (oldest) {
      const entry = this.ramCache.get(oldest);
      this.ramCacheSize -= entry.size;
      this.ramCache.delete(oldest);
      this.stats.evictions++;
    }
  }
  
  // Limpiar segmentos viejos
  cleanup() {
    const now = Date.now();
    const maxAgeMs = config.segmentMaxAgeSec * 1000;
    let cleaned = 0;
    
    for (const [key, entry] of this.ramCache.entries()) {
      if (now - entry.timestamp > maxAgeMs) {
        this.ramCacheSize -= entry.size;
        this.ramCache.delete(key);
        cleaned++;
      }
    }
    
    if (cleaned > 0) {
      console.log(`[OPTIMIZER] Limpiados ${cleaned} segmentos viejos. RAM: ${(this.ramCacheSize / 1024 / 1024).toFixed(2)}MB`);
    }
    
    // Limpiar disco (async)
    if (this.diskCacheEnabled) {
      this.cleanupDisk();
    }
  }
  
  // Limpiar caché de disco
  async cleanupDisk() {
    try {
      const files = await fs.promises.readdir(config.diskCacheDir);
      const now = Date.now();
      const maxAgeMs = config.segmentMaxAgeSec * 2 * 1000; // 2x para disco
      
      for (const file of files) {
        if (!file.endsWith('.cache')) continue;
        
        const filePath = path.join(config.diskCacheDir, file);
        const stats = await fs.promises.stat(filePath);
        
        if (now - stats.mtimeMs > maxAgeMs) {
          await fs.promises.unlink(filePath);
        }
      }
    } catch (err) {
      console.error('[OPTIMIZER] Error limpiando disco:', err.message);
    }
  }
  
  // Obtener estadísticas
  getStats() {
    const totalRequests = this.stats.ramHits + this.stats.diskHits + this.stats.misses;
    const hitRate = totalRequests > 0 
      ? ((this.stats.ramHits + this.stats.diskHits) / totalRequests * 100).toFixed(2)
      : 0;
    
    return {
      ...this.stats,
      totalRequests,
      hitRate: `${hitRate}%`,
      ramCacheSize: `${(this.ramCacheSize / 1024 / 1024).toFixed(2)} MB`,
      ramCacheItems: this.ramCache.size,
      compressionSavedMB: `${(this.stats.compressionSaved / 1024 / 1024).toFixed(2)} MB`
    };
  }
  
  // Limpiar todo
  clear() {
    this.ramCache.clear();
    this.ramCacheSize = 0;
    
    if (this.diskCacheEnabled) {
      fs.promises.readdir(config.diskCacheDir)
        .then(files => {
          files.forEach(file => {
            if (file.endsWith('.cache')) {
              fs.promises.unlink(path.join(config.diskCacheDir, file)).catch(() => {});
            }
          });
        })
        .catch(() => {});
    }
  }
}

// ============================================
// PRE-FETCHING INTELIGENTE
// ============================================
class SegmentPrefetcher {
  constructor(cache) {
    this.cache = cache;
    this.prefetchQueue = new Map(); // channelKey → { nextSegment, fetching }
  }
  
  // Registrar que se solicitó un segmento
  onSegmentRequested(channelKey, segmentNumber, fetchFunction) {
    if (!config.prefetchEnabled) return;
    
    // Pre-fetch de los próximos N segmentos
    for (let i = 1; i <= config.prefetchSegments; i++) {
      const nextSeg = segmentNumber + i;
      const key = this.cache.getCacheKey(channelKey, nextSeg);
      
      // Si ya está en caché o se está descargando, skip
      if (this.cache.ramCache.has(key)) continue;
      if (this.prefetchQueue.has(key)) continue;
      
      // Marcar como "fetching" y descargar
      this.prefetchQueue.set(key, true);
      
      fetchFunction(nextSeg)
        .then(data => {
          if (data) {
            this.cache.set(channelKey, nextSeg, data);
          }
          this.prefetchQueue.delete(key);
        })
        .catch(err => {
          console.error(`[PREFETCH] Error pre-fetching seg${nextSeg}:`, err.message);
          this.prefetchQueue.delete(key);
        });
    }
  }
}

// ============================================
// MONITOR DE ESTADÍSTICAS
// ============================================
class StatsMonitor {
  constructor(cache) {
    this.cache = cache;
    this.startTime = Date.now();
    this.channelStats = new Map(); // channelKey → { viewers, segments, bandwidth }
  }
  
  // Registrar viewer
  addViewer(channelKey, viewerKey) {
    if (!this.channelStats.has(channelKey)) {
      this.channelStats.set(channelKey, {
        viewers: new Set(),
        segmentsServed: 0,
        bytesServed: 0
      });
    }
    const stats = this.channelStats.get(channelKey);
    stats.viewers.add(viewerKey);
  }
  
  // Remover viewer
  removeViewer(channelKey, viewerKey) {
    const stats = this.channelStats.get(channelKey);
    if (stats) {
      stats.viewers.delete(viewerKey);
      if (stats.viewers.size === 0) {
        this.channelStats.delete(channelKey);
      }
    }
  }
  
  // Registrar segmento servido
  recordSegment(channelKey, bytes) {
    const stats = this.channelStats.get(channelKey);
    if (stats) {
      stats.segmentsServed++;
      stats.bytesServed += bytes;
    }
  }
  
  // Obtener estadísticas
  getStats() {
    const cacheStats = this.cache.getStats();
    const uptime = Math.floor((Date.now() - this.startTime) / 1000);
    
    const channels = [];
    for (const [key, stats] of this.channelStats.entries()) {
      channels.push({
        channel: key.substring(0, 20) + '...',
        viewers: stats.viewers.size,
        segments: stats.segmentsServed,
        bandwidth: `${(stats.bytesServed / 1024 / 1024).toFixed(2)} MB`
      });
    }
    
    return {
      uptime: `${Math.floor(uptime / 3600)}h ${Math.floor((uptime % 3600) / 60)}m`,
      cache: cacheStats,
      activeChannels: channels.length,
      totalViewers: Array.from(this.channelStats.values())
        .reduce((sum, s) => sum + s.viewers.size, 0),
      channels: channels.slice(0, 10) // Top 10
    };
  }
}

// ============================================
// INICIALIZACIÓN
// ============================================
const cache = new MultiLevelCache();
const prefetcher = new SegmentPrefetcher(cache);
const monitor = new StatsMonitor(cache);

// Limpieza automática cada 30 segundos
setInterval(() => {
  cache.cleanup();
}, config.cleanupIntervalMs);

// ============================================
// EXPORTS
// ============================================
module.exports = {
  cache,
  prefetcher,
  monitor,
  config,
  
  // Helper: obtener segmento optimizado
  async getSegment(channelKey, segmentNumber, fetchFunction) {
    // Intentar desde caché
    const cached = await cache.get(channelKey, segmentNumber);
    if (cached) {
      return cached;
    }
    
    // Descargar
    const data = await fetchFunction(segmentNumber);
    if (data) {
      // Guardar en caché
      await cache.set(channelKey, segmentNumber, data);
      
      // Activar pre-fetching
      prefetcher.onSegmentRequested(channelKey, segmentNumber, fetchFunction);
    }
    
    return data;
  },
  
  // Helper: registrar viewer
  addViewer(channelKey, viewerKey) {
    monitor.addViewer(channelKey, viewerKey);
  },
  
  // Helper: remover viewer
  removeViewer(channelKey, viewerKey) {
    monitor.removeViewer(channelKey, viewerKey);
  },
  
  // Helper: registrar segmento servido
  recordSegment(channelKey, bytes) {
    monitor.recordSegment(channelKey, bytes);
  },
  
  // Obtener estadísticas
  getStats() {
    return monitor.getStats();
  },
  
  // Limpiar todo
  clear() {
    cache.clear();
  }
};

// ============================================
// LOGGING
// ============================================
console.log('╔════════════════════════════════════════╗');
console.log('║   🚀 RESTREAM OPTIMIZER LOADED        ║');
console.log('╚════════════════════════════════════════╝');
console.log(`\n📊 Configuración:`);
console.log(`  - Caché RAM: ${config.maxRamCacheSizeMB}MB`);
console.log(`  - Caché Disco: ${config.maxDiskCacheSizeMB}MB`);
console.log(`  - Pre-fetching: ${config.prefetchEnabled ? 'Habilitado (' + config.prefetchSegments + ' segmentos)' : 'Deshabilitado'}`);
console.log(`  - Compresión: ${config.compressionEnabled ? 'Habilitado (nivel ' + config.compressionLevel + ')' : 'Deshabilitado'}`);
console.log(`  - Limpieza automática: cada ${config.cleanupIntervalMs / 1000}seg\n`);
