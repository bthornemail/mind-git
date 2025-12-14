import { CompilationResult } from '../state/StateManager';

/**
 * In-memory caching system for compilation results
 * Provides intelligent cache invalidation and performance optimization
 */

export interface CacheEntry {
  result: CompilationResult;
  fileHash: string;
  timestamp: number;
  accessCount: number;
  lastAccessed: number;
}

export interface CacheStats {
  entries: number;
  hitRate: number;
  totalHits: number;
  totalMisses: number;
  oldestEntry: number;
  newestEntry: number;
}

export class CompilationCache {
  private cache = new Map<string, CacheEntry>();
  private maxEntries = 100;
  private maxAge = 30 * 60 * 1000; // 30 minutes
  private stats = {
    hits: 0,
    misses: 0
  };
  
  /**
   * Generate hash for file content
   */
  private generateHash(content: string): string {
    // Simple hash function - could be replaced with crypto hash
    let hash = 0;
    for (let i = 0; i < content.length; i++) {
      const char = content.charCodeAt(i);
      hash = ((hash << 5) - hash) + char;
      hash = hash & hash; // Convert to 32-bit integer
    }
    return hash.toString(36);
  }
  
  /**
   * Store compilation result in cache
   */
  set(filePath: string, fileContent: string, result: CompilationResult): void {
    const fileHash = this.generateHash(fileContent);
    const now = Date.now();
    
    const entry: CacheEntry = {
      result,
      fileHash,
      timestamp: now,
      accessCount: 0,
      lastAccessed: now
    };
    
    this.cache.set(filePath, entry);
    
    // Clean up old entries if cache is full
    this.cleanup();
  }
  
  /**
   * Get compilation result from cache
   */
  get(filePath: string, fileContent: string): CompilationResult | null {
    const entry = this.cache.get(filePath);
    
    if (!entry) {
      this.stats.misses++;
      return null;
    }
    
    // Check if file content has changed
    const currentHash = this.generateHash(fileContent);
    if (entry.fileHash !== currentHash) {
      this.cache.delete(filePath);
      this.stats.misses++;
      return null;
    }
    
    // Check if entry is too old
    const now = Date.now();
    if (now - entry.timestamp > this.maxAge) {
      this.cache.delete(filePath);
      this.stats.misses++;
      return null;
    }
    
    // Update access statistics
    entry.accessCount++;
    entry.lastAccessed = now;
    this.stats.hits++;
    
    return entry.result;
  }
  
  /**
   * Check if file has cached result
   */
  has(filePath: string, fileContent: string): boolean {
    return this.get(filePath, fileContent) !== null;
  }
  
  /**
   * Remove entry from cache
   */
  delete(filePath: string): boolean {
    return this.cache.delete(filePath);
  }
  
  /**
   * Clear all cache entries
   */
  clear(): void {
    this.cache.clear();
    this.stats.hits = 0;
    this.stats.misses = 0;
  }
  
  /**
   * Clean up old and least-used entries
   */
  private cleanup(): void {
    if (this.cache.size <= this.maxEntries) {
      return;
    }
    
    // Sort entries by (lastAccessed, accessCount) for LRU with frequency consideration
    const entries = Array.from(this.cache.entries())
      .sort(([, a], [, b]) => {
        // First by last accessed time
        if (a.lastAccessed !== b.lastAccessed) {
          return a.lastAccessed - b.lastAccessed;
        }
        // Then by access count (keep frequently accessed items)
        return a.accessCount - b.accessCount;
      });
    
    // Remove oldest entries
    const toRemove = entries.slice(0, entries.length - this.maxEntries);
    toRemove.forEach(([filePath]) => this.cache.delete(filePath));
  }
  
  /**
   * Get cache statistics
   */
  getStats(): CacheStats {
    const now = Date.now();
    const entries = Array.from(this.cache.values());
    
    const oldestEntry = entries.length > 0 
      ? Math.min(...entries.map(e => e.timestamp))
      : 0;
    
    const newestEntry = entries.length > 0
      ? Math.max(...entries.map(e => e.timestamp))
      : 0;
    
    const totalRequests = this.stats.hits + this.stats.misses;
    const hitRate = totalRequests > 0 ? this.stats.hits / totalRequests : 0;
    
    return {
      entries: this.cache.size,
      hitRate,
      totalHits: this.stats.hits,
      totalMisses: this.stats.misses,
      oldestEntry,
      newestEntry
    };
  }
  
  /**
   * Get entries sorted by access frequency
   */
  getTopEntries(limit = 10): Array<{ filePath: string; entry: CacheEntry }> {
    return Array.from(this.cache.entries())
      .sort(([, a], [, b]) => b.accessCount - a.accessCount)
      .slice(0, limit)
      .map(([filePath, entry]) => ({ filePath, entry }));
  }
  
  /**
   * Get entries that haven't been accessed recently
   */
  getStaleEntries(maxAge = this.maxAge): Array<{ filePath: string; entry: CacheEntry }> {
    const now = Date.now();
    return Array.from(this.cache.entries())
      .filter(([, entry]) => now - entry.lastAccessed > maxAge)
      .map(([filePath, entry]) => ({ filePath, entry }));
  }
  
  /**
   * Force cleanup of old entries
   */
  forceCleanup(): number {
    const beforeSize = this.cache.size;
    
    // Remove expired entries
    const now = Date.now();
    for (const [filePath, entry] of this.cache.entries()) {
      if (now - entry.timestamp > this.maxAge) {
        this.cache.delete(filePath);
      }
    }
    
    // Remove excess entries
    this.cleanup();
    
    return beforeSize - this.cache.size;
  }
  
  /**
   * Set cache configuration
   */
  setConfig(maxEntries?: number, maxAge?: number): void {
    if (maxEntries !== undefined) {
      this.maxEntries = maxEntries;
    }
    if (maxAge !== undefined) {
      this.maxAge = maxAge;
    }
    
    // Trigger cleanup if limits changed
    this.cleanup();
  }
  
  /**
   * Export cache data (for debugging)
   */
  export(): Array<{ filePath: string; entry: CacheEntry }> {
    return Array.from(this.cache.entries()).map(([filePath, entry]) => ({
      filePath,
      entry: { ...entry }
    }));
  }
  
  /**
   * Get memory usage estimate
   */
  getMemoryUsage(): { entries: number; estimatedBytes: number } {
    let totalSize = 0;
    
    for (const [filePath, entry] of this.cache.entries()) {
      // Rough estimation of memory usage
      totalSize += filePath.length * 2; // String characters
      totalSize += entry.fileHash.length * 2;
      totalSize += JSON.stringify(entry.result).length * 2;
      totalSize += 64; // Overhead for object properties
    }
    
    return {
      entries: this.cache.size,
      estimatedBytes: totalSize
    };
  }
}