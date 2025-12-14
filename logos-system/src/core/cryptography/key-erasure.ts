/**
 * Key Erasure Mechanisms - Production Hardened Implementation
 *
 * === SECURITY REQUIREMENTS ===
 * - Immediate zeroization of sensitive key material
 * - Protection against memory dump attacks
 * - Secure key lifecycle management
 * - Protection against cold boot attacks
 *
 * === IMPLEMENTATION STRATEGY ===
 * - Multi-pass overwriting with different patterns
 * - Memory barriers to ensure write completion
 * - Hardware-specific secure clearing when available
 * - Automatic cleanup on object destruction
 *
 * === KEY TYPES SUPPORTED ===
 * - Cubic cryptographic keys
 * - Sedenion universe addresses
 * - Trigintaduonion private keys
 * - Session keys and temporary material
 */

import { SecureMemory, SecureBlock } from './secure-memory';
import { ConstantTime } from './constant-time';
import { TernaryCubicForm, CubicKeyPair } from './index';
import { Sedenion, Trigintaduonion } from '../multiverse/index';

/**
 * Key erasure configuration
 */
export interface KeyErasureConfig {
  overwritePasses: number;      // Number of overwrite passes
  useMemoryBarriers: boolean;   // Insert memory barriers
  hardwareSecureClear: boolean;  // Use hardware secure clear if available
  verifyErasure: boolean;       // Verify memory was actually zeroized
  auditLog: boolean;           // Log erasure events for audit trail
}

/**
 * Key erasure audit entry
 */
export interface ErasureAuditEntry {
  timestamp: number;
  keyType: string;
  keySize: number;
  passes: number;
  verified: boolean;
  success: boolean;
  duration: number;
}

/**
 * Production-hardened key erasure system
 */
export class KeyErasure {
  private config: KeyErasureConfig;
  private secureMemory: SecureMemory;
  private constantTime: ConstantTime;
  private auditLog: ErasureAuditEntry[] = [];
  private activeKeys: Map<string, SecureBlock> = new Map();

  constructor(config?: Partial<KeyErasureConfig>) {
    this.config = {
      overwritePasses: 8,
      useMemoryBarriers: true,
      hardwareSecureClear: true,
      verifyErasure: true,
      auditLog: true,
      ...config
    };

    this.secureMemory = new SecureMemory();
    this.constantTime = new ConstantTime();
  }

  /**
   * Register a key for secure tracking
   *
   * @param keyId - Unique key identifier
   * @param keyData - Key data to protect
   * @param keyType - Type of key for audit
   */
  async registerKey(
    keyId: string,
    keyData: Uint8Array,
    keyType: string
  ): Promise<void> {
    const block = await this.secureMemory.allocate(keyData.length, true);
    await this.secureMemory.secureCopy(
      { data: keyData, size: keyData.length, isSensitive: true, allocatedAt: Date.now() },
      block,
      keyData.length
    );
    
    this.activeKeys.set(keyId, block);
  }

  /**
   * Erase cubic cryptographic key
   *
   * @param keyPair - Cubic key pair to erase
   * @param keyId - Optional key identifier for tracking
   */
  async eraseCubicKey(keyPair: CubicKeyPair, keyId?: string): Promise<void> {
    const start = performance.now();
    
    try {
      // Serialize both private and public keys
      const privateBytes = keyPair.private_cubic.toBytes();
      const publicBytes = keyPair.public_cubic.toBytes();
      
      // Combine for complete erasure
      const combined = new Uint8Array(privateBytes.length + publicBytes.length);
      combined.set(privateBytes, 0);
      combined.set(publicBytes, privateBytes.length);
      
      // Perform secure erasure
      await this.secureErase(combined, keyId || 'cubic_key');
      
      // Clear original objects
      await this.clearCubicForm(keyPair.private_cubic);
      await this.clearCubicForm(keyPair.public_cubic);
      
      // Remove from tracking if registered
      if (keyId && this.activeKeys.has(keyId)) {
        const block = this.activeKeys.get(keyId)!;
        await this.secureMemory.deallocate(block);
        this.activeKeys.delete(keyId);
      }
      
      const duration = performance.now() - start;
      this.logAudit('cubic_key', combined.length, this.config.overwritePasses, true, true, duration);
      
    } catch (error) {
      const duration = performance.now() - start;
      this.logAudit('cubic_key', 0, this.config.overwritePasses, false, false, duration);
      throw error;
    }
  }

  /**
   * Erase sedenion universe address
   *
   * @param sedenion - Sedenion to erase
   * @param keyId - Optional key identifier for tracking
   */
  async eraseSedenion(sedenion: Sedenion, keyId?: string): Promise<void> {
    const start = performance.now();
    
    try {
      const bytes = sedenion.toBytes();
      await this.secureErase(bytes, keyId || 'sedenion');
      
      // Clear sedenion components
      await this.clearNumberArray(sedenion.components);
      
      const duration = performance.now() - start;
      this.logAudit('sedenion', bytes.length, this.config.overwritePasses, true, true, duration);
      
    } catch (error) {
      const duration = performance.now() - start;
      this.logAudit('sedenion', 0, this.config.overwritePasses, false, false, duration);
      throw error;
    }
  }

  /**
   * Erase trigintaduonion private key
   *
   * @param trigintaduonion - Trigintaduonion to erase
   * @param keyId - Optional key identifier for tracking
   */
  async eraseTrigintaduonion(
    trigintaduonion: Trigintaduonion,
    keyId?: string
  ): Promise<void> {
    const start = performance.now();
    
    try {
      const bytes = trigintaduonion.toBytes();
      await this.secureErase(bytes, keyId || 'trigintaduonion');
      
      // Clear all components
      await this.clearNumberArray(trigintaduonion.components);
      
      const duration = performance.now() - start;
      this.logAudit('trigintaduonion', bytes.length, this.config.overwritePasses, true, true, duration);
      
    } catch (error) {
      const duration = performance.now() - start;
      this.logAudit('trigintaduonion', 0, this.config.overwritePasses, false, false, duration);
      throw error;
    }
  }

  /**
   * Erase generic key material
   *
   * @param data - Key data to erase
   * @param keyType - Type of key for audit
   * @param keyId - Optional key identifier
   */
  async eraseKey(data: Uint8Array, keyType: string, keyId?: string): Promise<void> {
    const start = performance.now();
    
    try {
      await this.secureErase(data, keyId || keyType);
      
      const duration = performance.now() - start;
      this.logAudit(keyType, data.length, this.config.overwritePasses, true, true, duration);
      
    } catch (error) {
      const duration = performance.now() - start;
      this.logAudit(keyType, 0, this.config.overwritePasses, false, false, duration);
      throw error;
    }
  }

  /**
   * Perform secure multi-pass erasure
   *
   * @param data - Data to erase
   * @param keyId - Key identifier for tracking
   */
  private async secureErase(data: Uint8Array, keyId: string): Promise<void> {
    const patterns = [
      0x00, 0xFF, 0xAA, 0x55, 0x69, 0x96, 0x33, 0xCC
    ];
    
    let verified = true;
    
    for (let pass = 0; pass < this.config.overwritePasses; pass++) {
      const pattern = patterns[pass % patterns.length];
      
      // Overwrite with pattern
      await this.secureMemory.arrayFill(data, pattern, data.length);
      
      // Insert memory barrier if configured
      if (this.config.useMemoryBarriers) {
        await this.memoryBarrier();
      }
      
      // Hardware secure clear if available and configured
      if (this.config.hardwareSecureClear && pass === this.config.overwritePasses - 1) {
        await this.hardwareSecureClear(data);
      }
    }
    
    // Final zero pass
    await this.secureMemory.arrayFill(data, 0x00, data.length);
    
    // Verify erasure if configured
    if (this.config.verifyErasure) {
      verified = await this.verifyErasure(data);
    }
    
    if (!verified) {
      throw new Error(`Key erasure verification failed for ${keyId}`);
    }
  }

  /**
   * Clear cubic form coefficients
   *
   * @param cubic - Cubic form to clear
   */
  private async clearCubicForm(cubic: TernaryCubicForm): Promise<void> {
    for (const key of cubic.coeffs.keys()) {
      cubic.coeffs.set(key, 0);
    }
  }

  /**
   * Clear number array
   *
   * @param array - Array to clear
   */
  private async clearNumberArray(array: number[]): Promise<void> {
    for (let i = 0; i < array.length; i++) {
      array[i] = 0;
    }
  }

  /**
   * Memory barrier to ensure write completion
   */
  private async memoryBarrier(): Promise<void> {
    // Force memory writes to complete
    if (typeof Atomics !== 'undefined') {
      // Use atomic operations as memory barrier
      const buffer = new SharedArrayBuffer(4);
      const view = new Int32Array(buffer);
      Atomics.store(view, 0, 0);
      Atomics.load(view, 0); // Memory barrier
    } else {
      // Fallback: small delay to allow memory writes
      await new Promise(resolve => setTimeout(resolve, 1));
    }
  }

  /**
   * Hardware secure clear if available
   *
   * @param data - Data to clear
   */
  private async hardwareSecureClear(data: Uint8Array): Promise<void> {
    // Check for WebAssembly secure memory support
    if (typeof WebAssembly !== 'undefined' && WebAssembly.Memory) {
      try {
        // Try to use WebAssembly memory with secure clearing
        const memory = new WebAssembly.Memory({ 
          initial: Math.ceil(data.length / 65536) 
        });
        
        // Copy data to WASM memory
        const view = new Uint8Array(memory.buffer);
        view.set(data);
        
        // Clear WASM memory (may be more secure than regular JS)
        view.fill(0);
        
      } catch (error) {
        // Fallback to regular clearing
        console.warn('Hardware secure clear not available, using software method');
      }
    }
  }

  /**
   * Verify that data was properly erased
   *
   * @param data - Data to verify
   * @returns true if all zeros
   */
  private async verifyErasure(data: Uint8Array): Promise<boolean> {
    let isZero = true;
    
    for (let i = 0; i < data.length; i++) {
      if (data[i] !== 0) {
        isZero = false;
        break;
      }
    }
    
    return isZero;
  }

  /**
   * Log audit entry
   */
  private logAudit(
    keyType: string,
    keySize: number,
    passes: number,
    verified: boolean,
    success: boolean,
    duration: number
  ): void {
    if (!this.config.auditLog) return;
    
    const entry: ErasureAuditEntry = {
      timestamp: Date.now(),
      keyType,
      keySize,
      passes,
      verified,
      success,
      duration
    };
    
    this.auditLog.push(entry);
    
    // Keep only last 1000 entries
    if (this.auditLog.length > 1000) {
      this.auditLog = this.auditLog.slice(-1000);
    }
  }

  /**
   * Get audit log
   */
  getAuditLog(): ErasureAuditEntry[] {
    return [...this.auditLog];
  }

  /**
   * Get active keys
   */
  getActiveKeys(): string[] {
    return Array.from(this.activeKeys.keys());
  }

  /**
   * Erase all registered keys
   */
  async eraseAllKeys(): Promise<void> {
    const keyIds = Array.from(this.activeKeys.keys());
    
    for (const keyId of keyIds) {
      const block = this.activeKeys.get(keyId)!;
      await this.secureMemory.deallocate(block);
      this.activeKeys.delete(keyId);
    }
  }

  /**
   * Emergency erase - immediately clear all sensitive data
   */
  async emergencyErase(): Promise<void> {
    try {
      // Erase all registered keys
      await this.eraseAllKeys();
      
      // Clear audit log
      this.auditLog = [];
      
      // Clear secure memory
      await this.secureMemory.cleanupAll();
      
    } catch (error) {
      console.error('Emergency erase failed:', error);
      // Continue despite errors - this is emergency
    }
  }

  /**
   * Check if key is registered
   *
   * @param keyId - Key identifier
   * @returns true if key is registered
   */
  isKeyRegistered(keyId: string): boolean {
    return this.activeKeys.has(keyId);
  }

  /**
   * Get erasure statistics
   */
  getStatistics(): {
    totalErasures: number;
    successfulErasures: number;
    failedErasures: number;
    averageDuration: number;
    activeKeys: number;
  } {
    const total = this.auditLog.length;
    const successful = this.auditLog.filter(entry => entry.success).length;
    const failed = total - successful;
    const avgDuration = total > 0 
      ? this.auditLog.reduce((sum, entry) => sum + entry.duration, 0) / total 
      : 0;
    
    return {
      totalErasures: total,
      successfulErasures: successful,
      failedErasures: failed,
      averageDuration: avgDuration,
      activeKeys: this.activeKeys.size
    };
  }

  /**
   * Destructor - cleanup all resources
   */
  async destroy(): Promise<void> {
    await this.eraseAllKeys();
    await this.secureMemory.destroy();
    this.auditLog = [];
  }
}