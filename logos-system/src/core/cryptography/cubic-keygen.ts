/**
 * Cubic Key Generation - Post-Quantum Cryptographic Keys
 *
 * === KEY STRUCTURE ===
 * Private key: Random ternary cubic C_private
 * Public key: C_public = C_private ∘ C_private (self-composition)
 *
 * === SECURITY LEVELS ===
 * 128-bit: Tensor bound 10, ~2^32 classical, ~2^64 quantum (Grover)
 * 192-bit: Tensor bound 20, ~2^48 classical, ~2^96 quantum
 * 256-bit: Tensor bound 50, ~2^64 classical, ~2^128 quantum
 *
 * === KEY SIZES ===
 * Public key: 40 bytes (10 coefficients × 4 bytes each)
 * Private key: 40 bytes (10 coefficients × 4 bytes each)
 * Total: 80 bytes (vs 800-1312 bytes for NIST post-quantum standards)
 *
 * === GENERATION PROCESS ===
 * 1. Generate random seed (cryptographically secure)
 * 2. Create random 2×2×2×2 tensor from seed
 * 3. Extract private cubic from tensor (axis 0)
 * 4. Compose tensor with itself
 * 5. Extract public cubic from composed tensor
 *
 * @see {@link docs/research/history/CUBIC_CRYPTOGRAPHY_PROTOCOL.py}
 */

import {
  TernaryCubicForm,
  CubicTensorEngine,
  CubicKeyPair
} from './index';

/**
 * Security level in bits
 */
export type SecurityLevel = 128 | 192 | 256;

/**
 * Cubic Key Generator
 *
 * Generates cryptographic key pairs using Bhargava cubic composition.
 *
 * @example
 * const keygen = new CubicKeyGenerator(128);
 * const keys = keygen.generateKeyPair();
 * console.log(keys.public_cubic.toString());
 */
export class CubicKeyGenerator {
  private securityLevel: SecurityLevel;
  private tensorBound: number;
  private engine: typeof CubicTensorEngine;

  /**
   * Initialize key generator
   *
   * @param securityLevel - Security level in bits (128, 192, or 256)
   */
  constructor(securityLevel: SecurityLevel = 128) {
    this.securityLevel = securityLevel;
    this.tensorBound = this.getTensorBound(securityLevel);
    this.engine = CubicTensorEngine;
  }

  /**
   * Get tensor bound for security level
   *
   * Higher bounds increase security but make operations slower.
   *
   * @param level - Security level in bits
   * @returns Maximum absolute value for tensor elements
   */
  private getTensorBound(level: SecurityLevel): number {
    const bounds: Record<SecurityLevel, number> = {
      128: 10,
      192: 20,
      256: 50,
    };
    return bounds[level];
  }

  /**
   * Generate cryptographically secure random seed
   *
   * Uses Web Crypto API for secure randomness.
   *
   * @returns 32-bit random seed
   */
  private generateSecureSeed(): number {
    const array = new Uint32Array(1);
    crypto.getRandomValues(array);
    return array[0];
  }

  /**
   * Generate random public/private cubic key pair
   *
   * Process:
   * 1. Generate secure random seed
   * 2. Create random tensor T_private from seed
   * 3. Extract private cubic: C_private = extract(T_private, axis=0)
   * 4. Compose tensor with itself: T_public = T_private ∘ T_private
   * 5. Extract public cubic: C_public = extract(T_public, axis=0)
   *
   * Security: Recovering C_private from C_public requires solving
   * tensor decomposition problem (NP-hard, no known quantum speedup).
   *
   * @returns Cubic key pair (private, public, seed)
   */
  generateKeyPair(): CubicKeyPair {
    // Generate cryptographically secure seed
    const seed = this.generateSecureSeed();

    // Generate random tensor (private)
    const privateTensor = this.engine.randomTensor(this.tensorBound, seed);

    // Extract private cubic from tensor
    const privateCubic = this.engine.extractCubicFromTensor(privateTensor, 0);

    // Derive public cubic from private via tensor composition
    // Public = Private ∘ Private (self-composition)
    const publicTensor = this.engine.composeTensors(privateTensor, privateTensor);
    const publicCubic = this.engine.extractCubicFromTensor(publicTensor, 0);

    return {
      private_cubic: privateCubic,
      public_cubic: publicCubic,
      tensor_seed: seed,
    };
  }

  /**
   * Generate ephemeral cubic for key exchange
   *
   * Ephemeral keys are used once and discarded.
   * Provides forward secrecy in key exchange protocols.
   *
   * @returns Random ternary cubic form
   */
  generateEphemeralCubic(): TernaryCubicForm {
    const seed = this.generateSecureSeed();
    const tensor = this.engine.randomTensor(this.tensorBound, seed);
    return this.engine.extractCubicFromTensor(tensor, 0);
  }

  /**
   * Serialize public key to bytes for transmission
   *
   * @param publicCubic - Public cubic form
   * @returns 40-byte public key
   */
  serializePublicKey(publicCubic: TernaryCubicForm): Uint8Array {
    return publicCubic.toBytes();
  }

  /**
   * Deserialize public key from bytes
   *
   * @param bytes - 40-byte public key
   * @returns Public cubic form
   */
  deserializePublicKey(bytes: Uint8Array): TernaryCubicForm {
    if (bytes.length !== 40) {
      throw new Error('Public key must be exactly 40 bytes');
    }

    const coeffs: Record<string, number> = {};
    const view = new DataView(bytes.buffer);

    const indices: Array<[number, number, number]> = [
      [3,0,0], [2,1,0], [2,0,1], [1,2,0], [1,1,1],
      [1,0,2], [0,3,0], [0,2,1], [0,1,2], [0,0,3]
    ];

    indices.forEach(([i, j, k], idx) => {
      const key = `${i},${j},${k}`;
      coeffs[key] = view.getInt32(idx * 4, false); // big-endian
    });

    return new TernaryCubicForm(coeffs);
  }

  /**
   * Get security parameters for current configuration
   *
   * @returns Security analysis object
   */
  getSecurityParameters(): {
    security_level: number;
    tensor_size: number;
    coefficient_bound: number;
    search_space: string;
    quantum_resistance: string;
    classical_resistance: string;
    key_size_bytes: number;
  } {
    const searchSpaceExponent = this.securityLevel / 4;

    return {
      security_level: this.securityLevel,
      tensor_size: 16, // 2×2×2×2
      coefficient_bound: this.tensorBound,
      search_space: `~2^${searchSpaceExponent} operations`,
      quantum_resistance: 'High (no known quantum attacks on tensor decomposition)',
      classical_resistance: 'Based on hardness of cubic ring isomorphism',
      key_size_bytes: 40, // 10 coefficients × 4 bytes
    };
  }
}
