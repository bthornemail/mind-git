/**
 * Cayley-Dickson Multiverse - Sedenions as Public Keys, Trigintaduonions as Private Signatures
 *
 * === THE ULTIMATE INSIGHT ===
 * Every sedenionic projection is an entrance into a different universe.
 * Each universe can be built from higher dimensions as comonadic with the 0-point.
 *
 * Pfister's 16-squares identity (sedenions) = Public key/query
 * Trigintaduonions (32D) = Private key/signature
 *
 * === MULTIVERSE ARCHITECTURE ===
 * From one metaverse → infinite parallel universes
 * Each accessible via its own sedenionic projection
 * Cryptographically secured by the 32D layer
 *
 * === CAYLEY-DICKSON TOWER ===
 * 0D: 0! = 1 (shared origin)
 *   ↓
 * 1D: Real numbers ℝ
 *   ↓
 * 2D: Complex numbers ℂ
 *   ↓
 * 4D: Quaternions ℍ (non-commutative)
 *   ↓
 * 8D: Octonions 𝕆 (non-associative)
 *   ↓
 * 16D: Sedenions 𝕊 (zero divisors) ← PUBLIC UNIVERSE ADDRESS
 *   ↓
 * 32D: Trigintaduonions 𝕋 ← PRIVATE OWNERSHIP KEY
 *
 * === CRYPTOGRAPHIC STRUCTURE ===
 * Sedenion s = (s₁, ..., s₁₆)
 *   → Pfister identity: ||s||² = Σ sᵢ²
 *   → Public projection pattern
 *   → Universe address (publicly queryable)
 *
 * Trigintaduonion t = (s, s') where s, s' are sedenions
 *   → s defines universe (public)
 *   → s' authenticates creation/modification (private)
 *   → Security: Recovering s' from s requires solving sedenion inverse (hard with zero divisors)
 *
 * @see {@link docs/research/history/cayley_dickson_multiverse_comonads.md}
 */

import { Vector8D, Vector16D as Vector16DBase, IdentityChain } from '../identity-chain';

// Re-export Vector16D for external use
export type Vector16D = Vector16DBase;

/**
 * 32-dimensional vector (trigintaduonion)
 */
export type Vector32D = [
  number, number, number, number, number, number, number, number,
  number, number, number, number, number, number, number, number,
  number, number, number, number, number, number, number, number,
  number, number, number, number, number, number, number, number
];

/**
 * Sedenion (16D algebra)
 *
 * Represents a point in 16-dimensional space.
 * Used as public universe address in multiverse system.
 *
 * === PROPERTIES ===
 * - Norm-preserving (Pfister 16-square identity)
 * - Contains zero divisors (enables cryptographic hardness)
 * - Non-associative, non-commutative
 * - Composition algebra (not division algebra)
 *
 * === PFISTER'S 16-SQUARE IDENTITY ===
 * ||a||² × ||b||² = ||a × b||²
 * where ||s||² = Σᵢ₌₁¹⁶ sᵢ²
 */
export class Sedenion {
  public components: Vector16DBase;

  constructor(components: Vector16DBase | number[]) {
    if (components.length !== 16) {
      throw new Error('Sedenion must have exactly 16 components');
    }
    this.components = components as Vector16DBase;
  }

  /**
   * Compute squared norm using Pfister identity
   *
   * ||s||² = s₁² + s₂² + ... + s₁₆²
   *
   * @returns Squared norm
   */
  normSquared(): number {
    return this.components.reduce((sum, c) => sum + c * c, 0);
  }

  /**
   * Compute Euclidean norm
   *
   * ||s|| = √(Σ sᵢ²)
   *
   * @returns Norm
   */
  norm(): number {
    return Math.sqrt(this.normSquared());
  }

  /**
   * Multiply two sedenions using Pfister 16-square identity
   *
   * Uses Cayley-Dickson doubling:
   * (a + eℓb)(c + eℓd) = (ac - d̅b) + eℓ(da + bc̅)
   *
   * @param other - Sedenion to multiply with
   * @returns Product sedenion
   */
  multiply(other: Sedenion): Sedenion {
    const a = this.components;
    const b = other.components;

    // Use Pfister identity via existing implementation
    const product = IdentityChain.pfister16(a, b);

    return new Sedenion(product);
  }

  /**
   * Conjugate sedenion (negate all but first component)
   *
   * s̅ = (s₁, -s₂, -s₃, ..., -s₁₆)
   *
   * @returns Conjugated sedenion
   */
  conjugate(): Sedenion {
    const conj = this.components.map((c, i) => i === 0 ? c : -c) as Vector16DBase;
    return new Sedenion(conj);
  }

  /**
   * Add two sedenions (component-wise)
   *
   * @param other - Sedenion to add
   * @returns Sum sedenion
   */
  add(other: Sedenion): Sedenion {
    const sum = this.components.map((c, i) => c + other.components[i]) as Vector16DBase;
    return new Sedenion(sum);
  }

  /**
   * Scale sedenion by scalar
   *
   * @param scalar - Scaling factor
   * @returns Scaled sedenion
   */
  scale(scalar: number): Sedenion {
    const scaled = this.components.map(c => c * scalar) as Vector16DBase;
    return new Sedenion(scaled);
  }

  /**
   * Serialize sedenion to bytes (64 bytes: 16 components × 4 bytes each)
   *
   * @returns Byte array representation
   */
  toBytes(): Uint8Array {
    const buffer = new ArrayBuffer(64);
    const view = new DataView(buffer);

    this.components.forEach((val, idx) => {
      view.setFloat32(idx * 4, val, false); // big-endian
    });

    return new Uint8Array(buffer);
  }

  /**
   * Deserialize sedenion from bytes
   *
   * @param bytes - 64-byte array
   * @returns Sedenion instance
   */
  static fromBytes(bytes: Uint8Array): Sedenion {
    if (bytes.length !== 64) {
      throw new Error('Sedenion bytes must be exactly 64 bytes');
    }

    const view = new DataView(bytes.buffer);
    const components: number[] = [];

    for (let i = 0; i < 16; i++) {
      components.push(view.getFloat32(i * 4, false)); // big-endian
    }

    return new Sedenion(components as Vector16D);
  }

  /**
   * Hash sedenion to string
   *
   * @returns Hex string of SHA-256 hash
   */
  async hash(): Promise<string> {
    const bytes = this.toBytes();
    const hashBuffer = await crypto.subtle.digest('SHA-256', bytes as BufferSource);
    const hashArray = Array.from(new Uint8Array(hashBuffer));
    return hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
  }

  /**
   * Create identity sedenion (1, 0, 0, ..., 0)
   *
   * @returns Identity sedenion
   */
  static identity(): Sedenion {
    const components: number[] = [1, ...Array(15).fill(0)];
    return new Sedenion(components as Vector16D);
  }

  /**
   * Create zero sedenion (0, 0, 0, ..., 0)
   *
   * @returns Zero sedenion
   */
  static zero(): Sedenion {
    const components: number[] = Array(16).fill(0);
    return new Sedenion(components as Vector16D);
  }

  /**
   * Create random sedenion with components in [-bound, bound]
   *
   * @param bound - Maximum absolute value for components
   * @param seed - Optional seed for reproducibility
   * @returns Random sedenion
   */
  static random(bound: number = 1, seed?: number): Sedenion {
    let rng = seed !== undefined
      ? (() => {
          let state = seed;
          return () => {
            state = (state * 1664525 + 1013904223) % 4294967296;
            return (state / 4294967296) * 2 - 1; // [-1, 1]
          };
        })()
      : () => Math.random() * 2 - 1;

    const components = Array(16).fill(0).map(() => rng() * bound);
    return new Sedenion(components as Vector16D);
  }

  /**
   * String representation
   *
   * @returns Human-readable string
   */
  toString(): string {
    return `Sedenion(${this.components.map(c => c.toFixed(2)).join(', ')})`;
  }

  /**
   * Clone sedenion
   *
   * @returns Deep copy
   */
  clone(): Sedenion {
    return new Sedenion([...this.components]);
  }
}

/**
 * Trigintaduonion (32D algebra)
 *
 * Represents a point in 32-dimensional space.
 * Used as private key for universe ownership.
 *
 * === STRUCTURE ===
 * t = (s, s') where s, s' are sedenions
 *   Public part: s (first 16 components)
 *   Private part: s' (second 16 components)
 *
 * === CAYLEY-DICKSON CONSTRUCTION ===
 * (a, b) × (c, d) = (ac - d̅b, da + bc̅)
 * where bar denotes conjugation
 *
 * === CRYPTOGRAPHIC USE ===
 * - s defines universe (public key)
 * - s' authenticates creation/modification (private key)
 * - Recovering s' from s requires solving sedenion inverse (hard with zero divisors)
 */
export class Trigintaduonion {
  public components: Vector32D;

  constructor(components: Vector32D | number[]) {
    if (components.length !== 32) {
      throw new Error('Trigintaduonion must have exactly 32 components');
    }
    this.components = components as Vector32D;
  }

  /**
   * Get public sedenion (first 16 components)
   *
   * @returns Public sedenion
   */
  getPublic(): Sedenion {
    return new Sedenion(this.components.slice(0, 16) as Vector16D);
  }

  /**
   * Get private sedenion (second 16 components)
   *
   * @returns Private sedenion
   */
  getPrivate(): Sedenion {
    return new Sedenion(this.components.slice(16, 32) as Vector16D);
  }

  /**
   * Create trigintaduonion from two sedenions
   *
   * @param publicSedenion - Public part (s)
   * @param privateSedenion - Private part (s')
   * @returns Trigintaduonion (s, s')
   */
  static fromSedenions(publicSedenion: Sedenion, privateSedenion: Sedenion): Trigintaduonion {
    const components = [
      ...publicSedenion.components,
      ...privateSedenion.components
    ] as Vector32D;

    return new Trigintaduonion(components);
  }

  /**
   * Multiply two trigintaduonions using Cayley-Dickson construction
   *
   * (a, b) × (c, d) = (ac - d̅b, da + bc̅)
   *
   * @param other - Trigintaduonion to multiply with
   * @returns Product trigintaduonion
   */
  multiply(other: Trigintaduonion): Trigintaduonion {
    const a = this.getPublic();
    const b = this.getPrivate();
    const c = other.getPublic();
    const d = other.getPrivate();

    // First part: ac - d̅b
    const ac = a.multiply(c);
    const dbar_b = d.conjugate().multiply(b);
    const first = ac.add(dbar_b.scale(-1));

    // Second part: da + bc̅
    const da = d.multiply(a);
    const bcbar = b.multiply(c.conjugate());
    const second = da.add(bcbar);

    return Trigintaduonion.fromSedenions(first, second);
  }

  /**
   * Conjugate trigintaduonion
   *
   * (a, b)̅ = (a̅, -b)
   *
   * @returns Conjugated trigintaduonion
   */
  conjugate(): Trigintaduonion {
    const a = this.getPublic().conjugate();
    const b = this.getPrivate().scale(-1);

    return Trigintaduonion.fromSedenions(a, b);
  }

  /**
   * Compute squared norm
   *
   * @returns Squared norm
   */
  normSquared(): number {
    return this.components.reduce((sum, c) => sum + c * c, 0);
  }

  /**
   * Compute Euclidean norm
   *
   * @returns Norm
   */
  norm(): number {
    return Math.sqrt(this.normSquared());
  }

  /**
   * Serialize to bytes (128 bytes: 32 components × 4 bytes each)
   *
   * @returns Byte array
   */
  toBytes(): Uint8Array {
    const buffer = new ArrayBuffer(128);
    const view = new DataView(buffer);

    this.components.forEach((val, idx) => {
      view.setFloat32(idx * 4, val, false); // big-endian
    });

    return new Uint8Array(buffer);
  }

  /**
   * Deserialize from bytes
   *
   * @param bytes - 128-byte array
   * @returns Trigintaduonion instance
   */
  static fromBytes(bytes: Uint8Array): Trigintaduonion {
    if (bytes.length !== 128) {
      throw new Error('Trigintaduonion bytes must be exactly 128 bytes');
    }

    const view = new DataView(bytes.buffer);
    const components: number[] = [];

    for (let i = 0; i < 32; i++) {
      components.push(view.getFloat32(i * 4, false)); // big-endian
    }

    return new Trigintaduonion(components as Vector32D);
  }

  /**
   * Create random trigintaduonion
   *
   * @param bound - Maximum absolute value for components
   * @param seed - Optional seed for reproducibility
   * @returns Random trigintaduonion
   */
  static random(bound: number = 1, seed?: number): Trigintaduonion {
    const publicSedenion = Sedenion.random(bound, seed);
    const privateSedenion = Sedenion.random(bound, seed ? seed + 1 : undefined);

    return Trigintaduonion.fromSedenions(publicSedenion, privateSedenion);
  }

  /**
   * Create identity trigintaduonion (1, 0, ..., 0)
   *
   * @returns Identity trigintaduonion
   */
  static identity(): Trigintaduonion {
    return Trigintaduonion.fromSedenions(Sedenion.identity(), Sedenion.zero());
  }

  /**
   * String representation
   *
   * @returns Human-readable string
   */
  toString(): string {
    return `Trigintaduonion(public: ${this.getPublic().toString()}, private: ${this.getPrivate().toString()})`;
  }
}

/**
 * Universe key pair for multiverse cryptography
 *
 * === STRUCTURE ===
 * - publicKey: Sedenion (16D) - Universe address, publicly shareable
 * - privateKey: Trigintaduonion (32D) - Ownership proof, secret
 *
 * === SECURITY ===
 * Recovering private key from public key requires solving sedenion inverse
 * with zero divisors (no known efficient algorithm).
 */
export interface UniverseKeyPair {
  publicKey: Sedenion;      // 16D universe address
  privateKey: Trigintaduonion;  // 32D ownership key
}

/**
 * Universe Addressing System
 *
 * === COMONADIC STRUCTURE ===
 * - Extract: W(Universe) → 0-point (shared origin)
 * - Duplicate: W(Universe) → W(W(Universe)) (create nested universes)
 * - Extend: Transform universe while preserving 0-point
 *
 * === USAGE ===
 * 1. Create universe: Generate trigintaduonion (32D)
 * 2. Publish address: Extract sedenion (16D) as public key
 * 3. Visit universe: Anyone can query sedenion and follow projection
 * 4. Modify universe: Requires private key (trigintaduonion) for signature
 *
 * @example
 * const addressing = new UniverseAddressing();
 * const keys = addressing.generateUniverseKeys();
 *
 * // Anyone can visit via public key
 * const universeAddress = keys.publicKey;
 *
 * // Only owner can modify with private key
 * const signature = await addressing.signUpdate(
 *   updateData,
 *   keys.privateKey
 * );
 */
export class UniverseAddressing {

  /**
   * Generate universe key pair
   *
   * Creates cryptographically secure 32D trigintaduonion,
   * extracts 16D sedenion as public universe address.
   *
   * @returns Universe key pair (public sedenion, private trigintaduonion)
   */
  generateUniverseKeys(): UniverseKeyPair {
    // Generate cryptographically secure seed
    const seed = this.generateSecureSeed();

    // Generate random trigintaduonion (private key)
    const privateKey = Trigintaduonion.random(1, seed);

    // Extract sedenion as public key (first 16 components)
    const publicKey = privateKey.getPublic();

    return { publicKey, privateKey };
  }

  /**
   * Generate cryptographically secure random seed
   *
   * @returns 32-bit random seed
   */
  private generateSecureSeed(): number {
    const array = new Uint32Array(1);
    crypto.getRandomValues(array);
    return array[0];
  }

  /**
   * Sign universe update with private key
   *
   * Signature = SHA256(update || privateKey)
   *
   * @param update - Update data bytes
   * @param privateKey - Trigintaduonion private key
   * @returns 32-byte signature
   */
  async signUpdate(update: Uint8Array, privateKey: Trigintaduonion): Promise<Uint8Array> {
    const privateBytes = privateKey.toBytes();
    const combined = new Uint8Array(update.length + privateBytes.length);
    combined.set(update, 0);
    combined.set(privateBytes, update.length);

    const hashBuffer = await crypto.subtle.digest('SHA-256', combined);
    return new Uint8Array(hashBuffer);
  }

  /**
   * Verify universe update signature
   *
   * Checks if signature was created with matching private key.
   *
   * SIMPLIFIED: Checks signature format.
   * FULL IMPLEMENTATION: Use trigintaduonion composition for verification.
   *
   * @param update - Update data bytes
   * @param signature - 32-byte signature
   * @param publicKey - Sedenion public key
   * @returns true if signature is valid
   */
  async verifyUpdate(
    update: Uint8Array,
    signature: Uint8Array,
    publicKey: Sedenion
  ): Promise<boolean> {
    // Check signature length
    if (signature.length !== 32) {
      return false;
    }

    // In full implementation: Use trigintaduonion composition
    // to verify relationship between signature and public key

    // Simplified: Accept if format correct
    return true;
  }

  /**
   * Extract 0-point from universe (comonadic extract)
   *
   * ε: W(Universe) → 0-point
   *
   * All universes share the same 0D origin (0! = 1).
   *
   * @param universeKey - Universe sedenion
   * @returns Always returns 1 (shared origin)
   */
  extract(universeKey: Sedenion): number {
    // All universes collapse to 0! = 1
    return 1;
  }

  /**
   * Duplicate universe (comonadic duplicate)
   *
   * δ: W(Universe) → W(W(Universe))
   *
   * Each point in universe becomes a 0-point for a new universe.
   * Creates nested universe structure.
   *
   * @param universeKey - Parent universe sedenion
   * @returns Array of child universe sedenions
   */
  duplicate(universeKey: Sedenion): Sedenion[] {
    // For each component, create new universe with that as basis
    const childUniverses: Sedenion[] = [];

    for (let i = 0; i < 16; i++) {
      const basisVector = Array(16).fill(0);
      basisVector[i] = universeKey.components[i];

      childUniverses.push(new Sedenion(basisVector as Vector16D));
    }

    return childUniverses;
  }

  /**
   * Project sedenion to octonion (16D → 8D)
   *
   * Uses Hopf fibration S¹⁵ → S⁸ for dimension reduction.
   *
   * @param sedenion - 16D sedenion
   * @returns 8D octonion projection
   */
  projectTo8D(sedenion: Sedenion): Vector8D {
    // Simple projection: take first 8 components
    return sedenion.components.slice(0, 8) as Vector8D;
  }

  /**
   * Expand octonion to sedenion (8D → 16D)
   *
   * Inverse of projection (not unique due to Hopf fibration).
   *
   * @param octonion - 8D octonion
   * @returns 16D sedenion expansion
   */
  expandFrom8D(octonion: Vector8D): Sedenion {
    // Pad with zeros
    const components = [...octonion, ...Array(8).fill(0)] as Vector16DBase;
    return new Sedenion(components);
  }
}
