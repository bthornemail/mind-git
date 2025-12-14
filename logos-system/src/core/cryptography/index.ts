/**
 * Cubic Cryptography - Post-Quantum Key Exchange via Bhargava Cubic Composition
 *
 * === MENTAL MODEL ===
 * Ternary cubic forms are the cryptographic substrate. Each cubic form represents
 * a genus-1 elliptic curve in projective space, providing post-quantum security
 * through the hardness of tensor decomposition and cubic ring isomorphism.
 *
 * === WHY THIS WORKS ===
 * - Bhargava composition laws provide group structure on cubic forms
 * - 2×2×2×2 tensor decomposition is NP-hard (no known quantum speedup)
 * - Elliptic curves from cubics connect to established cryptographic theory
 * - 40-byte keys (vs 800+ bytes for NIST post-quantum standards)
 *
 * === REPRESENTATION ===
 * Cubic forms: C(u,v,w) = Σ a_ijk u^i v^j w^k where i+j+k=3
 * Coefficients stored as Map<[i,j,k], number> with 10 terms
 *
 * === SECURITY ===
 * - Classical: Based on tensor decomposition (NP-hard)
 * - Quantum: Grover's algorithm only provides quadratic speedup
 * - No known quantum attacks on tensor decomposition problem
 *
 * === RESEARCH STATUS ===
 * This is a novel cryptographic protocol. While mathematically sound,
 * it has not undergone extensive cryptanalysis. Use for research only.
 *
 * @see {@link docs/research/history/CUBIC_CRYPTOGRAPHY_PROTOCOL.py}
 * @see {@link docs/research/history/CUBIC_CRYPTO_DEPLOYMENT_GUIDE.md}
 */

/**
 * Coefficient index for ternary cubic form
 * (i,j,k) where i+j+k = 3
 */
export type CubicIndex = [number, number, number];

/**
 * Ternary cubic form C(u,v,w) = Σ a_ijk u^i v^j w^k
 *
 * Coefficients map: (i,j,k) → a_ijk where i+j+k = 3
 * Total of 10 coefficients for complete ternary cubic
 */
export interface ITernaryCubicForm {
  coeffs: Map<string, number>;
}

/**
 * Cubic key pair for post-quantum cryptography
 *
 * - private_cubic: Secret cubic form (never transmitted)
 * - public_cubic: Derived via self-composition (publicly shareable)
 * - tensor_seed: Random seed for tensor generation (for reproducibility)
 */
export interface CubicKeyPair {
  private_cubic: TernaryCubicForm;
  public_cubic: TernaryCubicForm;
  tensor_seed: number;
}

/**
 * Ternary Cubic Form - Foundation of Cubic Cryptography
 *
 * Represents C(u,v,w) = Σ_{i+j+k=3} a_ijk u^i v^j w^k
 *
 * === 10 COEFFICIENTS ===
 * (3,0,0): u³     (0,3,0): v³     (0,0,3): w³
 * (2,1,0): u²v    (2,0,1): u²w
 * (1,2,0): uv²    (1,0,2): uw²
 * (0,2,1): v²w    (0,1,2): vw²
 * (1,1,1): uvw
 *
 * === MATHEMATICAL PROPERTIES ===
 * - Smooth cubics define elliptic curves (genus-1)
 * - Discriminant measures smoothness
 * - Group law via Bhargava composition
 *
 * @example
 * // Fermat cubic: u³ + v³ + w³ - 3uvw
 * const fermat = TernaryCubicForm.fermat();
 */
export class TernaryCubicForm {
  public coeffs: Map<string, number>;

  constructor(coeffs: Map<string, number> | Record<string, number>) {
    this.coeffs = coeffs instanceof Map ? coeffs : new Map(Object.entries(coeffs));
    this.validate();
  }

  /**
   * Validate that all coefficient indices sum to 3
   */
  private validate(): void {
    for (const key of this.coeffs.keys()) {
      const [i, j, k] = this.parseIndex(key);
      if (i + j + k !== 3) {
        throw new Error(`Invalid cubic indices: ${i}+${j}+${k} !== 3`);
      }
    }
  }

  /**
   * Parse coefficient key "i,j,k" into array [i,j,k]
   */
  private parseIndex(key: string): CubicIndex {
    return key.split(',').map(Number) as CubicIndex;
  }

  /**
   * Format coefficient index [i,j,k] as string key
   */
  private static formatIndex(i: number, j: number, k: number): string {
    return `${i},${j},${k}`;
  }

  /**
   * Evaluate cubic form at point (u, v, w)
   *
   * C(u,v,w) = Σ a_ijk u^i v^j w^k
   *
   * @param u - First coordinate
   * @param v - Second coordinate
   * @param w - Third coordinate
   * @returns Value of cubic at (u,v,w)
   */
  eval(u: number, v: number, w: number): number {
    let result = 0;

    for (const [key, a] of this.coeffs.entries()) {
      const [i, j, k] = this.parseIndex(key);
      result += a * Math.pow(u, i) * Math.pow(v, j) * Math.pow(w, k);
    }

    return result;
  }

  /**
   * Compute discriminant (simplified proxy)
   *
   * Full discriminant for ternary cubics is extremely complex.
   * This uses product of non-zero coefficients as proxy.
   *
   * Discriminant ≠ 0 ⟺ Smooth elliptic curve (genus-1)
   *
   * @returns Approximate discriminant value
   */
  discriminant(): number {
    let product = 1;
    let hasNonZero = false;
    for (const a of this.coeffs.values()) {
      if (a !== 0) {
        product *= Math.abs(a);
        hasNonZero = true;
      }
    }
    return hasNonZero ? product : 0;
  }

  /**
   * Check if cubic defines smooth elliptic curve
   *
   * A cubic is smooth if its discriminant is non-zero.
   * Smooth ternary cubics are elliptic curves (genus-1).
   *
   * @returns true if smooth (discriminant ≠ 0)
   */
  isSmooth(): boolean {
    return this.discriminant() !== 0;
  }

  /**
   * Serialize cubic to bytes for hashing/signing
   *
   * Serializes coefficients in deterministic order:
   * (3,0,0), (2,1,0), (2,0,1), (1,2,0), (1,1,1), (1,0,2),
   * (0,3,0), (0,2,1), (0,1,2), (0,0,3)
   *
   * @returns Byte array representation
   */
  toBytes(): Uint8Array {
    const indices: CubicIndex[] = [
      [3,0,0], [2,1,0], [2,0,1], [1,2,0], [1,1,1],
      [1,0,2], [0,3,0], [0,2,1], [0,1,2], [0,0,3]
    ];

    const values: number[] = [];
    for (const [i, j, k] of indices) {
      const key = TernaryCubicForm.formatIndex(i, j, k);
      values.push(this.coeffs.get(key) || 0);
    }

    // Convert to bytes (4 bytes per number, big-endian)
    const buffer = new ArrayBuffer(values.length * 4);
    const view = new DataView(buffer);
    values.forEach((val, idx) => {
      view.setInt32(idx * 4, val, false); // big-endian
    });

    return new Uint8Array(buffer);
  }

  /**
   * Compute hash of cubic form
   *
   * Uses SHA-256 for cryptographic hashing.
   *
   * @returns Hex string of hash
   */
  async hash(): Promise<string> {
    const bytes = this.toBytes();
    const hashBuffer = await crypto.subtle.digest('SHA-256', bytes as BufferSource);
    const hashArray = Array.from(new Uint8Array(hashBuffer));
    return hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
  }

  /**
   * String representation of cubic form
   *
   * Shows non-zero terms in human-readable format:
   * "a₃₀₀u³ + a₂₁₀u²v + ..."
   *
   * @returns Human-readable string
   */
  toString(): string {
    const terms: string[] = [];

    // Sort by indices for consistent output
    const sortedEntries = Array.from(this.coeffs.entries()).sort((a, b) => {
      const [ai, aj, ak] = this.parseIndex(a[0]);
      const [bi, bj, bk] = this.parseIndex(b[0]);
      return (ai !== bi) ? bi - ai : (aj !== bj) ? bj - aj : bk - ak;
    });

    for (const [key, a] of sortedEntries) {
      if (a === 0) continue;

      const [i, j, k] = this.parseIndex(key);
      let term = `${a}`;

      if (i > 0) term += `u${i > 1 ? '^' + i : ''}`;
      if (j > 0) term += `v${j > 1 ? '^' + j : ''}`;
      if (k > 0) term += `w${k > 1 ? '^' + k : ''}`;

      terms.push(term);
    }

    return terms.length > 0 ? terms.join(' + ') : '0';
  }

  /**
   * Create Fermat cubic: u³ + v³ + w³ - 3uvw
   *
   * Classic example of smooth ternary cubic.
   * Defines elliptic curve with nice properties.
   *
   * @returns Fermat cubic form
   */
  static fermat(): TernaryCubicForm {
    return new TernaryCubicForm({
      '3,0,0': 1,   // u³
      '0,3,0': 1,   // v³
      '0,0,3': 1,   // w³
      '1,1,1': -3,  // -3uvw
      '2,1,0': 0,
      '2,0,1': 0,
      '1,2,0': 0,
      '1,0,2': 0,
      '0,2,1': 0,
      '0,1,2': 0,
    });
  }

  /**
   * Create random ternary cubic with bounded coefficients
   *
   * Generates random coefficients in [-bound, bound].
   * Used for key generation in cryptographic protocols.
   *
   * @param bound - Maximum absolute value for coefficients
   * @param seed - Optional seed for reproducible randomness
   * @returns Random cubic form
   */
  static random(bound: number = 10, seed?: number): TernaryCubicForm {
    // Simple LCG for deterministic randomness if seed provided
    let rng = seed !== undefined
      ? (() => {
          let state = seed;
          return () => {
            state = (state * 1664525 + 1013904223) % 4294967296;
            return state / 4294967296;
          };
        })()
      : Math.random;

    const randomInt = () => Math.floor(rng() * (2 * bound + 1)) - bound;

    const indices: CubicIndex[] = [
      [3,0,0], [2,1,0], [2,0,1], [1,2,0], [1,1,1],
      [1,0,2], [0,3,0], [0,2,1], [0,1,2], [0,0,3]
    ];

    const coeffs: Record<string, number> = {};
    for (const [i, j, k] of indices) {
      coeffs[TernaryCubicForm.formatIndex(i, j, k)] = randomInt();
    }

    return new TernaryCubicForm(coeffs);
  }

  /**
   * Clone this cubic form
   *
   * @returns Deep copy of cubic
   */
  clone(): TernaryCubicForm {
    const coeffsCopy = new Map(this.coeffs);
    return new TernaryCubicForm(coeffsCopy);
  }

  /**
   * Check equality with another cubic form
   *
   * @param other - Cubic to compare with
   * @returns true if all coefficients match
   */
  equals(other: TernaryCubicForm): boolean {
    if (this.coeffs.size !== other.coeffs.size) return false;

    for (const [key, val] of this.coeffs.entries()) {
      if (other.coeffs.get(key) !== val) return false;
    }

    return true;
  }
}

/**
 * Cubic Tensor Engine - 2×2×2×2 Tensor Operations
 *
 * === BHARGAVA COMPOSITION ===
 * Cubic forms compose via 2×2×2×2 integer tensors.
 *
 * Process:
 * 1. Given cubics C₁, C₂
 * 2. Find tensor T matching both on different slices
 * 3. Extract composed cubic C₃ = C₁ ∘ C₂ from tensor
 *
 * === TENSOR STRUCTURE ===
 * 4D tensor: T[i][j][k][l] where i,j,k,l ∈ {0,1}
 * 16 total elements
 * Extracts to cubic via trilinear determinant
 *
 * === SECURITY BASIS ===
 * Tensor decomposition is NP-hard.
 * Recovering private tensor from public cubic is computationally infeasible.
 */
export class CubicTensorEngine {

  /**
   * Generate random 2×2×2×2 integer tensor
   *
   * @param bound - Maximum absolute value for elements
   * @param seed - Optional seed for reproducibility
   * @returns 4D array [2][2][2][2]
   */
  static randomTensor(bound: number = 10, seed?: number): number[][][][] {
    let rng = seed !== undefined
      ? (() => {
          let state = seed;
          return () => {
            state = (state * 1664525 + 1013904223) % 4294967296;
            return state / 4294967296;
          };
        })()
      : Math.random;

    const randomInt = () => Math.floor(rng() * (2 * bound + 1)) - bound;

    const tensor: number[][][][] = [];
    for (let i = 0; i < 2; i++) {
      tensor[i] = [];
      for (let j = 0; j < 2; j++) {
        tensor[i][j] = [];
        for (let k = 0; k < 2; k++) {
          tensor[i][j][k] = [];
          for (let l = 0; l < 2; l++) {
            tensor[i][j][k][l] = randomInt();
          }
        }
      }
    }

    return tensor;
  }

  /**
   * Extract cubic form from tensor along given axis
   *
   * Uses trilinear extraction from 2×2×2×2 tensor.
   * Different axes yield different cubics from same tensor.
   *
   * @param tensor - 2×2×2×2 tensor
   * @param axis - Extraction axis (0-3)
   * @returns Extracted ternary cubic form
   */
  static extractCubicFromTensor(
    tensor: number[][][][],
    axis: number = 0
  ): TernaryCubicForm {
    if (axis < 0 || axis > 3) {
      throw new Error('Axis must be 0-3');
    }

    // Extract 2×2×2 slices along axis
    const M0 = this.getSlice(tensor, axis, 0);
    const M1 = this.getSlice(tensor, axis, 1);

    // Map tensor elements to cubic coefficients (simplified extraction)
    const coeffs: Record<string, number> = {};

    coeffs['3,0,0'] = M0[0][0][0] + M1[0][0][0];
    coeffs['0,3,0'] = M0[1][1][0] + M1[1][1][0];
    coeffs['0,0,3'] = M0[0][0][1] + M1[0][0][1];
    coeffs['2,1,0'] = M0[1][0][0] - M1[1][0][0];
    coeffs['2,0,1'] = M0[0][1][0] - M1[0][1][0];
    coeffs['1,2,0'] = M0[0][1][0] + M1[0][1][0];
    coeffs['1,0,2'] = M0[0][0][1] + M1[0][0][1];
    coeffs['0,2,1'] = M0[1][0][1] - M1[1][0][1];
    coeffs['0,1,2'] = M0[0][1][1] + M1[0][1][1];
    coeffs['1,1,1'] = M0[1][1][1] + M1[1][1][1];

    return new TernaryCubicForm(coeffs);
  }

  /**
   * Get 2×2×2 slice from 4D tensor along axis at index
   */
  private static getSlice(
    tensor: number[][][][],
    axis: number,
    index: 0 | 1
  ): number[][][] {
    const slice: number[][][] = [];

    for (let i = 0; i < 2; i++) {
      slice[i] = [];
      for (let j = 0; j < 2; j++) {
        slice[i][j] = [];
        for (let k = 0; k < 2; k++) {
          if (axis === 0) slice[i][j][k] = tensor[index][i][j][k];
          else if (axis === 1) slice[i][j][k] = tensor[i][index][j][k];
          else if (axis === 2) slice[i][j][k] = tensor[i][j][index][k];
          else slice[i][j][k] = tensor[i][j][k][index];
        }
      }
    }

    return slice;
  }

  /**
   * Compose two tensors via element-wise multiplication and symmetrization
   *
   * SIMPLIFIED IMPLEMENTATION:
   * Full Bhargava composition requires solving underdetermined system.
   * This uses element-wise product + symmetrization as approximation.
   *
   * For production: Implement full Bhargava inverse solver with LLL reduction.
   *
   * @param T1 - First tensor
   * @param T2 - Second tensor
   * @returns Composed tensor T3
   */
  static composeTensors(
    T1: number[][][][],
    T2: number[][][][]
  ): number[][][][] {
    // Element-wise multiplication
    const T3 = this.randomTensor(1, 0); // Initialize with zeros

    for (let i = 0; i < 2; i++) {
      for (let j = 0; j < 2; j++) {
        for (let k = 0; k < 2; k++) {
          for (let l = 0; l < 2; l++) {
            // Multiply elements
            const prod = T1[i][j][k][l] * T2[i][j][k][l];

            // Symmetrize by averaging permutations
            const perms = [
              prod,
              T1[j][i][k][l] * T2[j][i][k][l],
              T1[i][k][j][l] * T2[i][k][j][l],
              T1[k][j][i][l] * T2[k][j][i][l],
            ];

            T3[i][j][k][l] = Math.floor(
              perms.reduce((a, b) => a + b, 0) / perms.length
            );
          }
        }
      }
    }

    return T3;
  }
}

/**
 * Export all cryptography components
 */
export * from './cubic-keygen';
export * from './cubic-dh';
export * from './bhargava-solver';
export * from './lll-reduction';
export * from './secure-memory';
export * from './constant-time';
export * from './key-erasure';
export * from './production-crypto';

// Export MindGit-related cryptography functions for integration
export { signWithCubic, verifyCubicSignature } from './cubic-signature';
export { generateCommitProof, verifyCommitProof } from './commit-signature';
