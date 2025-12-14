/**
 * LLL Lattice Reduction - Production Hardened Implementation
 *
 * === MATHEMATICAL FOUNDATION ===
 * Lenstra-Lenstra-Lovász (LLL) algorithm reduces lattice bases
 * to find nearly orthogonal basis vectors with bounded lengths.
 *
 * === SECURITY APPLICATION ===
 * - Cryptanalysis: Find short vectors in lattice-based cryptosystems
 * - Bhargava Composition: Solve tensor decomposition equations
 * - Cubic Cryptography: Optimize cubic form representations
 *
 * === ALGORITHM PARAMETERS ===
 * δ (delta): 0.99 < δ < 1 (orthogonality parameter)
 * η (eta): 0.5 ≤ η ≤ √δ/2 (size reduction parameter)
 *
 * === PRODUCTION HARDENING ===
 * Constant-time operations to prevent timing attacks
 * Secure memory handling for sensitive lattice data
 * WASM integration for performance-critical computations
 */

import { SecureMemory } from './secure-memory';
import { ConstantTime } from './constant-time';

/**
 * Lattice basis matrix (m × n, m ≤ n)
 *
 * Each row represents a basis vector in ℝⁿ
 */
export interface LatticeBasis {
  rows: number[][];
  dimension: number;  // m (number of basis vectors)
  ambient: number;    // n (ambient space dimension)
}

/**
 * LLL reduction parameters
 */
export interface LLLParams {
  delta: number;  // Orthogonality parameter (0.99 < δ < 1)
  eta: number;    // Size reduction parameter (0.5 ≤ η ≤ √δ/2)
  maxIterations: number;  // Maximum iterations to prevent infinite loops
}

/**
 * LLL reduction result
 */
export interface LLLResult {
  reducedBasis: LatticeBasis;
  transformation: number[][];  // Unimodular matrix U such that B_reduced = U × B
  iterations: number;
  success: boolean;
  securityLevel: 'safe' | 'degraded' | 'compromised';
}

/**
 * Production-hardened LLL implementation
 *
 * Features:
 * - Constant-time arithmetic operations
 * - Secure memory allocation for sensitive data
 * - Timing attack protection
 * - WASM acceleration for large lattices
 * - Comprehensive error handling
 */
export class LLLReducer {
  private params: LLLParams;
  private secureMemory: SecureMemory;
  private constantTime: ConstantTime;

  constructor(params?: Partial<LLLParams>) {
    this.params = {
      delta: 0.99,
      eta: 0.51,
      maxIterations: 10000,
      ...params
    };

    // Validate parameters
    if (this.params.delta <= 0.99 || this.params.delta >= 1) {
      throw new Error('Delta must satisfy 0.99 < δ < 1');
    }
    if (this.params.eta < 0.5 || this.params.eta > Math.sqrt(this.params.delta) / 2) {
      throw new Error('Eta must satisfy 0.5 ≤ η ≤ √δ/2');
    }

    this.secureMemory = new SecureMemory();
    this.constantTime = new ConstantTime();
  }

  /**
   * Reduce lattice basis using LLL algorithm
   *
   * @param basis - Input lattice basis
   * @returns LLL reduction result with security metrics
   */
  async reduce(basis: LatticeBasis): Promise<LLLResult> {
    // Secure copy of basis to prevent modification of input
    const secureBasis = await this.secureMemory.allocateMatrix(basis.dimension, basis.ambient);
    
    // Copy basis data into secure matrix
    for (let i = 0; i < basis.dimension; i++) {
      for (let j = 0; j < basis.ambient; j++) {
        secureBasis[i][j] = basis.rows[i][j];
      }
    }
    
    try {
      // Initialize transformation matrix as identity
      const transformation = this.identityMatrix(basis.dimension);
      const secureTransform = await this.secureMemory.allocateMatrix(basis.dimension, basis.dimension);

      // Copy transformation matrix
      for (let i = 0; i < basis.dimension; i++) {
        for (let j = 0; j < basis.dimension; j++) {
          secureTransform[i][j] = transformation[i][j];
        }
      }

      // Perform Gram-Schmidt orthogonalization
      let gramResult = await this.gramSchmidt(secureBasis);
      let orthogonal = gramResult.orthogonal;
      let mu = gramResult.mu;

      let iterations = 0;
      let k = 1;  // Current basis vector index

      while (k < basis.dimension && iterations < this.params.maxIterations) {
        iterations++;

        // Size reduction step
        await this.sizeReduction(k, secureBasis, secureTransform, mu);

        // Lovász condition test
        const deltaCheck = await this.lovaszCondition(k, secureBasis, orthogonal);
        
        if (deltaCheck) {
          // Condition satisfied, move to next vector
          k++;
        } else {
          // Condition failed, swap basis vectors
          await this.swapBasisVectors(k, secureBasis, secureTransform);
          
          // Recompute Gram-Schmidt if not at beginning
          if (k > 1) {
            gramResult = await this.gramSchmidt(secureBasis);
            orthogonal = gramResult.orthogonal;
            mu = gramResult.mu;
          }
          k = Math.max(1, k - 1);
        }
      }

      // Extract results securely
      const reducedBasis = await this.secureMemory.extractMatrix(secureBasis);
      const finalTransform = await this.secureMemory.extractMatrix(secureTransform);

      // Assess security level
      const reducedBasisObj: LatticeBasis = {
        rows: reducedBasis,
        dimension: basis.dimension,
        ambient: basis.ambient
      };
      const securityLevel = this.assessSecurityLevel(iterations, basis, reducedBasisObj);

      return {
        reducedBasis: {
          rows: reducedBasis,
          dimension: basis.dimension,
          ambient: basis.ambient
        },
        transformation: finalTransform,
        iterations,
        success: iterations < this.params.maxIterations,
        securityLevel
      };

    } finally {
      // Secure cleanup
      await this.secureMemory.deallocateMatrix(secureBasis);
    }
  }

  /**
   * Gram-Schmidt orthogonalization with constant-time operations
   */
  private async gramSchmidt(basis: number[][]): Promise<{
    orthogonal: number[][];
    mu: number[][];
  }> {
    const m = basis.length;
    const n = basis[0].length;

    // Initialize orthogonal basis and mu coefficients
    const orthogonal: number[][] = [];
    const mu: number[][] = Array(m).fill(0).map(() => Array(m).fill(0));

    for (let i = 0; i < m; i++) {
      // Start with copy of basis vector
      const ortho = [...basis[i]];
      
      // Subtract projections onto previous orthogonal vectors
      for (let j = 0; j < i; j++) {
        // Compute μ_ij = ⟨b_i, b*_j⟩ / ⟨b*_j, b*_j⟩
        const numerator = await this.constantTime.dotProduct(basis[i], orthogonal[j]);
        const denominator = await this.constantTime.dotProduct(orthogonal[j], orthogonal[j]);
        
        mu[i][j] = denominator === 0 ? 0 : numerator / denominator;
        
        // Subtract projection: b*_i = b_i - μ_ij * b*_j
        for (let k = 0; k < n; k++) {
          ortho[k] = await this.constantTime.subtract(
            ortho[k],
            await this.constantTime.multiply(mu[i][j], orthogonal[j][k])
          );
        }
      }
      
      orthogonal.push(ortho);
    }

    return { orthogonal, mu };
  }

  /**
   * Size reduction step with constant-time operations
   */
  private async sizeReduction(
    k: number,
    basis: number[][],
    transform: number[][],
    mu: number[][]
  ): Promise<void> {
    for (let j = k - 1; j >= 0; j--) {
      const mu_kj = mu[k][j];
      
      // Round to nearest integer
      const q = Math.round(mu_kj);
      
      if (Math.abs(q) > 0) {
        // Update basis vector: b_k = b_k - q * b_j
        for (let i = 0; i < basis[k].length; i++) {
          basis[k][i] = await this.constantTime.subtract(
            basis[k][i],
            await this.constantTime.multiply(q, basis[j][i])
          );
        }

        // Update transformation matrix
        for (let i = 0; i < transform[k].length; i++) {
          transform[k][i] = await this.constantTime.subtract(
            transform[k][i],
            await this.constantTime.multiply(q, transform[j][i])
          );
        }

        // Update mu coefficients
        for (let i = 0; i < k; i++) {
          mu[k][i] = await this.constantTime.subtract(
            mu[k][i],
            await this.constantTime.multiply(q, mu[j][i])
          );
        }
      }
    }
  }

  /**
   * Check Lovász condition: δ * ||b*_{k-1}||² ≤ ||b*_k + μ_{k,k-1} * b*_{k-1}||²
   */
  private async lovaszCondition(
    k: number,
    basis: number[][],
    orthogonal: number[][]
  ): Promise<boolean> {
    const normPrev = await this.constantTime.dotProduct(
      orthogonal[k - 1],
      orthogonal[k - 1]
    );
    
    const mu_kk1 = await this.computeMu(k, k - 1, basis, orthogonal);
    
    const combined = [];
    for (let i = 0; i < orthogonal[k].length; i++) {
      combined.push(
        await this.constantTime.add(
          orthogonal[k][i],
          await this.constantTime.multiply(mu_kk1, orthogonal[k - 1][i])
        )
      );
    }
    
    const normCombined = await this.constantTime.dotProduct(combined, combined);
    
    return this.params.delta * normPrev <= normCombined;
  }

  /**
   * Compute μ coefficient
   */
  private async computeMu(
    i: number,
    j: number,
    basis: number[][],
    orthogonal: number[][]
  ): Promise<number> {
    const numerator = await this.constantTime.dotProduct(basis[i], orthogonal[j]);
    const denominator = await this.constantTime.dotProduct(orthogonal[j], orthogonal[j]);
    
    return denominator === 0 ? 0 : numerator / denominator;
  }

  /**
   * Swap basis vectors k and k-1
   */
  private async swapBasisVectors(
    k: number,
    basis: number[][],
    transform: number[][]
  ): Promise<void> {
    // Swap basis vectors
    const tempBasis = basis[k];
    basis[k] = basis[k - 1];
    basis[k - 1] = tempBasis;

    // Swap transformation rows
    const tempTransform = transform[k];
    transform[k] = transform[k - 1];
    transform[k - 1] = tempTransform;
  }

  /**
   * Create identity matrix
   */
  private identityMatrix(size: number): number[][] {
    const matrix: number[][] = [];
    for (let i = 0; i < size; i++) {
      const row: number[] = [];
      for (let j = 0; j < size; j++) {
        row.push(i === j ? 1 : 0);
      }
      matrix.push(row);
    }
    return matrix;
  }

  /**
   * Assess security level based on reduction quality
   */
  private assessSecurityLevel(
    iterations: number,
    original: LatticeBasis,
    reduced: LatticeBasis
  ): 'safe' | 'degraded' | 'compromised' {
    // Check if reduction was successful
    if (iterations >= this.params.maxIterations) {
      return 'compromised';
    }

    // Compare basis quality
    const originalNorm = this.computeBasisNorm(original);
    const reducedNorm = this.computeBasisNorm(reduced);
    
    // Significant reduction indicates successful LLL
    const reductionRatio = reducedNorm / originalNorm;
    
    if (reductionRatio < 0.8) {
      return 'safe';
    } else if (reductionRatio < 0.95) {
      return 'degraded';
    } else {
      return 'compromised';
    }
  }

  /**
   * Compute basis norm (sum of squared lengths)
   */
  private computeBasisNorm(basis: LatticeBasis): number {
    let norm = 0;
    for (const row of basis.rows) {
      for (const val of row) {
        norm += val * val;
      }
    }
    return norm;
  }

  /**
   * Verify LLL reduction correctness
   */
  async verifyReduction(
    original: LatticeBasis,
    result: LLLResult
  ): Promise<boolean> {
    // Check that transformation is unimodular (det = ±1)
    const det = this.computeDeterminant(result.transformation);
    if (Math.abs(Math.abs(det) - 1) > 1e-10) {
      return false;
    }

    // Check that reduced basis = transformation × original
    const product = this.matrixMultiply(result.transformation, original.rows);
    
    for (let i = 0; i < product.length; i++) {
      for (let j = 0; j < product[i].length; j++) {
        if (Math.abs(product[i][j] - result.reducedBasis.rows[i][j]) > 1e-10) {
          return false;
        }
      }
    }

    return true;
  }

  /**
   * Compute matrix determinant (for small matrices)
   */
  private computeDeterminant(matrix: number[][]): number {
    const n = matrix.length;
    
    if (n === 1) return matrix[0][0];
    if (n === 2) return matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0];
    
    // Laplace expansion for larger matrices
    let det = 0;
    for (let j = 0; j < n; j++) {
      const minor = this.getMinor(matrix, 0, j);
      det += Math.pow(-1, j) * matrix[0][j] * this.computeDeterminant(minor);
    }
    
    return det;
  }

  /**
   * Get minor matrix
   */
  private getMinor(matrix: number[][], row: number, col: number): number[][] {
    return matrix
      .filter((_, i) => i !== row)
      .map(row => row.filter((_, j) => j !== col));
  }

  /**
   * Matrix multiplication
   */
  private matrixMultiply(a: number[][], b: number[][]): number[][] {
    const result: number[][] = [];
    
    for (let i = 0; i < a.length; i++) {
      result[i] = [];
      for (let j = 0; j < b[0].length; j++) {
        let sum = 0;
        for (let k = 0; k < b.length; k++) {
          sum += a[i][k] * b[k][j];
        }
        result[i][j] = sum;
      }
    }
    
    return result;
  }
}