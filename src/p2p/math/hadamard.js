/**
 * Hadamard Matrix for Pfister 16-Square Identity
 * Orthogonal skeleton that holds Pfister's identity together
 * 
 * The 8×8 Hadamard matrix of Sylvester type, scaled by 1/2
 * This ensures auxiliary u_k terms are mutually orthogonal
 */

class HadamardMatrix {
  // 8×8 Sylvester Hadamard matrix scaled by 1/2
  static HADAMARD_8 = [
    [ 0.5, -0.5, -0.5, -0.5, -0.5, -0.5, -0.5, -0.5],
    [-0.5,  0.5, -0.5,  0.5, -0.5,  0.5, -0.5,  0.5],
    [-0.5, -0.5,  0.5, -0.5,  0.5, -0.5,  0.5, -0.5],
    [-0.5,  0.5, -0.5,  0.5, -0.5,  0.5, -0.5,  0.5],
    [-0.5, -0.5,  0.5, -0.5,  0.5, -0.5,  0.5, -0.5],
    [-0.5,  0.5, -0.5,  0.5, -0.5,  0.5, -0.5,  0.5],
    [-0.5, -0.5,  0.5, -0.5,  0.5, -0.5,  0.5, -0.5],
    [-0.5,  0.5, -0.5,  0.5, -0.5,  0.5, -0.5,  0.5]
  ];
  
  /**
   * Compute auxiliary u_k terms using Hadamard transform
   * u_k = Σ α_{ki} * x_i² where α is Hadamard matrix
   * @param {Array<number>} x8 - 8D vector [x₁..x₈]
   * @returns {Array<number>} - 8 auxiliary terms [u₁..u₈]
   */
  static computeU(x8) {
    if (x8.length !== 8) {
      throw new Error('Hadamard transform requires 8-dimensional vector');
    }
    
    // Compute squares of input components
    const x2 = x8.map(val => val * val);
    
    // Apply Hadamard matrix to squared values
    return this.HADAMARD_8.map(row => 
      row.reduce((sum, α, i) => sum + α * x2[i], 0)
    );
  }
  
  /**
   * Verify Hadamard orthogonality property
   * H * H^T = n * I where n = 8
   * @returns {boolean} - True if orthogonal
   */
  static verifyOrthogonality() {
    const n = 8;
    
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) {
        let dot = 0;
        for (let k = 0; k < n; k++) {
          dot += this.HADAMARD_8[i][k] * this.HADAMARD_8[j][k];
        }
        
        // Should equal n * δ_{ij} (Kronecker delta)
        const expected = (i === j) ? n : 0;
        if (Math.abs(dot - expected) > 1e-10) {
          return false;
        }
      }
    }
    
    return true;
  }
  
  /**
   * Generate Hadamard matrix of order 4^n recursively
   * @param {number} n - Power of 2 (n = 1, 2, 3, ...)
   * @returns {Array<Array<number>>} - Hadamard matrix H_{2^n}
   */
  static generateHadamard(n) {
    if (n === 0) return [[1]];
    if (n === 1) return [[1, 1], [1, -1]];
    
    const prev = this.generateHadamard(n - 1);
    const size = Math.pow(2, n);
    const result = new Array(size);
    
    for (let i = 0; i < size; i++) {
      result[i] = new Array(size);
      const halfSize = size / 2;
      
      for (let j = 0; j < size; j++) {
        if (i < halfSize && j < halfSize) {
          result[i][j] = prev[i][j];
        } else if (i < halfSize && j >= halfSize) {
          result[i][j] = prev[i][j - halfSize];
        } else if (i >= halfSize && j < halfSize) {
          result[i][j] = prev[i - halfSize][j];
        } else {
          result[i][j] = -prev[i - halfSize][j - halfSize];
        }
      }
    }
    
    return result;
  }
  
  /**
   * Scale Hadamard matrix by 1/2 for Pfister identity
   * @param {Array<Array<number>>} H - Hadamard matrix
   * @returns {Array<Array<number>>} - Scaled matrix
   */
  static scaleForPfister(H) {
    return H.map(row => row.map(val => val * 0.5));
  }
  
  /**
   * Verify that rows are orthogonal and have correct length
   * @param {Array<Array<number>>} matrix - Matrix to check
   * @returns {boolean} - True if valid Hadamard
   */
  static isValidHadamard(matrix) {
    const n = matrix.length;
    
    // Check square matrix
    if (!matrix.every(row => row.length === n)) {
      return false;
    }
    
    // Check orthogonality
    for (let i = 0; i < n; i++) {
      for (let j = 0; j < n; j++) {
        let dot = 0;
        for (let k = 0; k < n; k++) {
          dot += matrix[i][k] * matrix[j][k];
        }
        
        const expected = (i === j) ? n : 0;
        if (Math.abs(dot - expected) > 1e-10) {
          return false;
        }
      }
    }
    
    return true;
  }
  
  /**
   * Compute Hadamard transform of a vector
   * @param {Array<number>} vector - Input vector
   * @param {Array<Array<number>>} H - Hadamard matrix
   * @returns {Array<number>} - Transformed vector
   */
  static transform(vector, H) {
    const n = vector.length;
    if (H.length !== n || !H.every(row => row.length === n)) {
      throw new Error('Matrix and vector dimensions must match');
    }
    
    return H.map(row => 
      row.reduce((sum, val, i) => sum + val * vector[i], 0)
    );
  }
  
  /**
   * Get the exact coefficient table for Pfister 16-square
   * @returns {Array<Array<number>>} - Coefficient table α_{ki}
   */
  static getPfisterCoefficients() {
    return this.HADAMARD_8;
  }
  
  /**
   * Verify Pfister auxiliary terms computation
   * @param {Array<number>} x8 - Input 8D vector
   * @param {Array<number>} u8 - Computed auxiliary terms
   * @returns {boolean} - True if u_k = Σ α_{ki} * x_i²
   */
  static verifyAuxiliaryTerms(x8, u8) {
    const x2 = x8.map(val => val * val);
    const expected = this.computeU(x8);
    
    for (let i = 0; i < 8; i++) {
      if (Math.abs(u8[i] - expected[i]) > 1e-10) {
        return false;
      }
    }
    
    return true;
  }
}

module.exports = HadamardMatrix;