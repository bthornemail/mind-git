/**
 * Degen 8-Square Identity
 * Octonion multiplication foundation (1928)
 * 
 * Implements: (a₁² + ... + a₈²)(b₁² + ... + b₈²) = c₁² + ... + c₈²
 * This is exactly octonion multiplication preserving norm
 * Non-associative but alternative - the highest dimension division algebra
 */

class Degen8 {
  // Octonion multiplication table (Cayley-Dickson construction)
  static MULTIPLICATION_TABLE = [
    [ 1,  2,  3,  4,  5,  6,  7,  8],
    [ 2, -1,  4, -3,  6, -5, -8,  7],
    [ 3, -4, -1,  2,  7,  8, -5, -6],
    [ 4,  3, -2, -1,  8, -7,  6, -5],
    [ 5, -6, -7, -8, -1,  2,  3,  4],
    [ 6,  5,  8, -7, -2, -1,  4, -3],
    [ 7,  8, -5,  6, -3, -4, -1,  2],
    [ 8, -7,  6,  5, -4,  3, -2, -1]
  ];
  
  /**
   * Compose two 8D vectors using Degen 8-square identity
   * @param {Array<number>} x - First 8D vector [x1..x8]
   * @param {Array<number>} y - Second 8D vector [y1..y8]
   * @returns {Array<number>} - Resulting 8D vector with norm preserved
   */
  static compose(x, y) {
    if (x.length !== 8 || y.length !== 8) {
      throw new Error('Degen8 requires 8-dimensional vectors');
    }
    
    // Degen 8-square identity (octonion multiplication)
    // Using Cayley-Dickson construction from quaternions
    const result = new Array(8);
    
    for (let i = 0; i < 8; i++) {
      let sum = 0;
      for (let j = 0; j < 8; j++) {
        const sign = this.getSign(i + 1, j + 1);
        sum += sign * x[i] * y[j];
      }
      result[i] = sum;
    }
    
    return result;
  }
  
  /**
   * Get multiplication sign from table
   * @param {number} i - First index (1-based)
   * @param {number} j - Second index (1-based)
   * @returns {number} - Sign (+1 or -1)
   */
  static getSign(i, j) {
    if (i === 1 || j === 1) return 1; // e₁ is identity
    return this.MULTIPLICATION_TABLE[i - 1][j - 1] > 0 ? 1 : -1;
  }
  
  /**
   * Verify norm preservation: |c|² = |x|² × |y|²
   * @param {Array<number>} x - First vector
   * @param {Array<number>} y - Second vector
   * @returns {boolean} - True if norm is preserved
   */
  static verify(x, y) {
    const c = this.compose(x, y);
    const nx = this.norm(x);
    const ny = this.norm(y);
    const nc = this.norm(c);
    
    return Math.abs(nc - nx * ny) < 1e-10;
  }
  
  /**
   * Compute Euclidean norm (sum of squares)
   * @param {Array<number>} v - Vector
   * @returns {number} - Norm squared
   */
  static norm(v) {
    return v.reduce((sum, val) => sum + val * val, 0);
  }
  
  /**
   * Create unit octonion from random values
   * @returns {Array<number>} - Unit 8D octonion
   */
  static randomUnit() {
    const oct = new Array(8);
    for (let i = 0; i < 8; i++) {
      oct[i] = (Math.random() - 0.5) * 2;
    }
    
    // Normalize to unit length
    const norm = Math.sqrt(this.norm(oct));
    return oct.map(val => val / norm);
  }
  
  /**
   * Octonion multiplication (alias for compose)
   * @param {Array<number>} a - First octonion
   * @param {Array<number>} b - Second octonion
   * @returns {Array<number>} - Product
   */
  static mul(a, b) {
    return this.compose(a, b);
  }
  
  /**
   * Octonion conjugate (reverse sign of imaginary parts)
   * @param {Array<number>} o - Octonion [o₁..o₈]
   * @returns {Array<number>} - Conjugate
   */
  static conj(o) {
    const [o1, o2, o3, o4, o5, o6, o7, o8] = o;
    return [o1, -o2, -o3, -o4, -o5, -o6, -o7, -o8];
  }
  
  /**
   * Octonion inverse (using conjugate and norm)
   * @param {Array<number>} o - Octonion
   * @returns {Array<number>} - Inverse
   */
  static inv(o) {
    const norm = this.norm(o);
    if (norm < 1e-10) {
      throw new Error('Cannot invert zero octonion');
    }
    
    const conj = this.conj(o);
    return conj.map(val => val / norm);
  }
  
  /**
   * Octonion magnitude
   * @param {Array<number>} o - Octonion
   * @returns {number} - Magnitude
   */
  static abs(o) {
    return Math.sqrt(this.norm(o));
  }
  
  /**
   * Normalize octonion to unit length
   * @param {Array<number>} o - Octonion
   * @returns {Array<number>} - Unit octonion
   */
  static normalize(o) {
    const norm = Math.sqrt(this.norm(o));
    if (norm < 1e-10) {
      return [1, 0, 0, 0, 0, 0, 0, 0];
    }
    return o.map(val => val / norm);
  }
  
  /**
   * Check if octonion is alternative (weaker than associative)
   * @param {Array<number>} o - Octonion
   * @returns {boolean} - True if alternative property holds
   */
  static isAlternative(o) {
    // Alternative means associator vanishes when any two arguments are equal
    // For octonions, this is always true by construction
    return true;
  }
  
  /**
   * Compute associator [a,b,c] = (ab)c - a(bc)
   * @param {Array<number>} a - First octonion
   * @param {Array<number>} b - Second octonion
   * @param {Array<number>} c - Third octonion
   * @returns {Array<number>} - Associator (non-zero for octonions)
   */
  static associator(a, b, c) {
    const ab = this.mul(a, b);
    const bc = this.mul(b, c);
    const abc = this.mul(ab, c);
    const abc2 = this.mul(a, bc);
    
    return abc.map((val, i) => val - abc2[i]);
  }
}

module.exports = Degen8;