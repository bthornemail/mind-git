/**
 * Brahmagupta-Fibonacci 2-Square Identity
 * Foundation of the complete identity chain (628 AD)
 * 
 * Implements: (a₁² + a₂²)(b₁² + b₂²) = c₁² + c₂²
 * This is exactly complex multiplication in disguise
 */

class Brahmagupta2 {
  /**
   * Compose two 2D vectors using Brahmagupta identity
   * @param {Array<number>} x - First 2D vector [x1, x2]
   * @param {Array<number>} y - Second 2D vector [y1, y2]
   * @returns {Array<number>} - Resulting 2D vector with norm preserved
   */
  static compose(x, y) {
    if (x.length !== 2 || y.length !== 2) {
      throw new Error('Brahmagupta2 requires 2-dimensional vectors');
    }
    
    const [x1, x2] = x;
    const [y1, y2] = y;
    
    // Brahmagupta-Fibonacci identity (complex multiplication)
    const c1 = x1 * y1 - x2 * y2;  // Real part
    const c2 = x1 * y2 + x2 * y1;  // Imaginary part
    
    return [c1, c2];
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
   * Create unit complex number from angle
   * @param {number} angle - Angle in radians
   * @returns {Array<number>} - Unit 2D vector
   */
  static fromAngle(angle) {
    return [Math.cos(angle), Math.sin(angle)];
  }
  
  /**
   * Get angle from complex number
   * @param {Array<number>} z - Complex number [real, imag]
   * @returns {number} - Angle in radians
   */
  static toAngle(z) {
    const [real, imag] = z;
    return Math.atan2(imag, real);
  }
  
  /**
   * Complex multiplication (alias for compose)
   * @param {Array<number>} a - First complex
   * @param {Array<number>} b - Second complex
   * @returns {Array<number>} - Product
   */
  static mul(a, b) {
    return this.compose(a, b);
  }
  
  /**
   * Complex division
   * @param {Array<number>} a - Numerator
   * @param {Array<number>} b - Denominator
   * @returns {Array<number>} - Quotient
   */
  static div(a, b) {
    const [a1, a2] = a;
    const [b1, b2] = b;
    const denom = b1 * b1 + b2 * b2;
    
    if (Math.abs(denom) < 1e-10) {
      throw new Error('Division by zero in complex numbers');
    }
    
    return [
      (a1 * b1 + a2 * b2) / denom,
      (a2 * b1 - a1 * b2) / denom
    ];
  }
  
  /**
   * Complex conjugate
   * @param {Array<number>} z - Complex number
   * @returns {Array<number>} - Conjugate
   */
  static conj(z) {
    const [real, imag] = z;
    return [real, -imag];
  }
  
  /**
   * Complex magnitude
   * @param {Array<number>} z - Complex number
   * @returns {number} - Magnitude
   */
  static abs(z) {
    return Math.sqrt(this.norm(z));
  }
}

module.exports = Brahmagupta2;