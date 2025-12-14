/**
 * Euler 4-Square Identity
 * Quaternion multiplication foundation (1748)
 * 
 * Implements: (a₁² + a₂² + a₃² + a₄²)(b₁² + b₂² + b₃² + b₄²) = c₁² + c₂² + c₃² + c₄²
 * This is exactly quaternion multiplication preserving norm
 */

class Euler4 {
  /**
   * Compose two 4D vectors using Euler 4-square identity
   * @param {Array<number>} x - First 4D vector [x1, x2, x3, x4]
   * @param {Array<number>} y - Second 4D vector [y1, y2, y3, y4]
   * @returns {Array<number>} - Resulting 4D vector with norm preserved
   */
  static compose(x, y) {
    if (x.length !== 4 || y.length !== 4) {
      throw new Error('Euler4 requires 4-dimensional vectors');
    }
    
    const [x1, x2, x3, x4] = x;
    const [y1, y2, y3, y4] = y;
    
    // Euler 4-square identity (quaternion multiplication)
    // Treat as quaternion: x = x1 + x2*i + x3*j + x4*k
    const c1 = x1 * y1 - x2 * y2 - x3 * y3 - x4 * y4;  // Scalar part
    const c2 = x1 * y2 + x2 * y1 + x3 * y4 - x4 * y3;  // i component
    const c3 = x1 * y3 - x2 * y4 + x3 * y1 + x4 * y2;  // j component
    const c4 = x1 * y4 + x2 * y3 - x3 * y2 + x4 * y1;  // k component
    
    return [c1, c2, c3, c4];
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
   * Create unit quaternion from axis-angle
   * @param {Array<number>} axis - 3D axis vector [x, y, z]
   * @param {number} angle - Angle in radians
   * @returns {Array<number>} - Unit 4D quaternion
   */
  static fromAxisAngle(axis, angle) {
    const [ax, ay, az] = axis;
    const norm = Math.sqrt(ax * ax + ay * ay + az * az);
    
    if (norm < 1e-10) {
      return [1, 0, 0, 0]; // Identity quaternion
    }
    
    const halfAngle = angle * 0.5;
    const sinHalf = Math.sin(halfAngle);
    const cosHalf = Math.cos(halfAngle);
    
    return [
      cosHalf,
      (ax / norm) * sinHalf,
      (ay / norm) * sinHalf,
      (az / norm) * sinHalf
    ];
  }
  
  /**
   * Quaternion multiplication (alias for compose)
   * @param {Array<number>} a - First quaternion
   * @param {Array<number>} b - Second quaternion
   * @returns {Array<number>} - Product
   */
  static mul(a, b) {
    return this.compose(a, b);
  }
  
  /**
   * Quaternion conjugate
   * @param {Array<number>} q - Quaternion [w, x, y, z]
   * @returns {Array<number>} - Conjugate
   */
  static conj(q) {
    const [w, x, y, z] = q;
    return [w, -x, -y, -z];
  }
  
  /**
   * Quaternion inverse
   * @param {Array<number>} q - Quaternion
   * @returns {Array<number>} - Inverse
   */
  static inv(q) {
    const norm = this.norm(q);
    if (norm < 1e-10) {
      throw new Error('Cannot invert zero quaternion');
    }
    
    const conj = this.conj(q);
    return conj.map(val => val / norm);
  }
  
  /**
   * Quaternion magnitude
   * @param {Array<number>} q - Quaternion
   * @returns {number} - Magnitude
   */
  static abs(q) {
    return Math.sqrt(this.norm(q));
  }
  
  /**
   * Normalize quaternion to unit length
   * @param {Array<number>} q - Quaternion
   * @returns {Array<number>} - Unit quaternion
   */
  static normalize(q) {
    const norm = Math.sqrt(this.norm(q));
    if (norm < 1e-10) {
      return [1, 0, 0, 0];
    }
    return q.map(val => val / norm);
  }
  
  /**
   * Extract rotation matrix from quaternion
   * @param {Array<number>} q - Unit quaternion [w, x, y, z]
   * @returns {Array<Array<number>>} - 3x3 rotation matrix
   */
  static toRotationMatrix(q) {
    const [w, x, y, z] = q;
    
    return [
      [1 - 2*(y*y + z*z), 2*(x*y - w*z), 2*(x*z + w*y)],
      [2*(x*y + w*z), 1 - 2*(x*x + z*z), 2*(y*z - w*x)],
      [2*(x*z - w*y), 2*(y*z + w*x), 1 - 2*(x*x + y*y)]
    ];
  }
}

module.exports = Euler4;