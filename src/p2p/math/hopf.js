/**
 * Hopf Fibration System
 * S⁷ → S⁴ projection for quantum-like entanglement
 * 
 * Maps 8D octonion genome to 5D projective ket
 * Preserves mathematical structure while enabling non-local correlation
 */

class HopfFibration {
  /**
   * Project 8D octonion to 5D S⁴ space
   * @param {Array<number>} oct - 8D octonion [z₀..z₇]
   * @returns {Array<number>} - 5D projection [x₀..x₄]
   */
  static project(oct) {
    if (oct.length !== 8) {
      throw new Error('Hopf projection requires 8-dimensional octonion');
    }
    
    const [z0,z1,z2,z3,z4,z5,z6,z7] = oct;
    
    // Hopf fibration: S⁷ → S⁴ with S³ fiber
    const x0 = z0**2 + z1**2 + z2**2 + z3**2 - (z4**2 + z5**2 + z6**2 + z7**2);
    const x1 = 2*(z0*z4 + z1*z5 + z2*z6 + z3*z7);
    const x2 = 2*(-z0*z5 + z1*z4 + z2*z7 - z3*z6);
    const x3 = 2*(-z0*z6 - z1*z7 + z2*z4 + z3*z5);
    const x4 = 2*(-z0*z7 + z1*z6 - z2*z5 + z3*z4);
    
    const vec = [x0, x1, x2, x3, x4];
    const norm = Math.sqrt(vec.reduce((s, v) => s + v**2, 0));
    
    // Normalize to unit sphere S⁴
    return vec.map(v => v / norm);
  }
  
  /**
   * Lift 5D S⁴ point back to 8D with specific S³ fiber
   * @param {Array<number>} s4 - 5D projective point
   * @param {Array<number>} fiber - 4D S³ fiber (optional)
   * @returns {Array<number>} - 8D octonion
   */
  static lift(s4, fiber = null) {
    if (s4.length !== 5) {
      throw new Error('Hopf lift requires 5-dimensional S⁴ point');
    }
    
    const [x0, x1, x2, x3, x4] = s4;
    
    // Default fiber if not provided
    if (!fiber) {
      fiber = [1, 0, 0, 0]; // Identity quaternion
    }
    
    const [q0, q1, q2, q3] = fiber;
    
    // Inverse Hopf map (simplified)
    // This is not unique - many octonions project to same S⁴ point
    const z0 = Math.sqrt((x0 + Math.sqrt(x1**2 + x2**2 + x3**2 + x4**2)) / 2);
    const z1 = q1 * Math.sqrt((x0 - Math.sqrt(x1**2 + x2**2 + x3**2 + x4**2)) / 2);
    const z2 = q2 * Math.sqrt((x0 - Math.sqrt(x1**2 + x2**2 + x3**2 + x4**2)) / 2);
    const z3 = q3 * Math.sqrt((x0 - Math.sqrt(x1**2 + x2**2 + x3**2 + x4**2)) / 2);
    
    // Compute remaining components using constraint equations
    const constraint = Math.sqrt(x0**2 + x1**2 + x2**2 + x3**2 + x4**2);
    const z4 = Math.sqrt(constraint**2 - (z0**2 + z1**2 + z2**2 + z3**2));
    const z5 = Math.sqrt(constraint**2 - (z0**2 + z1**2 + z2**2 + z3**2 + z4**2));
    const z6 = Math.sqrt(constraint**2 - (z0**2 + z1**2 + z2**2 + z3**2 + z4**2 + z5**2));
    const z7 = Math.sqrt(constraint**2 - (z0**2 + z1**2 + z2**2 + z3**2 + z4**2 + z5**2 + z6**2));
    
    return [z0, z1, z2, z3, z4, z5, z6, z7];
  }
  
  /**
   * Compute correlation between two S⁴ projections
   * @param {Array<number>} s4a - First 5D projection
   * @param {Array<number>} s4b - Second 5D projection
   * @returns {number} - Correlation coefficient (-1 to 1)
   */
  static correlation(s4a, s4b) {
    if (s4a.length !== 5 || s4b.length !== 5) {
      throw new Error('Correlation requires 5-dimensional S⁴ points');
    }
    
    // Compute dot product
    const dot = s4a.reduce((sum, val, i) => sum + val * s4b[i], 0);
    
    // Both are unit vectors, so dot product equals correlation
    return Math.max(-1, Math.min(1, dot));
  }
  
  /**
   * Compute distance on S⁴ manifold
   * @param {Array<number>} s4a - First 5D point
   * @param {Array<number>} s4b - Second 5D point
   * @returns {number} - Geodesic distance
   */
  static distance(s4a, s4b) {
    const corr = this.correlation(s4a, s4b);
    
    // For unit sphere, distance = arccos(correlation)
    return Math.acos(Math.max(-1, Math.min(1, corr)));
  }
  
  /**
   * Interpolate between two S⁴ points
   * @param {Array<number>} s4a - First point
   * @param {Array<number>} s4b - Second point
   * @param {number} t - Interpolation parameter (0-1)
   * @returns {Array<number>} - Interpolated point
   */
  static interpolate(s4a, s4b, t) {
    if (s4a.length !== 5 || s4b.length !== 5) {
      throw new Error('Interpolation requires 5-dimensional S⁴ points');
    }
    
    // Spherical linear interpolation (SLERP)
    const angle = this.distance(s4a, s4b);
    const sinAngle = Math.sin(angle);
    
    if (Math.abs(sinAngle) < 1e-10) {
      // Points are very close, use linear interpolation
      return s4a.map((val, i) => 
        val * (1 - t) + s4b[i] * t
      );
    }
    
    // SLERP formula
    const factor1 = Math.sin((1 - t) * angle) / sinAngle;
    const factor2 = Math.sin(t * angle) / sinAngle;
    
    return s4a.map((val, i) => 
      factor1 * val + factor2 * s4b[i]
    );
  }
  
  /**
   * Generate random point on S⁴
   * @returns {Array<number>} - Random 5D unit vector
   */
  static randomS4() {
    const vec = new Array(5);
    for (let i = 0; i < 5; i++) {
      vec[i] = (Math.random() - 0.5) * 2;
    }
    
    // Normalize to unit sphere
    const norm = Math.sqrt(vec.reduce((s, v) => s + v**2, 0));
    return vec.map(v => v / norm);
  }
  
  /**
   * Verify that a point lies on S⁴
   * @param {Array<number>} s4 - 5D point to check
   * @returns {boolean} - True if on unit sphere
   */
  static isOnS4(s4) {
    if (s4.length !== 5) {
      return false;
    }
    
    const norm = s4.reduce((sum, val) => sum + val**2, 0);
    return Math.abs(norm - 1.0) < 1e-10;
  }
  
  /**
   * Compute tangent space at point on S⁴
   * @param {Array<number>} s4 - 5D point
   * @returns {Array<Array<number>>} - 4×4 tangent basis
   */
  static tangentSpace(s4) {
    if (s4.length !== 5) {
      throw new Error('Tangent space requires 5-dimensional point');
    }
    
    // Gram-Schmidt process to find orthonormal basis
    const tangent = [];
    
    for (let i = 0; i < 4; i++) {
      const basis = new Array(5).fill(0);
      basis[i] = 1;
      
      // Orthogonalize against previous vectors
      for (let j = 0; j < tangent.length; j++) {
        const dot = basis.reduce((sum, val, k) => sum + val * tangent[j][k], 0);
        const proj = tangent[j].map(val => val * dot);
        basis = basis.map((val, k) => val - proj[k]);
      }
      
      // Normalize
      const norm = Math.sqrt(basis.reduce((s, v) => s + v**2, 0));
      tangent.push(basis.map(v => v / norm));
    }
    
    return tangent;
  }
}

module.exports = HopfFibration;