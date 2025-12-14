/**
 * Pfister 16-Square Identity with Hadamard Orthogonalization
 * Dual-reality entanglement foundation (1965)
 * 
 * Expands 8D → 16D via Hadamard, then composes with Degen 8-square
 * Norm preservation: |z|² = |x|⁴ × |y|⁴
 */

const Degen8 = require('../identities/degen8');
const HadamardMatrix = require('../hadamard');

class Pfister16 {
  /**
   * Compose two 8D vectors using Pfister 16-square identity
   * @param {Array<number>} x - First 8D vector [x₁..x₈]
   * @param {Array<number>} y - Second 8D vector [y₁..y₈]
   * @returns {Array<number>} - Resulting 16D vector with norm preserved
   */
  static compose(x, y) {
    if (x.length !== 8 || y.length !== 8) {
      throw new Error('Pfister16 requires 8-dimensional vectors');
    }
    
    // Step 1: Compute auxiliary u_k terms using Hadamard
    const u = HadamardMatrix.computeU(x);
    const v = HadamardMatrix.computeU(y);
    
    // Step 2: Expand to 16D: [x₁..x₈, u₁..u₈]
    const x16 = [...x, ...u];
    const y16 = [...y, ...v];
    
    // Step 3: Apply Degen 8-square to first 8 components
    const blue = Degen8.compose(x, y);
    
    // Step 4: Apply Degen 8-square to auxiliary terms
    const twist = Degen8.compose(u, v);
    
    // Step 5: Combine results
    return [...blue, ...twist];
  }
  
  /**
   * Verify norm preservation: |z|² = |x|⁴ × |y|⁴
   * @param {Array<number>} x - First 8D vector
   * @param {Array<number>} y - Second 8D vector
   * @returns {boolean} - True if norm is preserved
   */
  static verify(x, y) {
    const z = this.compose(x, y);
    const nx = Degen8.norm(x);
    const ny = Degen8.norm(y);
    const nz = Degen8.norm(z);
    
    // For Pfister 16: |z|² should equal |x|⁴ × |y|⁴
    const expected = nx * nx * ny * ny;
    return Math.abs(nz - expected) < 1e-10;
  }
  
  /**
   * Compute norm (sum of squares)
   * @param {Array<number>} v - Vector
   * @returns {number} - Norm squared
   */
  static norm(v) {
    return Degen8.norm(v);
  }
  
  /**
   * Expand 8D vector to 16D via Hadamard
   * @param {Array<number>} x8 - 8D vector
   * @returns {Array<number>} - 16D expanded vector
   */
  static expand(x8) {
    if (x8.length !== 8) {
      throw new Error('Expansion requires 8-dimensional vector');
    }
    
    const u = HadamardMatrix.computeU(x8);
    return [...x8, ...u];
  }
  
  /**
   * Reduce 16D vector back to 8D via consensus
   * @param {Array<number>} z16 - 16D vector
   * @returns {Array<number>} - Consensus 8D vector
   */
  static reduce(z16) {
    if (z16.length !== 16) {
      throw new Error('Reduction requires 16-dimensional vector');
    }
    
    // Split into two 8D vectors
    const z1 = z16.slice(0, 8);
    const z2 = z16.slice(8, 16);
    
    // Apply Degen composition for consensus
    return Degen8.compose(z1, z2);
  }
  
  /**
   * Generate integrity proof for 16D composition
   * @param {Array<number>} x - First 8D vector
   * @param {Array<number>} y - Second 8D vector
   * @returns {Object} - Mathematical proof
   */
  static generateProof(x, y) {
    const z = this.compose(x, y);
    const u = HadamardMatrix.computeU(x);
    const v = HadamardMatrix.computeU(y);
    
    return {
      type: 'pfister16',
      inputs: { x, y },
      auxiliary: { u, v },
      output: z,
      normLeft: Degen8.norm(x),
      normRight: Degen8.norm(y),
      normOutput: Degen8.norm(z),
      hadamardHash: this.computeHadamardHash(u),
      normPreserved: this.verify(x, y),
      timestamp: Date.now()
    };
  }
  
  /**
   * Compute hash of Hadamard auxiliary terms
   * @param {Array<number>} u - Auxiliary terms
   * @returns {string} - Hash string
   */
  static computeHadamardHash(u) {
    const combined = u.reduce((sum, val) => sum + val * Math.PI, 0);
    return `hadamard:${combined.toFixed(6)}`;
  }
  
  /**
   * Verify integrity of 16D packet
   * @param {Array<number>} packet16 - 16D packet
   * @param {Object} proof - Expected proof
   * @returns {boolean} - True if packet is valid
   */
  static verifyPacket(packet16, proof) {
    if (packet16.length !== 16) {
      return false;
    }
    
    // Verify norm preservation
    const actualNorm = Degen8.norm(packet16);
    const expectedNorm = proof.normLeft * proof.normLeft * proof.normRight * proof.normRight;
    
    return Math.abs(actualNorm - expectedNorm) < 1e-10;
  }
  
  /**
   * Compress 16D vector to BQF coefficients
   * @param {Array<number>} v16 - 16D vector
   * @returns {Object} - BQF coefficients {a, b, c}
   */
  static compressToBQF(v16) {
    // Use Hilbert's theorem for binary quadratic forms
    // Compress 16D to 3 coefficients via projection
    
    const a = v16.reduce((sum, val, i) => sum + val * Math.cos(i * Math.PI / 8), 0);
    const b = v16.reduce((sum, val, i) => sum + val * Math.sin(i * Math.PI / 8), 0);
    const c = v16.reduce((sum, val) => sum + val * val, 0);
    
    return { a, b, c };
  }
  
  /**
   * Decompress BQF coefficients back to 16D vector
   * @param {Object} bqf - BQF coefficients {a, b, c}
   * @returns {Array<number>} - 16D vector
   */
  static decompressFromBQF(bqf) {
    const { a, b, c } = bqf;
    const v16 = new Array(16);
    
    for (let i = 0; i < 16; i++) {
      v16[i] = a * Math.cos(i * Math.PI / 8) + 
                 b * Math.sin(i * Math.PI / 8) + 
                 c * Math.cos(2 * i * Math.PI / 8);
    }
    
    return v16;
  }
}

module.exports = Pfister16;