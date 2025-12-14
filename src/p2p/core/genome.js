/**
 * Octonion Genome System
 * Core reality primitive for CanvasL P2P metaverse
 * 
 * Every agent/reality is defined by unit octonion on S⁷
 * With projective S⁴ ket and S³ phase fiber
 */

const Degen8 = require('../math/identities/degen8.js');
const HopfFibration = require('../math/hopf.js');
const BQFCompression = require('../math/bqf.js');

class OctonionGenome {
  /**
   * Create new octonion genome
   * @param {string} id - Unique reality identifier
   * @param {Array<number>} genome - Optional 8D octonion (random if not provided)
   */
  constructor(id, genome = null) {
    this.id = id;
    this.genome = genome || Degen8.randomUnit();
    this.s4_ket = HopfFibration.project(this.genome);
    this.s3_fiber = this.generateFiber();
    this.bqf = BQFCompression.compress(this.genome);
    this.fitness = 0;
    this.entanglements = new Map();
    this.lastUpdate = Date.now();
    this.mutationRate = 0.01;
    
    // Verify genome integrity
    this.verifyIntegrity();
  }
  
  /**
   * Generate S³ phase fiber
   * @returns {Array<number>} - 4D quaternion fiber
   */
  generateFiber() {
    return [
      Math.random() * 2 - 1,  // q₀
      Math.random() * 2 - 1,  // q₁
      Math.random() * 2 - 1,  // q₂
      Math.random() * 2 - 1   // q₃
    ];
  }
  
  /**
   * Verify genome mathematical integrity
   * @returns {boolean} - True if genome is valid
   */
  verifyIntegrity() {
    // Check unit norm
    const norm = Math.sqrt(Degen8.norm(this.genome));
    if (Math.abs(norm - 1.0) > 1e-10) {
      throw new Error(`Genome ${this.id} not unit length: ${norm}`);
    }
    
    // Check BQF compression consistency
    const decompressed = BQFCompression.decompress(this.bqf);
    for (let i = 0; i < 8; i++) {
      if (Math.abs(decompressed[i] - this.genome[i]) > 1e-6) {
        throw new Error(`BQF compression error for genome ${this.id}`);
      }
    }
    
    return true;
  }
  
  /**
   * Mutate genome using Gaussian perturbation
   * @param {number} rate - Mutation rate (default: 0.01)
   */
  mutate(rate = this.mutationRate) {
    const oldGenome = [...this.genome];
    
    // Apply Gaussian mutation in octonion space
    this.genome = this.genome.map((z, i) => 
      z + rate * this.gaussianRandom() * Math.cos(i * Math.PI / 8)
    );
    
    // Renormalize to unit octonion (stay on S⁷)
    const norm = Math.sqrt(Degen8.norm(this.genome));
    this.genome = this.genome.map(v => v / norm);
    
    // Update derived properties
    this.s4_ket = HopfFibration.project(this.genome);
    this.bqf = BQFCompression.compress(this.genome);
    this.lastUpdate = Date.now();
    
    // Compute fitness change
    const fitnessChange = this.computeFitness() - this.fitness;
    this.fitness += fitnessChange;
    
    return {
      oldGenome,
      newGenome: this.genome,
      fitnessChange,
      mutationRate: rate
    };
  }
  
  /**
   * Generate Gaussian random number
   * @returns {number} - Gaussian random (μ=0, σ=1)
   */
  gaussianRandom() {
    // Box-Muller transform
    const u1 = Math.random();
    const u2 = Math.random();
    while (u1 === 0) u1 = Math.random();
    while (u2 === 0) u2 = Math.random();
    
    const z0 = Math.sqrt(-2 * Math.log(u1)) * Math.cos(2 * Math.PI * u2);
    const z1 = Math.sqrt(-2 * Math.log(u1)) * Math.sin(2 * Math.PI * u2);
    
    return z0;
  }
  
  /**
   * Compute fitness based on entanglement correlations
   * @returns {number} - Fitness score
   */
  computeFitness() {
    if (this.entanglements.size === 0) {
      return 0.5; // Neutral fitness
    }
    
    let totalCorr = 0;
    let count = 0;
    
    // Average correlation with all entangled peers
    for (const [peerId, ket] of this.entanglements) {
      const correlation = HopfFibration.correlation(this.s4_ket, ket);
      totalCorr += correlation;
      count++;
    }
    
    return count > 0 ? totalCorr / count : 0.5;
  }
  
  /**
   * Entangle with another reality
   * @param {OctonionGenome} peer - Another reality to entangle with
   * @returns {Object} - Entanglement result
   */
  entangleWith(peer) {
    if (!(peer instanceof OctonionGenome)) {
      throw new Error('Can only entangle with OctonionGenome instances');
    }
    
    // Compute shared ket via projective linking
    const sharedKet = this.computeSharedKet(this.s4_ket, peer.s4_ket);
    
    // Store entanglement
    this.entanglements.set(peer.id, sharedKet);
    peer.entanglements.set(this.id, sharedKet);
    
    // Update fitness
    this.fitness = this.computeFitness();
    peer.fitness = peer.computeFitness();
    
    return {
      id: `${this.id}_${peer.id}`,
      realityA: this.id,
      realityB: peer.id,
      sharedKet,
      correlation: HopfFibration.correlation(this.s4_ket, peer.s4_ket),
      timestamp: Date.now(),
      bqf: BQFCompression.compress(this.genome),
      peerBQF: BQFCompression.compress(peer.genome)
    };
  }
  
  /**
   * Compute shared ket between two S⁴ projections
   * @param {Array<number>} ketA - First ket
   * @param {Array<number>} ketB - Second ket
   * @returns {Array<number>} - Shared ket
   */
  computeSharedKet(ketA, ketB) {
    // Bilinear "entanglement" map
    const linked = [];
    
    for (let i = 0; i < 5; i++) {
      linked.push(ketA[i] * ketB[i]);
    }
    
    // Normalize to projective point
    const norm = Math.sqrt(linked.reduce((s, v) => s + v**2, 0));
    return linked.map(v => v / norm);
  }
  
  /**
   * Update genome from entanglement
   * @param {Array<number>} sharedKet - Shared ket state
   * @param {number} weight - Blending weight (0-1)
   */
  updateFromEntanglement(sharedKet, weight = 0.7) {
    // Lift shared ket back to S⁷
    const liftedGenome = HopfFibration.lift(sharedKet, this.s3_fiber);
    
    // Blend with current genome
    this.genome = this.genome.map((v, i) => 
      v * (1 - weight) + liftedGenome[i] * weight
    );
    
    // Renormalize
    const norm = Math.sqrt(Degen8.norm(this.genome));
    this.genome = this.genome.map(v => v / norm);
    
    // Update derived properties
    this.s4_ket = HopfFibration.project(this.genome);
    this.bqf = BQFCompression.compress(this.genome);
    this.lastUpdate = Date.now();
    this.fitness = this.computeFitness();
  }
  
  /**
   * Serialize genome for network transmission
   * @returns {ArrayBuffer} - Serialized genome (12 bytes)
   */
  serialize() {
    return BQFCompression.serialize(this.bqf);
  }
  
  /**
   * Deserialize genome from network data
   * @param {ArrayBuffer} data - Serialized genome
   * @returns {OctonionGenome} - New genome instance
   */
  static deserialize(data) {
    const bqf = BQFCompression.deserialize(data);
    const genome = BQFCompression.decompress(bqf);
    
    const id = `genome_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
    return new OctonionGenome(id, genome);
  }
  
  /**
   * Clone genome
   * @returns {OctonionGenome} - Clone of this genome
   */
  clone() {
    const cloned = new OctonionGenome(`${this.id}_clone`, [...this.genome]);
    cloned.s3_fiber = [...this.s3_fiber];
    cloned.fitness = this.fitness;
    cloned.mutationRate = this.mutationRate;
    
    return cloned;
  }
  
  /**
   * Get genome statistics
   * @returns {Object} - Statistics object
   */
  getStats() {
    return {
      id: this.id,
      norm: Math.sqrt(Degen8.norm(this.genome)),
      fitness: this.fitness,
      entanglements: this.entanglements.size,
      lastUpdate: this.lastUpdate,
      mutationRate: this.mutationRate,
      bqf: this.bqf,
      s4_ket: this.s4_ket,
      integrity: this.verifyIntegrity()
    };
  }
  
  /**
   * Reset genome to random state
   */
  reset() {
    this.genome = Degen8.randomUnit();
    this.s4_ket = HopfFibration.project(this.genome);
    this.s3_fiber = this.generateFiber();
    this.bqf = BQFCompression.compress(this.genome);
    this.fitness = 0.5;
    this.entanglements.clear();
    this.lastUpdate = Date.now();
  }
}

module.exports = OctonionGenome;