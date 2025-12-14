/**
 * Projective Ket Linking Protocol
 * P2P projective-to-projective space mapping
 * Links two realities like quantum ket entanglement
 */

const OctonionGenome = require('../core/genome');
const HopfFibration = require('../math/hopf.js');
const BQFCompression = require('../math/bqf.js');

class ProjectiveKetLinker {
  constructor(myReality) {
    this.myReality = myReality;
    this.peers = new Map();  // peerId → {proj: S⁴, ket: sharedKet}
    this.sharedKets = new Map();  // peerId → linked ket (projective point)
    
    // P2P setup (using WebRTC or libp2p)
    this.p2p = null;  // Will be set externally
    this.linkHistory = new Map();  // peerId → [timestamps...]
    
    console.log(`🔗 Projective P2P Linker initialized for reality: ${myReality.id}`);
  }
  
  /**
   * Set P2P network instance
   * @param {Object} p2p - P2P network instance
   */
  setP2PNetwork(p2p) {
    this.p2p = p2p;
    
    // Register packet handlers
    p2p.on('peer:connected', (peer) => {
      this.onPeerConnect(peer.id);
    });
    
    p2p.on('peer:disconnected', (peer) => {
      this.onPeerDisconnect(peer.id);
    });
    
    p2p.on('ket:received', (data, peerId) => {
      this.onReceiveKet(data, peerId);
    });
  }
  
  /**
   * Hopf projection: 8D → 5D (S⁴)
   * @param {Array<number>} oct - 8D octonion
   * @returns {Array<number>} - 5D projective point
   */
  hopfProject(oct) {
    return HopfFibration.project(oct);
  }
  
  /**
   * Link two projectives like entangled ket
   * @param {Array<number>} projA - First S⁴ point
   * @param {Array<number>} projB - Second S⁴ point
   * @returns {Array<number>} - Linked ket (projective point)
   */
  linkWithPeer(peerId, peerProj) {
    const myProj = this.myReality.s4_ket;
    
    // Bilinear "entanglement" map (Pfister-safe in outer product space)
    const linked = this.bilinearLink(myProj, peerProj);
    
    // Normalize to projective point
    const norm = Math.sqrt(linked.reduce((s, v) => s + v**2, 0));
    const projKet = linked.map(v => v / norm);
    
    // Store shared ket
    this.sharedKets.set(peerId, projKet);
    
    // Update link history
    if (!this.linkHistory.has(peerId)) {
      this.linkHistory.set(peerId, []);
    }
    this.linkHistory.get(peerId).push(Date.now());
    
    // Update local reality (inverse Hopf lift)
    this.updateLocalReality(projKet);
    
    console.log(`🔗 Linked with ${peerId}: shared ket correlation ${this.computeCorrelation(myProj, projKet).toFixed(3)}`);
    
    return projKet;
  }
  
  /**
   * Bilinear map: S⁴ × S⁴ → ℝ⁵ (then project)
   * @param {Array<number>} p1 - First S⁴ point
   * @param {Array<number>} p2 - Second S⁴ point
   * @returns {Array<number>} - 5D linked vector
   */
  bilinearLink(p1, p2) {
    // Outer product inspired (5×5 matrix flattened)
    const linked = [];
    for (let i = 0; i < 5; i++) {
      for (let j = 0; j < 5; j++) {
        linked.push(p1[i] * p2[j]);
      }
    }
    
    // Take only first 5 for simplicity (can be extended to 25)
    return linked.slice(0, 5);
  }
  
  /**
   * Handle peer connection
   * @param {string} peerId - Peer identifier
   */
  onPeerConnect(peerId) {
    console.log(`🤝 Connected to peer: ${peerId}`);
    
    // Send my projective state
    this.sendProjectiveState(peerId);
  }
  
  /**
   * Handle peer disconnection
   * @param {string} peerId - Peer identifier
   */
  onPeerDisconnect(peerId) {
    console.log(`👋 Disconnected from peer: ${peerId}`);
    
    // Clean up peer data
    this.peers.delete(peerId);
    this.sharedKets.delete(peerId);
    this.linkHistory.delete(peerId);
  }
  
  /**
   * Handle received ket from peer
   * @param {Object} data - Ket data
   * @param {string} peerId - Source peer ID
   */
  onReceiveKet(data, peerId) {
    try {
      if (data.type !== 'proj_state') {
        return;
      }
      
      const peerProj = data.proj;
      this.peers.set(peerId, { proj: peerProj });
      
      // Create entanglement
      const linkedKet = this.linkWithPeer(peerId, peerProj);
      
      // Send back my linked ket
      this.sendKet(peerId, linkedKet);
      
    } catch (error) {
      console.error(`Error processing ket from ${peerId}:`, error);
    }
  }
  
  /**
   * Send projective state to peer
   * @param {string} peerId - Target peer ID
   */
  sendProjectiveState(peerId) {
    if (!this.p2p) return;
    
    const packet = {
      type: 'proj_state',
      proj: this.myReality.s4_ket,
      timestamp: Date.now(),
      sourceId: this.myReality.id
    };
    
    this.p2p.sendToPeer(peerId, packet);
  }
  
  /**
   * Send ket to peer
   * @param {string} peerId - Target peer ID
   * @param {Array<number>} ket - Ket to send
   */
  sendKet(peerId, ket) {
    if (!this.p2p) return;
    
    const packet = {
      type: 'shared_ket',
      ket,
      timestamp: Date.now(),
      sourceId: this.myReality.id
    };
    
    this.p2p.sendToPeer(peerId, packet);
  }
  
  /**
   * Update local reality from linked ket
   * @param {Array<number>} sharedKet - Shared projective ket
   */
  updateLocalReality(sharedKet) {
    // Inverse Hopf lift with random S³ fiber
    const fiber = this.generateRandomFiber();
    const liftedGenome = HopfFibration.lift(sharedKet, fiber);
    
    // Blend with current genome (weighted evolution)
    const blendWeight = 0.7; // 70% new, 30% old
    const oldGenome = this.myReality.genome;
    
    this.myReality.genome = oldGenome.map((v, i) => 
      v * (1 - blendWeight) + liftedGenome[i] * blendWeight
    );
    
    // Renormalize to unit octonion
    const norm = Math.sqrt(this.myReality.genome.reduce((s, v) => s + v**2, 0));
    this.myReality.genome = this.myReality.genome.map(v => v / norm);
    
    // Update derived properties
    this.myReality.s4_ket = this.hopfProject(this.myReality.genome);
    this.myReality.bqf = BQFCompression.compress(this.myReality.genome);
    this.myReality.lastUpdate = Date.now();
    
    // Update fitness
    this.myReality.fitness = this.myReality.computeFitness();
  }
  
  /**
   * Generate random S³ fiber
   * @returns {Array<number>} - Random 4D quaternion
   */
  generateRandomFiber() {
    return [
      Math.random() * 2 - 1,  // q₀
      Math.random() * 2 - 1,  // q₁
      Math.random() * 2 - 1,  // q₂
      Math.random() * 2 - 1   // q₃
    ];
  }
  
  /**
   * Compute correlation between two projective points
   * @param {Array<number>} projA - First S⁴ point
   * @param {Array<number>} projB - Second S⁴ point
   * @returns {number} - Correlation (-1 to 1)
   */
  computeCorrelation(projA, projB) {
    return HopfFibration.correlation(projA, projB);
  }
  
  /**
   * Get all linked peers
   * @returns {Array} - Array of peer information
   */
  getLinkedPeers() {
    const peers = [];
    
    for (const [peerId, data] of this.peers) {
      const sharedKet = this.sharedKets.get(peerId);
      const history = this.linkHistory.get(peerId) || [];
      
      peers.push({
        id: peerId,
        proj: data.proj,
        sharedKet,
        linkCount: history.length,
        lastLink: history.length > 0 ? history[history.length - 1] : null,
        correlation: this.computeCorrelation(this.myReality.s4_ket, data.proj)
      });
    }
    
    return peers;
  }
  
  /**
   * Get entanglement statistics
   * @returns {Object} - Statistics object
   */
  getStatistics() {
    const peers = this.getLinkedPeers();
    
    if (peers.length === 0) {
      return {
        linkedPeers: 0,
        averageCorrelation: 0,
        totalLinks: 0,
        uniquePeers: 0
      };
    }
    
    const correlations = peers.map(p => p.correlation);
    const averageCorrelation = correlations.reduce((sum, corr) => sum + corr, 0) / correlations.length;
    const totalLinks = peers.reduce((sum, p) => sum + p.linkCount, 0);
    const uniquePeers = new Set(peers.map(p => p.id)).size;
    
    return {
      linkedPeers: peers.length,
      averageCorrelation,
      totalLinks,
      uniquePeers,
      myProjectiveState: this.myReality.s4_ket,
      sharedKetsCount: this.sharedKets.size,
      uptime: Date.now() - (this.startTime || Date.now())
    };
  }
  
  /**
   * Find best correlated peers
   * @param {number} limit - Maximum number to return
   * @returns {Array} - Array of best peers
   */
  getBestCorrelatedPeers(limit = 5) {
    const peers = this.getLinkedPeers();
    
    return peers
      .sort((a, b) => b.correlation - a.correlation)
      .slice(0, limit);
  }
  
  /**
   * Break link with specific peer
   * @param {string} peerId - Peer ID to break link with
   */
  breakLink(peerId) {
    this.sharedKets.delete(peerId);
    this.peers.delete(peerId);
    this.linkHistory.delete(peerId);
    
    console.log(`💔 Broken link with peer: ${peerId}`);
  }
  
  /**
   * Reset all links
   */
  reset() {
    this.peers.clear();
    this.sharedKets.clear();
    this.linkHistory.clear();
    
    console.log('🔄 Projective P2P links reset');
  }
}

module.exports = ProjectiveKetLinker;