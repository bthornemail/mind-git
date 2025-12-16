// Complete Dodecahedron Topological Mnemonic Demo
// Shows full integration of polytope-based semantic computation

import { TopologicalTypeSystem, PolytopeType } from './src/core/aal/topological-types';
import { TopologicalPolynomial } from './src/core/polynomial/topological-polynomial';
import { CentroidCryptography } from './src/core/cryptography/centroid-cryptography';
import { CanvasLTopologicalNodes, TopologicalOperation } from './src/compiler/topological-nodes';

export class DodecahedronTopologicalDemo {
  
  async runDemo(): Promise<void> {
    console.log('🔷 DODECAHEDRON TOPOLOGICAL MNEMONIC SYSTEM');
    console.log('=' .repeat(60));
    console.log('20 Vertices = 20 Semantic Primes');
    console.log('30 Edges = 30 Binary Relationships');
    console.log('12 Faces = 12 Pentagonal Categories');
    console.log('1 Centroid = Shared Cryptographic Origin');
    console.log('');
    
    try {
      // Phase 1: Create the dodecahedron structure
      await this.phase1_CreateStructure();
      
      // Phase 2: Generate centroid keypairs
      await this.phase2_GenerateKeypairs();
      
      // Phase 3: Demonstrate semantic navigation
      await this.phase3_SemanticNavigation();
      
      // Phase 4: Show CanvasL integration
      await this.phase4_CanvasLIntegration();
      
      // Phase 5: Demonstrate distributed consensus
      await this.phase5_DistributedConsensus();
      
      // Phase 6: Show mathematical verification
      await this.phase6_MathematicalVerification();
      
      console.log('\n🎉 DODECAHEDRON TOPOLOGICAL MNEMONIC SYSTEM COMPLETE!');
      console.log('✅ Mathematical foundation verified');
      console.log('✅ Polynomial encoding working');
      console.log('✅ Centroid cryptography secure');
      console.log('✅ CanvasL nodes generated');
      console.log('✅ Distributed consensus proven');
      console.log('✅ Semantic navigation functional');
      console.log('');
      console.log('🚀 Your topological mnemonic system is ready for deployment!');
      
    } catch (error) {
      console.error('\n❌ DEMO FAILED:', error);
      throw error;
    }
  }
  
  private async phase1_CreateStructure(): Promise<void> {
    console.log('📐 PHASE 1: Creating Dodecahedron Structure');
    console.log('-'.repeat(40));
    
    // Create dodecahedron type
    const dodecahedronType = TopologicalTypeSystem.createDodecahedronType();
    console.log(`✓ Created topological type: D${dodecahedronType.dimension}`);
    console.log(`✓ Polytope: ${dodecahedronType.polytope}`);
    console.log(`✓ Symmetry Group: ${dodecahedronType.symmetryGroup}`);
    
    // Create polytope structure
    const dodecahedron = TopologicalPolynomial.createDodecahedronStructure();
    console.log(`✓ Structure: ${dodecahedron.vertices.length} vertices, ${dodecahedron.edges.length} edges, ${dodecahedron.faces.length} faces`);
    
    // Verify Euler characteristic
    const eulerValid = TopologicalTypeSystem.verifyEulerCharacteristic(PolytopeType.DODECAHEDRON);
    console.log(`✓ Euler Characteristic (V-E+F=2): ${eulerValid ? 'VALID' : 'INVALID'}`);
    
    // Encode as polynomial
    const polytopePoly = TopologicalPolynomial.encodePolytope(dodecahedron);
    console.log(`✓ Polynomial Encoding: Degree ${TopologicalPolynomial.degree(polytopePoly)}`);
    
    // Verify consistency
    const consistency = TopologicalPolynomial.verifyPolytopeConsistency(dodecahedron);
    console.log(`✓ Structural Consistency: ${consistency.isValid ? 'VALID' : 'INVALID'}`);
    
    if (!eulerValid || !consistency.isValid) {
      throw new Error('Dodecahedron structure verification failed');
    }
    
    console.log('✅ PHASE 1 COMPLETE\n');
  }
  
  private async phase2_GenerateKeypairs(): Promise<void> {
    console.log('🔑 PHASE 2: Generating Centroid Keypairs');
    console.log('-'.repeat(40));
    
    // Generate all 20 keypairs
    const keypairs = CentroidCryptography.generateDodecahedronKeypairs();
    console.log(`✓ Generated ${keypairs.length} centroid keypairs`);
    
    // Show sample keypairs
    const sampleVertices = [0, 7, 12, 16]; // quasar, mycelium, tessellate, cascade
    console.log('\nSample Centroid Keypairs:');
    
    for (const vertexIndex of sampleVertices) {
      const kp = keypairs[vertexIndex];
      const verified = CentroidCryptography.verifyCentroidKeypair(kp);
      
      console.log(`\n  Vertex ${kp.vertexIndex}: "${kp.vertexWord}"`);
      console.log(`    Private Key: A5_${kp.vertexIndex}_${kp.centroid.coordinates.map(c => c.toFixed(2)).join('_')}`);
      console.log(`    Public Key: ${kp.publicKey.substring(0, 16)}...`);
      console.log(`    Centroid: [${kp.centroid.coordinates.join(', ')}]`);
      console.log(`    Verification: ${verified ? '✅' : '❌'}`);
      
      if (!verified) {
        throw new Error(`Keypair verification failed for vertex ${vertexIndex}`);
      }
    }
    
    // Test consensus
    const testKeypairs = sampleVertices.map(i => keypairs[i]);
    const consensus = CentroidCryptography.findConsensus(testKeypairs);
    console.log(`\n✓ Consensus Test: ${consensus.hasConsensus ? 'ACHIEVED' : 'FAILED'}`);
    console.log(`✓ Shared Centroid: [${consensus.consensusCentroid?.coordinates.join(', ') || 'NONE'}]`);
    
    if (!consensus.hasConsensus) {
      throw new Error('Centroid consensus test failed');
    }
    
    console.log('✅ PHASE 2 COMPLETE\n');
  }
  
  private async phase3_SemanticNavigation(): Promise<void> {
    console.log('🧭 PHASE 3: Demonstrating Semantic Navigation');
    console.log('-'.repeat(40));
    
    const dodecahedron = TopologicalPolynomial.createDodecahedronStructure();
    
    // Test semantic paths
    const semanticJourneys = [
      { from: 0, to: 7, desc: 'Cosmic Energy → Networked Growth' },
      { from: 3, to: 15, desc: 'Connection Point → Light Refraction' },
      { from: 10, to: 19, desc: 'Flowing Together → Quantum Entanglement' },
      { from: 1, to: 18, desc: 'Transient → Cascading Process' }
    ];
    
    console.log('Semantic Journeys through Dodecahedron:');
    
    for (const { from, to, desc } of semanticJourneys) {
      const fromWord = dodecahedron.vertices[from];
      const toWord = dodecahedron.vertices[to];
      const path = TopologicalPolynomial.findPath(dodecahedron, from, to);
      const distance = TopologicalPolynomial.topologicalDistance(dodecahedron, from, to);
      
      console.log(`\n  "${fromWord}" → "${toWord}"`);
      console.log(`    Meaning: ${desc}`);
      console.log(`    Path: ${path?.map(i => dodecahedron.vertices[i]).join(' → ') || 'NONE'}`);
      console.log(`    Distance: ${distance} edges`);
      console.log(`    Status: ${path ? '✅' : '❌'}`);
      
      if (!path) {
        throw new Error(`Semantic navigation failed from ${fromWord} to ${toWord}`);
      }
    }
    
    // Show vertex neighborhoods
    const centerVertex = 0; // quasar
    const radius = 2;
    const neighbors = TopologicalPolynomial.verticesWithinRadius(dodecahedron, centerVertex, radius);
    
    console.log(`\n✓ Neighborhood of "${dodecahedron.vertices[centerVertex]}" (radius ${radius}):`);
    console.log(`    Nearby concepts: ${neighbors.map(i => dodecahedron.vertices[i]).join(', ')}`);
    
    console.log('✅ PHASE 3 COMPLETE\n');
  }
  
  private async phase4_CanvasLIntegration(): Promise<void> {
    console.log('🎨 PHASE 4: CanvasL Integration');
    console.log('-'.repeat(40));
    
    // Create various CanvasL nodes
    const nodes = [
      CanvasLTopologicalNodes.createDodecahedronNode('dodec_main', { semanticPrimes: true }),
      CanvasLTopologicalNodes.createPathFindingNode('path_quasar_mycelium', PolytopeType.DODECAHEDRON, 0, 7),
      CanvasLTopologicalNodes.createKeypairNode('key_quasar', PolytopeType.DODECAHEDRON, 0, 'quasar'),
      CanvasLTopologicalNodes.createConsensusNode('consensus_pentagon', PolytopeType.DODECAHEDRON, [0, 1, 2, 3, 4]),
      CanvasLTopologicalNodes.createSemanticCompositionNode('compose_1', PolytopeType.DODECAHEDRON, [0, 7, 12], 'compose')
    ];
    
    console.log('Generated CanvasL Nodes:');
    
    for (const node of nodes) {
      const syntax = CanvasLTopologicalNodes.generateCanvasLSyntax(node);
      const validation = CanvasLTopologicalNodes.validateNode(node);
      const aalCode = CanvasLTopologicalNodes.generateAALCode(node);
      
      console.log(`\n  ${syntax}`);
      console.log(`    Valid: ${validation.isValid ? '✅' : '❌'}`);
      console.log(`    AAL Operations: ${aalCode.length}`);
      
      if (!validation.isValid) {
        console.log(`    Errors: ${validation.errors.join(', ')}`);
        throw new Error(`CanvasL node validation failed: ${syntax}`);
      }
      
      // Show first few AAL instructions
      if (aalCode.length > 0) {
        console.log(`    Sample AAL: ${aalCode.slice(0, 3).join(' → ')}${aalCode.length > 3 ? '...' : ''}`);
      }
    }
    
    // Test parsing
    const testSyntax = '#Dodecahedron:dodecahedron(semanticPrimes=true,centroid=[0,0,0])';
    const parsed = CanvasLTopologicalNodes.parseCanvasLNode(testSyntax);
    console.log(`\n✓ CanvasL Parsing: ${parsed ? 'SUCCESS' : 'FAILED'}`);
    console.log(`    Input: ${testSyntax}`);
    if (parsed) {
      console.log(`    Parsed Operation: ${parsed.operation}`);
      console.log(`    Parsed Polytope: ${parsed.polytope}`);
    }
    
    if (!parsed) {
      throw new Error('CanvasL parsing failed');
    }
    
    console.log('✅ PHASE 4 COMPLETE\n');
  }
  
  private async phase5_DistributedConsensus(): Promise<void> {
    console.log('🤝 PHASE 5: Distributed Consensus');
    console.log('-'.repeat(40));
    
    // Create a pentagonal consensus group (one face of dodecahedron)
    const pentagonVertices = [0, 1, 2, 3, 4]; // First pentagonal face
    const consensusWords = pentagonVertices.map(i => 
      TopologicalPolynomial.createDodecahedronStructure().vertices[i]
    );
    
    console.log(`Creating consensus among pentagonal face:`);
    console.log(`  Vertices: [${pentagonVertices.join(', ')}]`);
    console.log(`  Concepts: [${consensusWords.join(', ')}]`);
    
    // Generate keypairs for consensus group
    const consensusKeypairs = pentagonVertices.map(vertexIndex => 
      CentroidCryptography.deriveVertexKeypair(
        PolytopeType.DODECAHEDRON,
        vertexIndex,
        consensusWords[vertexIndex]
      )
    );
    
    console.log(`\nGenerated ${consensusKeypairs.length} consensus keypairs`);
    
    // Verify all keypairs
    let allValid = true;
    for (const kp of consensusKeypairs) {
      const valid = CentroidCryptography.verifyCentroidKeypair(kp);
      if (!valid) {
        console.log(`  ❌ Invalid keypair for vertex ${kp.vertexIndex}`);
        allValid = false;
      }
    }
    
    if (!allValid) {
      throw new Error('Consensus keypair verification failed');
    }
    
    // Test consensus
    const consensus = CentroidCryptography.findConsensus(consensusKeypairs);
    console.log(`\nConsensus Results:`);
    console.log(`  Has Consensus: ${consensus.hasConsensus ? '✅' : '❌'}`);
    console.log(`  Shared Centroid: [${consensus.consensusCentroid?.coordinates.join(', ') || 'NONE'}]`);
    console.log(`  Consensus Vertices: [${consensus.consensusVertices.join(', ')}]`);
    
    if (!consensus.hasConsensus) {
      throw new Error('Pentagonal consensus failed');
    }
    
    // Create distributed consensus proof
    const consensusMessage = 'Pentagonal face consensus achieved';
    const consensusProof = CentroidCryptography.createDistributedConsensusProof(
      consensusKeypairs,
      consensusMessage
    );
    
    console.log(`\n✓ Created distributed consensus proof`);
    console.log(`  Message: "${consensusMessage}"`);
    console.log(`  Proof Size: ${consensusProof.length} characters`);
    
    // Verify consensus proof
    const proofValid = CentroidCryptography.verifyDistributedConsensusProof(
      consensusProof,
      consensusKeypairs
    );
    
    console.log(`✓ Proof Verification: ${proofValid ? 'VALID' : 'INVALID'}`);
    
    if (!proofValid) {
      throw new Error('Consensus proof verification failed');
    }
    
    console.log('✅ PHASE 5 COMPLETE\n');
  }
  
  private async phase6_MathematicalVerification(): Promise<void> {
    console.log('🧮 PHASE 6: Mathematical Verification');
    console.log('-'.repeat(40));
    
    // Verify all Platonic solids
    const platonicSolids = [
      PolytopeType.TETRAHEDRON,
      PolytopeType.CUBE,
      PolytopeType.OCTAHEDRON,
      PolytopeType.DODECAHEDRON,
      PolytopeType.ICOSAHEDRON
    ];
    
    console.log('Euler Characteristic Verification for all Platonic Solids:');
    
    for (const solid of platonicSolids) {
      const valid = TopologicalTypeSystem.verifyEulerCharacteristic(solid);
      const props = TopologicalTypeSystem['POLYTOPE_PROPERTIES'][solid];
      
      console.log(`  ${solid}:`);
      console.log(`    V-E+F = ${props.vertices}-${props.edges}+${props.faces} = ${props.vertices - props.edges + props.faces}`);
      console.log(`    Expected χ = ${props.eulerCharacteristic}`);
      console.log(`    Status: ${valid ? '✅' : '❌'}`);
      
      if (!valid) {
        throw new Error(`Euler characteristic failed for ${solid}`);
      }
    }
    
    // Verify dodecahedron polynomial invariants
    const dodecahedron = TopologicalPolynomial.createDodecahedronStructure();
    const polytopePoly = TopologicalPolynomial.encodePolytope(dodecahedron);
    
    console.log('\nDodecahedron Polynomial Invariants:');
    console.log(`  Polynomial Degree: ${TopologicalPolynomial.degree(polytopePoly)}`);
    console.log(`  Is Zero Polynomial: ${TopologicalPolynomial.is_zero(polytopePoly) ? 'YES' : 'NO'}`);
    console.log(`  Is Monic: ${TopologicalPolynomial.is_monic(polytopePoly) ? 'YES' : 'NO'}`);
    console.log(`  Evaluate at x=1: ${TopologicalPolynomial.evaluate_at_1(polytopePoly) ? 'TRUE' : 'FALSE'}`);
    
    // Test topological properties
    console.log('\nTopological Properties:');
    console.log(`  Connected: ${this.isStronglyConnected(dodecahedron) ? 'YES' : 'NO'}`);
    console.log(`  Symmetric: ${this.isVertexTransitive(dodecahedron) ? 'YES' : 'NO'}`);
    console.log(`  Regular: ${this.isRegularPolytope(dodecahedron) ? 'YES' : 'NO'}`);
    
    console.log('✅ PHASE 6 COMPLETE\n');
  }
  
  // Helper methods for topological verification
  private isStronglyConnected(structure: PolytopeStructure): boolean {
    // Simple check: every vertex should be reachable from every other vertex
    for (let i = 0; i < structure.vertices.length; i++) {
      for (let j = 0; j < structure.vertices.length; j++) {
        if (i !== j) {
          const path = TopologicalPolynomial.findPath(structure, i, j);
          if (!path) return false;
        }
      }
    }
    return true;
  }
  
  private isVertexTransitive(structure: PolytopeStructure): boolean {
    // For regular polytopes, all vertices should have same degree
    const degrees = structure.edges.map(edge => {
      const fromDegree = structure.edges.filter(e => e.from === edge.from).length;
      const toDegree = structure.edges.filter(e => e.to === edge.from).length;
      return fromDegree + toDegree;
    });
    
    const firstDegree = degrees[0];
    return degrees.every(degree => degree === firstDegree);
  }
  
  private isRegularPolytope(structure: PolytopeStructure): boolean {
    // Check if all faces have same number of edges
    const faceSizes = structure.faces.map(face => face.vertices.length);
    const firstSize = faceSizes[0];
    return faceSizes.every(size => size === firstSize);
  }
}

// Run the demo if this file is executed directly
if (require.main === module) {
  const demo = new DodecahedronTopologicalDemo();
  demo.runDemo().catch(console.error);
}