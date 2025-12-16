// Dodecahedron Integration Test
// Demonstrates complete topological mnemonic system

import { TopologicalTypeSystem, PolytopeType } from '../src/core/aal/topological-types';
import { TopologicalPolynomial, PolytopeStructure } from '../src/core/polynomial/topological-polynomial';
import { CentroidCryptography, CentroidKeypair } from '../src/core/cryptography/centroid-cryptography';
import { CanvasLTopologicalNodes, TopologicalOperation } from '../src/compiler/topological-nodes';

export class DodecahedronIntegrationTest {
  
  async runCompleteTest(): Promise<void> {
    console.log('🔷 DODECAHEDRON TOPOLOGICAL MNEMONIC SYSTEM TEST');
    console.log('=' .repeat(60));
    
    try {
      // Test 1: Create topological type system
      await this.testTopologicalTypeSystem();
      
      // Test 2: Encode dodecahedron as polynomial
      await this.testDodecahedronPolynomialEncoding();
      
      // Test 3: Generate centroid keypairs
      await this.testCentroidCryptography();
      
      // Test 4: Create CanvasL nodes
      await this.testCanvasLNodes();
      
      // Test 5: Verify Euler characteristic
      await this.testEulerCharacteristic();
      
      // Test 6: Test semantic navigation
      await this.testSemanticNavigation();
      
      // Test 7: Test distributed consensus
      await this.testDistributedConsensus();
      
      console.log('\n✅ ALL TESTS PASSED - Dodecahedron Integration Complete!');
      
    } catch (error) {
      console.error('\n❌ TEST FAILED:', error);
      throw error;
    }
  }
  
  private async testTopologicalTypeSystem(): Promise<void> {
    console.log('\n📐 Test 1: Topological Type System');
    
    // Create dodecahedron type
    const dodecahedronType = TopologicalTypeSystem.createDodecahedronType();
    
    console.log('  Dodecahedron Type:');
    console.log(`    Dimension: D${dodecahedronType.dimension}`);
    console.log(`    Polytope: ${dodecahedronType.polytope}`);
    console.log(`    Vertices: ${dodecahedronType.vertices.length}`);
    console.log(`    Euler Characteristic: ${dodecahedronType.eulerCharacteristic}`);
    console.log(`    Symmetry Group: ${dodecahedronType.symmetryGroup}`);
    
    // Verify Euler characteristic
    const eulerValid = TopologicalTypeSystem.verifyEulerCharacteristic(PolytopeType.DODECAHEDRON);
    console.log(`    Euler Verification: ${eulerValid ? '✅' : '❌'}`);
    
    if (!eulerValid) {
      throw new Error('Euler characteristic verification failed');
    }
    
    console.log('  ✅ Topological type system test passed');
  }
  
  private async testDodecahedronPolynomialEncoding(): Promise<void> {
    console.log('\n🧮 Test 2: Dodecahedron Polynomial Encoding');
    
    // Create dodecahedron structure
    const dodecahedron = TopologicalPolynomial.createDodecahedronStructure();
    
    console.log('  Dodecahedron Structure:');
    console.log(`    Type: ${dodecahedron.type}`);
    console.log(`    Vertices: ${dodecahedron.vertices.length}`);
    console.log(`    Edges: ${dodecahedron.edges.length}`);
    console.log(`    Faces: ${dodecahedron.faces.length}`);
    
    // Encode as polynomial
    const polytopePoly = TopologicalPolynomial.encodePolytope(dodecahedron);
    console.log(`    Polynomial Degree: ${TopologicalPolynomial.degree(polytopePoly)}`);
    console.log(`    Polynomial: ${TopologicalPolynomial.toString(polytopePoly)}`);
    
    // Verify consistency
    const consistency = TopologicalPolynomial.verifyPolytopeConsistency(dodecahedron);
    console.log(`    Consistency: ${consistency.isValid ? '✅' : '❌'}`);
    
    if (!consistency.isValid) {
      console.error('    Errors:', consistency.errors);
      throw new Error('Polytope consistency verification failed');
    }
    
    console.log('  ✅ Polynomial encoding test passed');
  }
  
  private async testCentroidCryptography(): Promise<void> {
    console.log('\n🔑 Test 3: Centroid Cryptography');
    
    // Generate keypairs for all dodecahedron vertices
    const keypairs = CentroidCryptography.generateDodecahedronKeypairs();
    
    console.log(`  Generated ${keypairs.length} centroid keypairs`);
    
    // Show first few keypairs
    for (let i = 0; i < Math.min(3, keypairs.length); i++) {
      const kp = keypairs[i];
      console.log(`\n    Vertex ${kp.vertexIndex} (${kp.vertexWord}):`);
      console.log(`      Private Key: ${kp.privateKey.substring(0, 20)}...`);
      console.log(`      Public Key: ${kp.publicKey.substring(0, 20)}...`);
      console.log(`      Centroid: [${kp.centroid.coordinates.join(', ')}]`);
      
      // Verify keypair
      const isValid = CentroidCryptography.verifyCentroidKeypair(kp);
      console.log(`      Verification: ${isValid ? '✅' : '❌'}`);
      
      if (!isValid) {
        throw new Error(`Keypair verification failed for vertex ${i}`);
      }
    }
    
    // Test consensus
    const consensus = CentroidCryptography.findConsensus(keypairs.slice(0, 5));
    console.log(`\n  Consensus Test (5 vertices):`);
    console.log(`    Has Consensus: ${consensus.hasConsensus ? '✅' : '❌'}`);
    console.log(`    Consensus Vertices: [${consensus.consensusVertices.join(', ')}]`);
    
    if (!consensus.hasConsensus) {
      throw new Error('Centroid consensus test failed');
    }
    
    console.log('  ✅ Centroid cryptography test passed');
  }
  
  private async testCanvasLNodes(): Promise<void> {
    console.log('\n🎨 Test 4: CanvasL Topological Nodes');
    
    // Create various topological nodes
    const dodecahedronNode = CanvasLTopologicalNodes.createDodecahedronNode('dodec_1');
    const pathNode = CanvasLTopologicalNodes.createPathFindingNode('path_1', PolytopeType.DODECAHEDRON, 0, 7);
    const keypairNode = CanvasLTopologicalNodes.createKeypairNode('key_1', PolytopeType.DODECAHEDRON, 0, 'quasar');
    const consensusNode = CanvasLTopologicalNodes.createConsensusNode('consensus_1', PolytopeType.DODECAHEDRON, [0, 1, 2, 3, 4]);
    
    console.log('  Created CanvasL Nodes:');
    
    const nodes = [
      { name: 'Dodecahedron', node: dodecahedronNode },
      { name: 'Path Finding', node: pathNode },
      { name: 'Keypair', node: keypairNode },
      { name: 'Consensus', node: consensusNode }
    ];
    
    for (const { name, node } of nodes) {
      const syntax = CanvasLTopologicalNodes.generateCanvasLSyntax(node);
      const validation = CanvasLTopologicalNodes.validateNode(node);
      const aalCode = CanvasLTopologicalNodes.generateAALCode(node);
      
      console.log(`\n    ${name} Node:`);
      console.log(`      Syntax: ${syntax}`);
      console.log(`      Valid: ${validation.isValid ? '✅' : '❌'}`);
      if (!validation.isValid) {
        console.log(`      Errors: ${validation.errors.join(', ')}`);
      }
      console.log(`      AAL Instructions: ${aalCode.length} operations`);
      
      if (!validation.isValid) {
        throw new Error(`CanvasL node validation failed for ${name}`);
      }
    }
    
    // Test parsing
    const parsedDodecahedron = CanvasLTopologicalNodes.parseCanvasLNode('#Dodecahedron:dodecahedron(semanticPrimes=true)');
    console.log(`\n  Parsed CanvasL: ${parsedDodecahedron ? '✅' : '❌'}`);
    
    if (!parsedDodecahedron) {
      throw new Error('CanvasL parsing failed');
    }
    
    console.log('  ✅ CanvasL nodes test passed');
  }
  
  private async testEulerCharacteristic(): Promise<void> {
    console.log('\n📐 Test 5: Euler Characteristic Verification');
    
    const polytopes = [
      PolytopeType.TETRAHEDRON,
      PolytopeType.CUBE,
      PolytopeType.OCTAHEDRON,
      PolytopeType.DODECAHEDRON,
      PolytopeType.ICOSAHEDRON
    ];
    
    console.log('  Euler Characteristic Verification:');
    
    for (const polytope of polytopes) {
      const isValid = TopologicalTypeSystem.verifyEulerCharacteristic(polytope);
      const props = TopologicalTypeSystem['POLYTOPE_PROPERTIES'][polytope];
      
      console.log(`    ${polytope}: V=${props.vertices}, E=${props.edges}, F=${props.faces}, χ=${props.eulerCharacteristic} ${isValid ? '✅' : '❌'}`);
      
      if (!isValid) {
        throw new Error(`Euler characteristic failed for ${polytope}`);
      }
    }
    
    console.log('  ✅ Euler characteristic test passed');
  }
  
  private async testSemanticNavigation(): Promise<void> {
    console.log('\n🧭 Test 6: Semantic Navigation');
    
    const dodecahedron = TopologicalPolynomial.createDodecahedronStructure();
    
    // Test path finding between semantic primes
    const testPaths = [
      { from: 0, to: 7, fromWord: 'quasar', toWord: 'mycelium' },
      { from: 3, to: 15, fromWord: 'nexus', toWord: 'prismatic' },
      { from: 10, to: 19, fromWord: 'confluence', toWord: 'entangle' }
    ];
    
    console.log('  Semantic Path Finding:');
    
    for (const { from, to, fromWord, toWord } of testPaths) {
      const path = TopologicalPolynomial.findPath(dodecahedron, from, to);
      const distance = TopologicalPolynomial.topologicalDistance(dodecahedron, from, to);
      
      console.log(`    ${fromWord} → ${toWord}:`);
      console.log(`      Path: [${path?.join(' → ') || 'NONE'}]`);
      console.log(`      Distance: ${distance} edges`);
      console.log(`      Status: ${path ? '✅' : '❌'}`);
      
      if (!path) {
        throw new Error(`Path finding failed from ${fromWord} to ${toWord}`);
      }
    }
    
    // Test neighbors
    const centerVertex = 0; // quasar
    const neighbors = TopologicalPolynomial.findConnectedVertices(
      TopologicalPolynomial.encodePolytope(dodecahedron),
      centerVertex,
      dodecahedron.vertices.length
    );
    
    console.log(`\n  Neighbors of "${dodecahedron.vertices[centerVertex]}":`);
    console.log(`    Connected vertices: [${neighbors.join(', ')}]`);
    console.log(`    Status: ${neighbors.length > 0 ? '✅' : '❌'}`);
    
    if (neighbors.length === 0) {
      throw new Error('Neighbor finding failed');
    }
    
    console.log('  ✅ Semantic navigation test passed');
  }
  
  private async testDistributedConsensus(): Promise<void> {
    console.log('\n🤝 Test 7: Distributed Consensus');
    
    // Generate keypairs for subset of vertices
    const consensusVertices = [0, 3, 7, 12, 16]; // quasar, nexus, mycelium, tessellate, cascade
    const keypairs = consensusVertices.map(vertexIndex => 
      CentroidCryptography.deriveVertexKeypair(
        PolytopeType.DODECAHEDRON,
        vertexIndex,
        TopologicalPolynomial.createDodecahedronStructure().vertices[vertexIndex]
      )
    );
    
    console.log(`  Testing consensus among ${keypairs.length} vertices:`);
    console.log(`    Vertices: [${consensusVertices.map(i => TopologicalPolynomial.createDodecahedronStructure().vertices[i]).join(', ')}]`);
    
    // Verify all keypairs
    for (const kp of keypairs) {
      const isValid = CentroidCryptography.verifyCentroidKeypair(kp);
      if (!isValid) {
        throw new Error(`Keypair verification failed for vertex ${kp.vertexIndex}`);
      }
    }
    
    // Test consensus
    const consensus = CentroidCryptography.findConsensus(keypairs);
    console.log(`    Consensus: ${consensus.hasConsensus ? '✅' : '❌'}`);
    console.log(`    Shared Centroid: [${consensus.consensusCentroid?.coordinates.join(', ') || 'NONE'}]`);
    
    if (!consensus.hasConsensus) {
      throw new Error('Distributed consensus failed');
    }
    
    // Create distributed consensus proof
    const message = 'Test consensus message';
    const consensusProof = CentroidCryptography.createDistributedConsensusProof(keypairs, message);
    console.log(`    Consensus Proof: Generated ✅`);
    
    // Verify consensus proof
    const proofValid = CentroidCryptography.verifyDistributedConsensusProof(consensusProof, keypairs);
    console.log(`    Proof Verification: ${proofValid ? '✅' : '❌'}`);
    
    if (!proofValid) {
      throw new Error('Consensus proof verification failed');
    }
    
    console.log('  ✅ Distributed consensus test passed');
  }
}

// Run the test if this file is executed directly
if (require.main === module) {
  const test = new DodecahedronIntegrationTest();
  test.runCompleteTest().catch(console.error);
}