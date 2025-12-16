// Centroid-Based Cryptography for Topological Mnemonic Systems
// Extends existing cubic cryptography with polytope-based keypair generation

import { CubicCryptography } from '../cryptography/cubic-signature';
import { TopologicalPolynomial, PolytopeStructure } from '../polynomial/topological-polynomial';
import { PolytopeType, TopologicalType, DODECAHEDRON_SEMANTIC_PRIMES } from '../aal/topological-types';

export interface CentroidKeypair {
  polytope: PolytopeType;
  vertexIndex: number;
  vertexWord: string;
  centroid: VectorND;
  privateKey: string;
  publicKey: string;
  proof: string;
}

export interface VectorND {
  coordinates: number[];
  dimension: number;
}

export interface CentroidProof {
  vertexIndex: number;
  centroidHash: string;
  vertexHash: string;
  signature: string;
  polytopeType: PolytopeType;
  symmetryGroup: string;
}

export class CentroidCryptography extends CubicCryptography {
  
  /**
   * Generate shared centroid for a polytope
   * Centroid is always the origin [0, 0, 0, ...] in typed space
   */
  static generateCentroid(dimension: number): VectorND {
    return {
      coordinates: new Array(dimension).fill(0),
      dimension
    };
  }
  
  /**
   * Derive cryptographic keypair for a vertex from shared centroid
   * Private key = hash(centroid || vertex_position || symmetry_group)
   * Public key = project(private_key, vertex_position)
   */
  static deriveVertexKeypair(
    polytope: PolytopeType,
    vertexIndex: number,
    vertexWord: string,
    centroid?: VectorND
  ): CentroidKeypair {
    
    // Use default centroid if not provided
    const polytopeCentroid = centroid || this.generateCentroid(3); // 3D for most polytopes
    
    // Get vertex position in polytope space
    const vertexPosition = this.getVertexPosition(polytope, vertexIndex);
    
    // Get symmetry group for polytope
    const symmetryGroup = this.getSymmetryGroup(polytope);
    
    // Generate private key from centroid + vertex + symmetry
    const privateKey = this.hashCentroidVertex(
      polytopeCentroid,
      vertexPosition,
      symmetryGroup,
      vertexWord
    );
    
    // Generate public key by projecting private key to vertex space
    const publicKey = this.projectToVertexSpace(privateKey, vertexPosition);
    
    // Generate proof of membership
    const proof = this.generateCentroidProof(
      polytope,
      vertexIndex,
      polytopeCentroid,
      privateKey,
      publicKey
    );
    
    return {
      polytope,
      vertexIndex,
      vertexWord,
      centroid: polytopeCentroid,
      privateKey,
      publicKey,
      proof
    };
  }
  
  /**
   * Get vertex position in polytope's coordinate system
   */
  private static getVertexPosition(polytope: PolytopeType, vertexIndex: number): VectorND {
    switch (polytope) {
      case PolytopeType.DODECAHEDRON:
        return this.getDodecahedronVertexPosition(vertexIndex);
      case PolytopeType.TETRAHEDRON:
        return this.getTetrahedronVertexPosition(vertexIndex);
      case PolytopeType.CUBE:
        return this.getCubeVertexPosition(vertexIndex);
      case PolytopeType.ICOSAHEDRON:
        return this.getIcosahedronVertexPosition(vertexIndex);
      default:
        throw new Error(`Vertex positions not defined for polytope: ${polytope}`);
    }
  }
  
  /**
   * Dodecahedron vertex positions (20 vertices)
   * Uses golden ratio φ = (1 + √5) / 2
   */
  private static getDodecahedronVertexPosition(vertexIndex: number): VectorND {
    const φ = (1 + Math.sqrt(5)) / 2; // Golden ratio
    
    // Dodecahedron vertices (standard coordinates)
    const vertices = [
      // Cube vertices scaled by φ
      [1, 1, 1], [1, 1, -1], [1, -1, 1], [1, -1, -1],
      [-1, 1, 1], [-1, 1, -1], [-1, -1, 1], [-1, -1, -1],
      // Rectangle vertices in three orthogonal planes
      [0, φ, 1/φ], [0, φ, -1/φ], [0, -φ, 1/φ], [0, -φ, -1/φ],
      [1/φ, 0, φ], [1/φ, 0, -φ], [-1/φ, 0, φ], [-1/φ, 0, -φ],
      [φ, 1/φ, 0], [φ, -1/φ, 0], [-φ, 1/φ, 0], [-φ, -1/φ, 0]
    ];
    
    if (vertexIndex >= vertices.length) {
      throw new Error(`Invalid vertex index ${vertexIndex} for dodecahedron`);
    }
    
    return {
      coordinates: vertices[vertexIndex],
      dimension: 3
    };
  }
  
  /**
   * Tetrahedron vertex positions (4 vertices)
   */
  private static getTetrahedronVertexPosition(vertexIndex: number): VectorND {
    const vertices = [
      [1, 1, 1],
      [1, -1, -1],
      [-1, 1, -1],
      [-1, -1, 1]
    ];
    
    if (vertexIndex >= vertices.length) {
      throw new Error(`Invalid vertex index ${vertexIndex} for tetrahedron`);
    }
    
    return {
      coordinates: vertices[vertexIndex],
      dimension: 3
    };
  }
  
  /**
   * Cube vertex positions (8 vertices)
   */
  private static getCubeVertexPosition(vertexIndex: number): VectorND {
    const vertices = [
      [-1, -1, -1], [1, -1, -1], [1, 1, -1], [-1, 1, -1],
      [-1, -1, 1], [1, -1, 1], [1, 1, 1], [-1, 1, 1]
    ];
    
    if (vertexIndex >= vertices.length) {
      throw new Error(`Invalid vertex index ${vertexIndex} for cube`);
    }
    
    return {
      coordinates: vertices[vertexIndex],
      dimension: 3
    };
  }
  
  /**
   * Icosahedron vertex positions (12 vertices)
   */
  private static getIcosahedronVertexPosition(vertexIndex: number): VectorND {
    const φ = (1 + Math.sqrt(5)) / 2;
    const vertices = [
      [0, 1, φ], [0, 1, -φ], [0, -1, φ], [0, -1, -φ],
      [1, φ, 0], [1, -φ, 0], [-1, φ, 0], [-1, -φ, 0],
      [φ, 0, 1], [φ, 0, -1], [-φ, 0, 1], [-φ, 0, -1]
    ];
    
    if (vertexIndex >= vertices.length) {
      throw new Error(`Invalid vertex index ${vertexIndex} for icosahedron`);
    }
    
    return {
      coordinates: vertices[vertexIndex],
      dimension: 3
    };
  }
  
  /**
   * Get symmetry group for polytope
   */
  private static getSymmetryGroup(polytope: PolytopeType): string {
    switch (polytope) {
      case PolytopeType.TETRAHEDRON:
        return 'A4';
      case PolytopeType.CUBE:
      case PolytopeType.OCTAHEDRON:
        return 'S4×C2';
      case PolytopeType.DODECAHEDRON:
      case PolytopeType.ICOSAHEDRON:
        return 'A5×C2';
      case PolytopeType.FIVE_CELL:
        return 'A5';
      case PolytopeType.SIXTEEN_CELL:
      case PolytopeType.TWENTY_FOUR_CELL:
        return 'B4' || 'F4';
      case PolytopeType.ONE_TWENTY_CELL:
      case PolytopeType.SIX_HUNDRED_CELL:
        return 'H4';
      default:
        return 'UNKNOWN';
    }
  }
  
  /**
   * Hash centroid, vertex position, and symmetry group to create private key
   */
  private static hashCentroidVertex(
    centroid: VectorND,
    vertexPosition: VectorND,
    symmetryGroup: string,
    vertexWord: string
  ): string {
    // Combine all elements into a single string
    const combined = [
      `centroid:${centroid.coordinates.join(',')}`,
      `vertex:${vertexPosition.coordinates.join(',')}`,
      `symmetry:${symmetryGroup}`,
      `word:${vertexWord}`
    ].join('|');
    
    // Use existing cubic cryptography for hashing
    return this.hashString(combined);
  }
  
  /**
   * Project private key to vertex space to create public key
   */
  private static projectToVertexSpace(privateKey: string, vertexPosition: VectorND): string {
    // Use vertex position as projection parameters
    const projectionParams = vertexPosition.coordinates.join(',');
    const projectionInput = `${privateKey}|project:${projectionParams}`;
    
    return this.hashString(projectionInput);
  }
  
  /**
   * Generate proof that vertex belongs to polytope with shared centroid
   */
  private static generateCentroidProof(
    polytope: PolytopeType,
    vertexIndex: number,
    centroid: VectorND,
    privateKey: string,
    publicKey: string
  ): string {
    const centroidHash = this.hashVector(centroid);
    const vertexHash = this.hashVertex(polytope, vertexIndex);
    
    // Sign the combination with private key
    const message = `${centroidHash}|${vertexHash}|${polytope}`;
    const signature = this.signMessage(privateKey, message);
    
    return JSON.stringify({
      vertexIndex,
      centroidHash,
      vertexHash,
      signature,
      polytopeType: polytope,
      symmetryGroup: this.getSymmetryGroup(polytope)
    });
  }
  
  /**
   * Hash a vector for consistent representation
   */
  private static hashVector(vector: VectorND): string {
    const vectorString = `${vector.dimension}:${vector.coordinates.join(',')}`;
    return this.hashString(vectorString);
  }
  
  /**
   * Hash a vertex in a polytope
   */
  private static hashVertex(polytope: PolytopeType, vertexIndex: number): string {
    return this.hashString(`${polytope}:vertex:${vertexIndex}`);
  }
  
  /**
   * Verify that a keypair is consistent with centroid and polytope
   */
  static verifyCentroidKeypair(keypair: CentroidKeypair): boolean {
    try {
      // Parse proof
      const proof: CentroidProof = JSON.parse(keypair.proof);
      
      // Verify centroid hash
      const expectedCentroidHash = this.hashVector(keypair.centroid);
      if (proof.centroidHash !== expectedCentroidHash) {
        return false;
      }
      
      // Verify vertex hash
      const expectedVertexHash = this.hashVertex(keypair.polytope, keypair.vertexIndex);
      if (proof.vertexHash !== expectedVertexHash) {
        return false;
      }
      
      // Verify signature
      const message = `${proof.centroidHash}|${proof.vertexHash}|${keypair.polytope}`;
      const isValidSignature = this.verifySignature(
        keypair.publicKey,
        message,
        proof.signature
      );
      
      if (!isValidSignature) {
        return false;
      }
      
      // Verify public key derivation
      const vertexPosition = this.getVertexPosition(keypair.polytope, keypair.vertexIndex);
      const expectedPublicKey = this.projectToVertexSpace(keypair.privateKey, vertexPosition);
      
      return keypair.publicKey === expectedPublicKey;
      
    } catch (error) {
      console.error('Error verifying centroid keypair:', error);
      return false;
    }
  }
  
  /**
   * Generate keypairs for all vertices in a polytope
   */
  static generatePolytopeKeypairs(
    polytope: PolytopeType,
    vertexWords: string[],
    centroid?: VectorND
  ): CentroidKeypair[] {
    const keypairs: CentroidKeypair[] = [];
    
    for (let i = 0; i < vertexWords.length; i++) {
      const keypair = this.deriveVertexKeypair(
        polytope,
        i,
        vertexWords[i],
        centroid
      );
      keypairs.push(keypair);
    }
    
    return keypairs;
  }
  
  /**
   * Generate dodecahedron keypairs with semantic primes
   */
  static generateDodecahedronKeypairs(centroid?: VectorND): CentroidKeypair[] {
    return this.generatePolytopeKeypairs(
      PolytopeType.DODECAHEDRON,
      DODECAHEDRON_SEMANTIC_PRIMES,
      centroid
    );
  }
  
  /**
   * Check if two vertices share the same centroid (consensus)
   */
  static shareSameCentroid(keypair1: CentroidKeypair, keypair2: CentroidKeypair): boolean {
    // Check if both keypairs have same centroid coordinates
    if (keypair1.centroid.dimension !== keypair2.centroid.dimension) {
      return false;
    }
    
    for (let i = 0; i < keypair1.centroid.dimension; i++) {
      if (keypair1.centroid.coordinates[i] !== keypair2.centroid.coordinates[i]) {
        return false;
      }
    }
    
    return true;
  }
  
  /**
   * Find consensus among multiple vertices
   */
  static findConsensus(keypairs: CentroidKeypair[]): {
    hasConsensus: boolean;
    consensusCentroid?: VectorND;
    consensusVertices: number[];
  } {
    if (keypairs.length === 0) {
      return { hasConsensus: false, consensusVertices: [] };
    }
    
    const firstCentroid = keypairs[0].centroid;
    const consensusVertices: number[] = [keypairs[0].vertexIndex];
    
    for (let i = 1; i < keypairs.length; i++) {
      if (this.shareSameCentroid(keypairs[0], keypairs[i])) {
        consensusVertices.push(keypairs[i].vertexIndex);
      }
    }
    
    return {
      hasConsensus: consensusVertices.length === keypairs.length,
      consensusCentroid: firstCentroid,
      consensusVertices
    };
  }
  
  /**
   * Create distributed consensus proof
   */
  static createDistributedConsensusProof(
    keypairs: CentroidKeypair[],
    message: string
  ): string {
    const consensus = this.findConsensus(keypairs);
    
    if (!consensus.hasConsensus) {
      throw new Error('Cannot create consensus proof: keypairs do not share centroid');
    }
    
    // Create multi-signature proof
    const signatures = keypairs.map(kp => {
      const proof: CentroidProof = JSON.parse(kp.proof);
      return {
        vertexIndex: kp.vertexIndex,
        signature: this.signMessage(kp.privateKey, message)
      };
    });
    
    return JSON.stringify({
      consensusCentroid: consensus.consensusCentroid,
      consensusVertices: consensus.consensusVertices,
      message,
      signatures,
      timestamp: Date.now()
    });
  }
  
  /**
   * Verify distributed consensus proof
   */
  static verifyDistributedConsensusProof(proofString: string, keypairs: CentroidKeypair[]): boolean {
    try {
      const proof = JSON.parse(proofString);
      
      // Verify all required signatures are present
      if (proof.signatures.length !== keypairs.length) {
        return false;
      }
      
      // Verify each signature
      for (let i = 0; i < keypairs.length; i++) {
        const keypair = keypairs[i];
        const signature = proof.signatures.find((s: any) => s.vertexIndex === keypair.vertexIndex);
        
        if (!signature) {
          return false;
        }
        
        const isValid = this.verifySignature(
          keypair.publicKey,
          proof.message,
          signature.signature
        );
        
        if (!isValid) {
          return false;
        }
      }
      
      return true;
      
    } catch (error) {
      console.error('Error verifying consensus proof:', error);
      return false;
    }
  }
}