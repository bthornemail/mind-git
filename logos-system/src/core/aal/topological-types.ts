// Topological Dimensions for Polytope-Based Semantic Computation
// Extends existing AAL type system with Platonic and Archimedean solids

import { AALType } from './types';

export enum TopologicalDimension {
  // Existing AAL Dimensions (D0-D10)
  D0_Activate = 0,
  D1_Integrate = 1,
  D2_Propagate = 2,
  D3_BackPropagate = 3,
  D4_Transform = 4,
  D5_Verify = 5,
  D6_Store = 6,
  D7_Observe = 7,
  D8_HigherOrder1 = 8,
  D9_HigherOrder2 = 9,
  D10_HigherOrder3 = 10,
  
  // NEW: Topological Dimensions for Polytope Spaces
  D11_TetrahedralSpace = 11,    // 4 vertices - Foundational operations
  D12_CubicSpace = 12,          // 8 vertices - Operational dimensions  
  D13_OctahedralSpace = 13,     // 6 vertices - Dual perspectives
  D14_DodecahedralSpace = 14,   // 20 vertices - Categorical knowledge
  D15_IcosahedralSpace = 15,     // 12 vertices - Connection framework
  
  // 4D Regular Polytopes
  D16_FiveCell = 16,            // 5 vertices - Minimal 4D reasoning
  D17_SixteenCell = 17,        // 8 vertices - Dual 4D perspectives
  D18_TwentyFourCell = 18,      // 24 vertices - Self-dual knowledge
  D19_OneTwentyCell = 19,       // 600 vertices - Extended semantic field
  D20_SixHundredCell = 20,      // 120 vertices - Inverted field
  
  // Archimedean Transformations
  D21_TruncatedSpace = 21,      // Truncated polytopes
  D22_SnubSpace = 22,          // Chiral transformations
  D23_DualSpace = 23,           // Vertex-face duality
}

export interface TopologicalType extends AALType {
  dimension: TopologicalDimension;
  polytope: PolytopeType;
  vertices: string[];
  eulerCharacteristic: number;
  symmetryGroup: string;
}

export enum PolytopeType {
  // Platonic Solids
  TETRAHEDRON = 'tetrahedron',      // V=4, E=6, F=4, χ=2
  CUBE = 'cube',                    // V=8, E=12, F=6, χ=2
  OCTAHEDRON = 'octahedron',        // V=6, E=12, F=8, χ=2
  DODECAHEDRON = 'dodecahedron',    // V=20, E=30, F=12, χ=2
  ICOSAHEDRON = 'icosahedron',      // V=12, E=30, F=20, χ=2
  
  // 4D Regular Polytopes
  FIVE_CELL = '5-cell',             // V=5, E=10, F=10, C=5
  SIXTEEN_CELL = '16-cell',         // V=8, E=24, F=32, C=16
  TWENTY_FOUR_CELL = '24-cell',     // V=24, E=96, F=96, C=24
  ONE_TWENTY_CELL = '120-cell',     // V=600, E=1200, F=720, C=120
  SIX_HUNDRED_CELL = '600-cell',    // V=120, E=720, F=1200, C=600
  
  // Archimedean Solids
  TRUNCATED_TETRAHEDRON = 'truncated-tetrahedron',
  TRUNCATED_CUBE = 'truncated-cube',
  TRUNCATED_OCTAHEDRON = 'truncated-octahedron',
  TRUNCATED_DODECAHEDRON = 'truncated-dodecahedron',
  TRUNCATED_ICOSAHEDRON = 'truncated-icosahedron',
  CUBOCTAHEDRON = 'cuboctahedron',
  ICOSIDODECAHEDRON = 'icosidodecahedron',
  RHOMBICUBOCTAHEDRON = 'rhombicuboctahedron',
  TRUNCATED_CUBOCTAHEDRON = 'truncated-cuboctahedron',
  TRUNCATED_ICOSIDODECAHEDRON = 'truncated-icosidodecahedron',
  SNUB_CUBE = 'snub-cube',
  SNUB_DODECAHEDRON = 'snub-dodecahedron',
}

export interface PolytopeProperties {
  type: PolytopeType;
  vertices: number;
  edges: number;
  faces: number;
  cells?: number; // For 4D polytopes
  eulerCharacteristic: number;
  symmetryGroup: string;
  dual?: PolytopeType;
  vertexConfiguration?: string;
}

// Polytope Property Database
export const POLYTOPE_PROPERTIES: Record<PolytopeType, PolytopeProperties> = {
  [PolytopeType.TETRAHEDRON]: {
    type: PolytopeType.TETRAHEDRON,
    vertices: 4,
    edges: 6,
    faces: 4,
    eulerCharacteristic: 2,
    symmetryGroup: 'A4',
    vertexConfiguration: '3.3.3'
  },
  [PolytopeType.CUBE]: {
    type: PolytopeType.CUBE,
    vertices: 8,
    edges: 12,
    faces: 6,
    eulerCharacteristic: 2,
    symmetryGroup: 'S4×C2',
    vertexConfiguration: '4.4.4',
    dual: PolytopeType.OCTAHEDRON
  },
  [PolytopeType.OCTAHEDRON]: {
    type: PolytopeType.OCTAHEDRON,
    vertices: 6,
    edges: 12,
    faces: 8,
    eulerCharacteristic: 2,
    symmetryGroup: 'S4×C2',
    vertexConfiguration: '3.3.3.3',
    dual: PolytopeType.CUBE
  },
  [PolytopeType.DODECAHEDRON]: {
    type: PolytopeType.DODECAHEDRON,
    vertices: 20,
    edges: 30,
    faces: 12,
    eulerCharacteristic: 2,
    symmetryGroup: 'A5×C2',
    vertexConfiguration: '5.5.5',
    dual: PolytopeType.ICOSAHEDRON
  },
  [PolytopeType.ICOSAHEDRON]: {
    type: PolytopeType.ICOSAHEDRON,
    vertices: 12,
    edges: 30,
    faces: 20,
    eulerCharacteristic: 2,
    symmetryGroup: 'A5×C2',
    vertexConfiguration: '3.3.3.3.3',
    dual: PolytopeType.DODECAHEDRON
  },
  // 4D Polytopes
  [PolytopeType.FIVE_CELL]: {
    type: PolytopeType.FIVE_CELL,
    vertices: 5,
    edges: 10,
    faces: 10,
    cells: 5,
    eulerCharacteristic: 0, // 4D Euler characteristic: V - E + F - C = 0
    symmetryGroup: 'A5'
  },
  [PolytopeType.SIXTEEN_CELL]: {
    type: PolytopeType.SIXTEEN_CELL,
    vertices: 8,
    edges: 24,
    faces: 32,
    cells: 16,
    eulerCharacteristic: 0,
    symmetryGroup: 'B4',
    dual: PolytopeType.TWENTY_FOUR_CELL
  },
  [PolytopeType.TWENTY_FOUR_CELL]: {
    type: PolytopeType.TWENTY_FOUR_CELL,
    vertices: 24,
    edges: 96,
    faces: 96,
    cells: 24,
    eulerCharacteristic: 0,
    symmetryGroup: 'F4',
    dual: PolytopeType.SIXTEEN_CELL
  },
  [PolytopeType.ONE_TWENTY_CELL]: {
    type: PolytopeType.ONE_TWENTY_CELL,
    vertices: 600,
    edges: 1200,
    faces: 720,
    cells: 120,
    eulerCharacteristic: 0,
    symmetryGroup: 'H4',
    dual: PolytopeType.SIX_HUNDRED_CELL
  },
  [PolytopeType.SIX_HUNDRED_CELL]: {
    type: PolytopeType.SIX_HUNDRED_CELL,
    vertices: 120,
    edges: 720,
    faces: 1200,
    cells: 600,
    eulerCharacteristic: 0,
    symmetryGroup: 'H4',
    dual: PolytopeType.ONE_TWENTY_CELL
  }
};

// Dodecahedron Semantic Primes (20 vertices)
export const DODECAHEDRON_SEMANTIC_PRIMES = [
  'quasar', 'ephemeral', 'catalyst', 'nexus', 'liminal',
  'resonance', 'mycelium', 'fractal', 'threshold', 'emanate',
  'confluence', 'sonder', 'umbra', 'tessellate', 'prismatic',
  'oscillate', 'cascade', 'dialectic', 'emergence', 'entangle'
];

// Tetrahedron Foundational Operations (4 vertices)
export const TETRAHEDRON_OPERATIONS = [
  'observe', 'activate', 'integrate', 'propagate'
];

// Cube Operational Dimensions (8 vertices)
export const CUBE_OPERATIONS = [
  'query', 'store', 'verify', 'learn', 'share', 'adapt', 'emerge', 'reflect'
];

// Icosahedron Connection Types (12 vertices)
export const ICOSAHEDRON_CONNECTIONS = [
  'subject', 'object', 'cause', 'effect', 'local', 'global',
  'temporal', 'spatial', 'abstract', 'concrete', 'simple', 'complex'
];

export class TopologicalTypeSystem {
  /**
   * Create a topological type for a given polytope
   */
  static createTopologicalType(
    polytope: PolytopeType,
    vertices: string[],
    additionalProperties: any[] = []
  ): TopologicalType {
    const props = POLYTOPE_PROPERTIES[polytope];
    const dimension = this.getDimensionForPolytope(polytope);
    
    return {
      type: 'topological',
      dimension,
      polytope,
      vertices,
      eulerCharacteristic: props.eulerCharacteristic,
      symmetryGroup: props.symmetryGroup,
      properties: additionalProperties
    };
  }
  
  /**
   * Get the AAL dimension for a given polytope
   */
  static getDimensionForPolytope(polytope: PolytopeType): TopologicalDimension {
    switch (polytope) {
      case PolytopeType.TETRAHEDRON:
        return TopologicalDimension.D11_TetrahedralSpace;
      case PolytopeType.CUBE:
        return TopologicalDimension.D12_CubicSpace;
      case PolytopeType.OCTAHEDRON:
        return TopologicalDimension.D13_OctahedralSpace;
      case PolytopeType.DODECAHEDRON:
        return TopologicalDimension.D14_DodecahedralSpace;
      case PolytopeType.ICOSAHEDRON:
        return TopologicalDimension.D15_IcosahedralSpace;
      case PolytopeType.FIVE_CELL:
        return TopologicalDimension.D16_FiveCell;
      case PolytopeType.SIXTEEN_CELL:
        return TopologicalDimension.D17_SixteenCell;
      case PolytopeType.TWENTY_FOUR_CELL:
        return TopologicalDimension.D18_TwentyFourCell;
      case PolytopeType.ONE_TWENTY_CELL:
        return TopologicalDimension.D19_OneTwentyCell;
      case PolytopeType.SIX_HUNDRED_CELL:
        return TopologicalDimension.D20_SixHundredCell;
      default:
        throw new Error(`Unsupported polytope type: ${polytope}`);
    }
  }
  
  /**
   * Verify Euler characteristic for a polytope
   * V - E + F = 2 for 3D polytopes
   * V - E + F - C = 0 for 4D polytopes
   */
  static verifyEulerCharacteristic(polytope: PolytopeType): boolean {
    const props = POLYTOPE_PROPERTIES[polytope];
    
    if (props.cells !== undefined) {
      // 4D polytope: V - E + F - C = 0
      return props.vertices - props.edges + props.faces - props.cells === props.eulerCharacteristic;
    } else {
      // 3D polytope: V - E + F = 2
      return props.vertices - props.edges + props.faces === props.eulerCharacteristic;
    }
  }
  
  /**
   * Get semantic vertices for a polytope
   */
  static getSemanticVertices(polytope: PolytopeType): string[] {
    switch (polytope) {
      case PolytopeType.DODECAHEDRON:
        return DODECAHEDRON_SEMANTIC_PRIMES;
      case PolytopeType.TETRAHEDRON:
        return TETRAHEDRON_OPERATIONS;
      case PolytopeType.CUBE:
        return CUBE_OPERATIONS;
      case PolytopeType.ICOSAHEDRON:
        return ICOSAHEDRON_CONNECTIONS;
      default:
        throw new Error(`No semantic vertices defined for polytope: ${polytope}`);
    }
  }
  
  /**
   * Create a dodecahedron type with semantic primes
   */
  static createDodecahedronType(): TopologicalType {
    return this.createTopologicalType(
      PolytopeType.DODECAHEDRON,
      DODECAHEDRON_SEMANTIC_PRIMES,
      ['semantic-knowledge', 'categorical-reasoning', 'pentagonal-logic']
    );
  }
  
  /**
   * Create a tetrahedron type with foundational operations
   */
  static createTetrahedronType(): TopologicalType {
    return this.createTopologicalType(
      PolytopeType.TETRAHEDRON,
      TETRAHEDRON_OPERATIONS,
      ['foundational-operations', 'minimal-logic', 'triangular-reasoning']
    );
  }
  
  /**
   * Create a cube type with operational dimensions
   */
  static createCubeType(): TopologicalType {
    return this.createTopologicalType(
      PolytopeType.CUBE,
      CUBE_OPERATIONS,
      ['operational-dimensions', 'cubic-logic', 'binary-structure']
    );
  }
  
  /**
   * Get dual polytope relationship
   */
  static getDualPolytope(polytope: PolytopeType): PolytopeType | null {
    const props = POLYTOPE_PROPERTIES[polytope];
    return props.dual || null;
  }
  
  /**
   * Check if two polytopes are duals
   */
  static areDuals(polytope1: PolytopeType, polytope2: PolytopeType): boolean {
    return this.getDualPolytope(polytope1) === polytope2;
  }
}