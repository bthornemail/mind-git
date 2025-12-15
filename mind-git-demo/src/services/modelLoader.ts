/**
 * GLTF/GLB Model Loader Service
 *
 * Handles loading and caching of 3D models for different node types
 * Supports both GLTF (JSON, human-readable) and GLB (binary, efficient) formats
 */

import { NodeType } from '../types';

/**
 * Model configuration for each node type
 */
export interface ModelConfig {
  path?: string;           // Path to GLTF/GLB file
  scale?: number;          // Scale multiplier
  rotation?: [number, number, number];  // Euler angles in radians
  useProcedural?: boolean; // Use procedurally generated geometry
}

/**
 * Default model paths for each node type
 * You can replace these with custom GLTF/GLB files
 */
export const MODEL_PATHS: Record<NodeType, ModelConfig> = {
  [NodeType.Observe]: {
    path: '/models/observe.glb',
    scale: 1.0,
    useProcedural: true,
  },
  [NodeType.Activate]: {
    path: '/models/activate.glb',
    scale: 1.0,
    useProcedural: true,
  },
  [NodeType.Integrate]: {
    path: '/models/integrate.glb',
    scale: 1.0,
    useProcedural: true,
  },
  [NodeType.Propagate]: {
    path: '/models/propagate.glb',
    scale: 1.0,
    useProcedural: true,
  },
  [NodeType.BackPropagate]: {
    path: '/models/backpropagate.glb',
    scale: 1.0,
    useProcedural: true,
  },
  [NodeType.Transform]: {
    path: '/models/transform.glb',
    scale: 1.0,
    useProcedural: true,
  },
  [NodeType.Verify]: {
    path: '/models/verify.glb',
    scale: 1.0,
    useProcedural: true,
  },
  [NodeType.Store]: {
    path: '/models/store.glb',
    scale: 1.0,
    useProcedural: true,
  },
};

/**
 * Procedural geometry generators for each node type
 * These create mathematically meaningful shapes when custom models aren't available
 */
export const PROCEDURAL_GEOMETRIES = {
  [NodeType.Observe]: 'sphere',        // Sphere - perfect symmetry for identity
  [NodeType.Activate]: 'pyramid',      // Pyramid - pointing upward (activation)
  [NodeType.Integrate]: 'torus',       // Torus - addition/integration
  [NodeType.Propagate]: 'cone',        // Cone - directional propagation
  [NodeType.BackPropagate]: 'inverseCone', // Inverted cone - backward flow
  [NodeType.Transform]: 'octahedron',  // Octahedron - 8 faces (8D octonions)
  [NodeType.Verify]: 'dodecahedron',   // Dodecahedron - verification (12 faces)
  [NodeType.Store]: 'box',             // Box - storage container
};

/**
 * Generate GLTF JSON structure procedurally
 * This creates a valid GLTF 2.0 file structure in memory
 */
export function generateProceduralGLTF(nodeType: NodeType, color: string): any {
  const geometry = PROCEDURAL_GEOMETRIES[nodeType];

  // Base GLTF 2.0 structure
  const gltf = {
    asset: {
      version: '2.0',
      generator: 'mind-git procedural generator',
    },
    scene: 0,
    scenes: [
      {
        nodes: [0],
      },
    ],
    nodes: [
      {
        mesh: 0,
        name: `${nodeType}_node`,
      },
    ],
    meshes: [
      {
        primitives: [
          {
            attributes: {
              POSITION: 0,
              NORMAL: 1,
            },
            indices: 2,
            material: 0,
          },
        ],
      },
    ],
    materials: [
      {
        pbrMetallicRoughness: {
          baseColorFactor: hexToRgba(color),
          metallic: 0.2,
          roughness: 0.4,
        },
        name: `${nodeType}_material`,
      },
    ],
    accessors: [],
    bufferViews: [],
    buffers: [],
  };

  return gltf;
}

/**
 * Convert hex color to RGBA array for GLTF
 */
function hexToRgba(hex: string): [number, number, number, number] {
  const result = /^#?([a-f\d]{2})([a-f\d]{2})([a-f\d]{2})$/i.exec(hex);
  if (!result) return [1, 1, 1, 1];

  return [
    parseInt(result[1], 16) / 255,
    parseInt(result[2], 16) / 255,
    parseInt(result[3], 16) / 255,
    1.0,
  ];
}

/**
 * Export scene as GLTF JSON (human-readable)
 * Useful for debugging and custom model creation
 */
export function exportAsGLTF(scene: any): string {
  const gltf = generateSceneGLTF(scene);
  return JSON.stringify(gltf, null, 2);
}

/**
 * Export scene as GLB binary (efficient)
 * Better for production use - smaller file size
 */
export function exportAsGLB(scene: any): ArrayBuffer {
  const gltf = generateSceneGLTF(scene);
  return gltfToGLB(gltf);
}

/**
 * Generate complete GLTF structure from scene
 */
function generateSceneGLTF(scene: any): any {
  // This would contain the full scene export logic
  // For now, return a minimal valid GLTF
  return {
    asset: {
      version: '2.0',
      generator: 'mind-git visualizer',
    },
    scene: 0,
    scenes: [{ nodes: [0] }],
    nodes: [{ mesh: 0 }],
    meshes: [],
  };
}

/**
 * Convert GLTF JSON to GLB binary format
 * GLB = 12-byte header + JSON chunk + BIN chunk
 */
function gltfToGLB(gltf: any): ArrayBuffer {
  const jsonString = JSON.stringify(gltf);
  const jsonBuffer = new TextEncoder().encode(jsonString);

  // Align to 4-byte boundary
  const jsonLength = jsonBuffer.length;
  const jsonPadding = (4 - (jsonLength % 4)) % 4;
  const jsonPaddedLength = jsonLength + jsonPadding;

  // GLB header: magic, version, length
  const headerLength = 12;
  const jsonChunkHeaderLength = 8;
  const totalLength = headerLength + jsonChunkHeaderLength + jsonPaddedLength;

  const glb = new ArrayBuffer(totalLength);
  const view = new DataView(glb);

  // Write GLB header
  view.setUint32(0, 0x46546C67, true); // 'glTF' magic
  view.setUint32(4, 2, true);          // version 2
  view.setUint32(8, totalLength, true); // total length

  // Write JSON chunk header
  view.setUint32(12, jsonPaddedLength, true); // chunk length
  view.setUint32(16, 0x4E4F534A, true);       // 'JSON' chunk type

  // Write JSON data
  const jsonView = new Uint8Array(glb, 20, jsonLength);
  jsonView.set(jsonBuffer);

  // Pad with spaces (0x20)
  for (let i = 0; i < jsonPadding; i++) {
    view.setUint8(20 + jsonLength + i, 0x20);
  }

  return glb;
}

/**
 * Model cache to avoid reloading
 */
const modelCache = new Map<string, any>();

/**
 * Preload all models for better performance
 */
export function preloadModels() {
  Object.entries(MODEL_PATHS).forEach(([nodeType, config]) => {
    if (config.path && !config.useProcedural) {
      // Trigger model loading (will be cached)
      fetch(config.path).catch(() => {
        console.warn(`Failed to preload model for ${nodeType}, will use procedural`);
      });
    }
  });
}

/**
 * Get model configuration for a node type
 */
export function getModelConfig(nodeType: NodeType): ModelConfig {
  return MODEL_PATHS[nodeType] || { useProcedural: true };
}

/**
 * Check if a custom model exists for a node type
 */
export async function hasCustomModel(nodeType: NodeType): Promise<boolean> {
  const config = MODEL_PATHS[nodeType];
  if (!config.path || config.useProcedural) return false;

  try {
    const response = await fetch(config.path, { method: 'HEAD' });
    return response.ok;
  } catch {
    return false;
  }
}
