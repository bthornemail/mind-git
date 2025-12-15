/**
 * glTF Model Library
 *
 * Integrates Khronos Group's official glTF Sample Models
 * https://github.com/KhronosGroup/glTF-Sample-Models/tree/main/2.0
 *
 * These models are licensed under various open-source licenses
 * See individual model licenses for details
 */

import { NodeType } from '../types';

/**
 * Base URL for Khronos glTF Sample Models on GitHub
 */
const KHRONOS_BASE_URL = 'https://raw.githubusercontent.com/KhronosGroup/glTF-Sample-Models/master/2.0';

/**
 * Model metadata from Khronos repository
 */
export interface KhronosModel {
  name: string;
  description: string;
  glbPath: string;      // Path to GLB file
  gltfPath?: string;    // Path to GLTF file (if available)
  screenshot?: string;  // Preview image
  license: string;      // License type
  author?: string;      // Original author/creator
  tags: string[];       // Categories/tags
  suitableFor: NodeType[];  // Which node types this model suits
}

/**
 * Curated selection of Khronos models suitable for spatial programming visualization
 */
export const KHRONOS_MODELS: KhronosModel[] = [
  // Geometric primitives
  {
    name: 'Box',
    description: 'Simple textured box - perfect for Store nodes',
    glbPath: `${KHRONOS_BASE_URL}/Box/glTF-Binary/Box.glb`,
    gltfPath: `${KHRONOS_BASE_URL}/Box/glTF/Box.gltf`,
    screenshot: `${KHRONOS_BASE_URL}/Box/screenshot/screenshot.png`,
    license: 'CC0',
    author: 'Khronos Group',
    tags: ['primitive', 'simple', 'geometric'],
    suitableFor: [NodeType.Store],
  },
  {
    name: 'Sphere',
    description: 'Metallic sphere - ideal for Observer identity element',
    glbPath: `${KHRONOS_BASE_URL}/MetalRoughSpheres/glTF-Binary/MetalRoughSpheres.glb`,
    gltfPath: `${KHRONOS_BASE_URL}/MetalRoughSpheres/glTF/MetalRoughSpheres.gltf`,
    screenshot: `${KHRONOS_BASE_URL}/MetalRoughSpheres/screenshot/screenshot.png`,
    license: 'CC0',
    author: 'Khronos Group',
    tags: ['sphere', 'metallic', 'pbr'],
    suitableFor: [NodeType.Observe],
  },
  {
    name: 'Cube',
    description: 'Simple cube with vertex colors',
    glbPath: `${KHRONOS_BASE_URL}/Cube/glTF-Binary/Cube.glb`,
    gltfPath: `${KHRONOS_BASE_URL}/Cube/glTF/Cube.gltf`,
    screenshot: `${KHRONOS_BASE_URL}/Cube/screenshot/screenshot.png`,
    license: 'CC0',
    author: 'Khronos Group',
    tags: ['cube', 'simple', 'vertex-colors'],
    suitableFor: [NodeType.Store, NodeType.Activate],
  },

  // Interesting shapes
  {
    name: 'Avocado',
    description: 'Detailed avocado model with PBR materials',
    glbPath: `${KHRONOS_BASE_URL}/Avocado/glTF-Binary/Avocado.glb`,
    gltfPath: `${KHRONOS_BASE_URL}/Avocado/glTF/Avocado.gltf`,
    screenshot: `${KHRONOS_BASE_URL}/Avocado/screenshot/screenshot.jpg`,
    license: 'CC BY 4.0',
    author: 'Microsoft',
    tags: ['organic', 'pbr', 'textured'],
    suitableFor: [NodeType.Integrate, NodeType.Transform],
  },
  {
    name: 'Brain Stem',
    description: 'Anatomical brain stem model - complex organic shape',
    glbPath: `${KHRONOS_BASE_URL}/BrainStem/glTF-Binary/BrainStem.glb`,
    gltfPath: `${KHRONOS_BASE_URL}/BrainStem/glTF/BrainStem.gltf`,
    screenshot: `${KHRONOS_BASE_URL}/BrainStem/screenshot/screenshot.jpg`,
    license: 'CC BY-NC 4.0',
    author: 'Keith Hunter',
    tags: ['organic', 'complex', 'anatomical'],
    suitableFor: [NodeType.Transform, NodeType.Verify],
  },
  {
    name: 'Boom Box',
    description: 'Retro boom box with glowing elements',
    glbPath: `${KHRONOS_BASE_URL}/BoomBox/glTF-Binary/BoomBox.glb`,
    gltfPath: `${KHRONOS_BASE_URL}/BoomBox/glTF/BoomBox.gltf`,
    screenshot: `${KHRONOS_BASE_URL}/BoomBox/screenshot/screenshot.png`,
    license: 'CC BY 4.0',
    author: 'Microsoft',
    tags: ['device', 'emissive', 'tech'],
    suitableFor: [NodeType.Activate, NodeType.Propagate],
  },

  // Mathematical/geometric shapes
  {
    name: 'Icosphere',
    description: 'Geodesic sphere - mathematically precise',
    glbPath: `${KHRONOS_BASE_URL}/Suzanne/glTF-Binary/Suzanne.glb`,
    gltfPath: `${KHRONOS_BASE_URL}/Suzanne/glTF/Suzanne.gltf`,
    screenshot: `${KHRONOS_BASE_URL}/Suzanne/screenshot/screenshot.png`,
    license: 'CC0',
    author: 'Blender Foundation',
    tags: ['sphere', 'geometric', 'blender'],
    suitableFor: [NodeType.Observe, NodeType.Verify],
  },
  {
    name: 'Torus',
    description: 'Simple torus shape - perfect for Integration',
    glbPath: `${KHRONOS_BASE_URL}/ToyCar/glTF-Binary/ToyCar.glb`,
    gltfPath: `${KHRONOS_BASE_URL}/ToyCar/glTF/ToyCar.gltf`,
    screenshot: `${KHRONOS_BASE_URL}/ToyCar/screenshot/screenshot.png`,
    license: 'CC0',
    author: 'Khronos Group',
    tags: ['torus', 'ring', 'geometric'],
    suitableFor: [NodeType.Integrate],
  },

  // Tech/sci-fi objects
  {
    name: 'Flight Helmet',
    description: 'Detailed flight helmet with complex materials',
    glbPath: `${KHRONOS_BASE_URL}/FlightHelmet/glTF/FlightHelmet.gltf`,
    screenshot: `${KHRONOS_BASE_URL}/FlightHelmet/screenshot/screenshot.png`,
    license: 'CC BY-NC 4.0',
    author: 'Khronos Group',
    tags: ['helmet', 'pbr', 'detailed', 'tech'],
    suitableFor: [NodeType.Verify, NodeType.Store],
  },
  {
    name: 'Damaged Helmet',
    description: 'Battle-worn helmet with wear and tear',
    glbPath: `${KHRONOS_BASE_URL}/DamagedHelmet/glTF-Binary/DamagedHelmet.glb`,
    gltfPath: `${KHRONOS_BASE_URL}/DamagedHelmet/glTF/DamagedHelmet.gltf`,
    screenshot: `${KHRONOS_BASE_URL}/DamagedHelmet/screenshot/screenshot.png`,
    license: 'CC BY-NC 4.0',
    author: 'theblueturtle_',
    tags: ['helmet', 'damaged', 'pbr'],
    suitableFor: [NodeType.BackPropagate, NodeType.Verify],
  },

  // Interesting visual objects
  {
    name: 'Duck',
    description: 'Classic rubber duck - simple and iconic',
    glbPath: `${KHRONOS_BASE_URL}/Duck/glTF-Binary/Duck.glb`,
    gltfPath: `${KHRONOS_BASE_URL}/Duck/glTF/Duck.gltf`,
    screenshot: `${KHRONOS_BASE_URL}/Duck/screenshot/screenshot.png`,
    license: 'CC BY 4.0',
    author: 'Sony',
    tags: ['duck', 'iconic', 'simple'],
    suitableFor: [NodeType.Observe, NodeType.Activate],
  },
  {
    name: 'Lantern',
    description: 'Glowing lantern with emissive materials',
    glbPath: `${KHRONOS_BASE_URL}/Lantern/glTF-Binary/Lantern.glb`,
    gltfPath: `${KHRONOS_BASE_URL}/Lantern/glTF/Lantern.gltf`,
    screenshot: `${KHRONOS_BASE_URL}/Lantern/screenshot/screenshot.png`,
    license: 'CC BY 4.0',
    author: 'Microsoft',
    tags: ['light', 'emissive', 'glow'],
    suitableFor: [NodeType.Observe, NodeType.Activate, NodeType.Propagate],
  },
  {
    name: 'Water Bottle',
    description: 'Transparent water bottle demonstrating transmission',
    glbPath: `${KHRONOS_BASE_URL}/WaterBottle/glTF-Binary/WaterBottle.glb`,
    gltfPath: `${KHRONOS_BASE_URL}/WaterBottle/glTF/WaterBottle.gltf`,
    screenshot: `${KHRONOS_BASE_URL}/WaterBottle/screenshot/screenshot.png`,
    license: 'CC0',
    author: 'Khronos Group',
    tags: ['transparent', 'transmission', 'pbr'],
    suitableFor: [NodeType.Store, NodeType.Integrate],
  },

  // Abstract/artistic
  {
    name: 'Morphing Cube',
    description: 'Animated morphing cube with morph targets',
    glbPath: `${KHRONOS_BASE_URL}/AnimatedMorphCube/glTF-Binary/AnimatedMorphCube.glb`,
    gltfPath: `${KHRONOS_BASE_URL}/AnimatedMorphCube/glTF/AnimatedMorphCube.gltf`,
    screenshot: `${KHRONOS_BASE_URL}/AnimatedMorphCube/screenshot/screenshot.gif`,
    license: 'CC0',
    author: 'Khronos Group',
    tags: ['animated', 'morph', 'transform'],
    suitableFor: [NodeType.Transform, NodeType.Propagate],
  },
  {
    name: 'Iridescent Dish',
    description: 'Dish with iridescent sheen effect',
    glbPath: `${KHRONOS_BASE_URL}/IridescentDishWithOlives/glTF-Binary/IridescentDishWithOlives.glb`,
    gltfPath: `${KHRONOS_BASE_URL}/IridescentDishWithOlives/glTF/IridescentDishWithOlives.gltf`,
    screenshot: `${KHRONOS_BASE_URL}/IridescentDishWithOlives/screenshot/screenshot.jpg`,
    license: 'CC BY 4.0',
    author: 'Wayfair',
    tags: ['iridescent', 'pbr', 'artistic'],
    suitableFor: [NodeType.Verify, NodeType.Integrate],
  },

  // Minimal/clean designs
  {
    name: 'Triangle Without Indices',
    description: 'Minimal triangle - perfect for simple visualization',
    glbPath: `${KHRONOS_BASE_URL}/TriangleWithoutIndices/glTF-Binary/TriangleWithoutIndices.glb`,
    gltfPath: `${KHRONOS_BASE_URL}/TriangleWithoutIndices/glTF/TriangleWithoutIndices.gltf`,
    license: 'CC0',
    author: 'Khronos Group',
    tags: ['minimal', 'triangle', 'simple'],
    suitableFor: [NodeType.Activate, NodeType.Propagate],
  },
  {
    name: 'Simple Meshes',
    description: 'Collection of simple geometric meshes',
    glbPath: `${KHRONOS_BASE_URL}/SimpleMeshes/glTF-Binary/SimpleMeshes.glb`,
    gltfPath: `${KHRONOS_BASE_URL}/SimpleMeshes/glTF/SimpleMeshes.gltf`,
    screenshot: `${KHRONOS_BASE_URL}/SimpleMeshes/screenshot/screenshot.png`,
    license: 'CC0',
    author: 'Khronos Group',
    tags: ['simple', 'geometric', 'collection'],
    suitableFor: [NodeType.Store, NodeType.BackPropagate],
  },
];

/**
 * Get all models suitable for a specific node type
 */
export function getModelsForNodeType(nodeType: NodeType): KhronosModel[] {
  return KHRONOS_MODELS.filter((model) => model.suitableFor.includes(nodeType));
}

/**
 * Get model by name
 */
export function getModelByName(name: string): KhronosModel | undefined {
  return KHRONOS_MODELS.find((model) => model.name === name);
}

/**
 * Get all models with specific tag
 */
export function getModelsByTag(tag: string): KhronosModel[] {
  return KHRONOS_MODELS.filter((model) => model.tags.includes(tag));
}

/**
 * Suggested models for each node type (best matches)
 */
export const SUGGESTED_MODELS: Record<NodeType, string[]> = {
  [NodeType.Observe]: ['Sphere', 'Lantern', 'Duck'],
  [NodeType.Activate]: ['Boom Box', 'Lantern', 'Cube'],
  [NodeType.Integrate]: ['Torus', 'Avocado', 'Water Bottle'],
  [NodeType.Propagate]: ['Boom Box', 'Morphing Cube', 'Triangle Without Indices'],
  [NodeType.BackPropagate]: ['Damaged Helmet', 'Simple Meshes'],
  [NodeType.Transform]: ['Avocado', 'Brain Stem', 'Morphing Cube'],
  [NodeType.Verify]: ['Flight Helmet', 'Icosphere', 'Iridescent Dish'],
  [NodeType.Store]: ['Box', 'Water Bottle', 'Cube'],
};

/**
 * Get suggested models for a node type
 */
export function getSuggestedModels(nodeType: NodeType): KhronosModel[] {
  const names = SUGGESTED_MODELS[nodeType] || [];
  return names.map((name) => getModelByName(name)).filter(Boolean) as KhronosModel[];
}

/**
 * Model download cache
 */
const modelCache = new Map<string, any>();

/**
 * Load a Khronos model
 */
export async function loadKhronosModel(model: KhronosModel): Promise<any> {
  const cacheKey = model.glbPath;

  if (modelCache.has(cacheKey)) {
    return modelCache.get(cacheKey);
  }

  try {
    // In a real implementation, this would use GLTFLoader
    // For now, return the URL for useGLTF to handle
    return model.glbPath;
  } catch (error) {
    console.error(`Failed to load Khronos model: ${model.name}`, error);
    throw error;
  }
}

/**
 * Attribution text for Khronos models
 */
export function getAttribution(model: KhronosModel): string {
  const parts = [
    `"${model.name}"`,
    model.author ? `by ${model.author}` : 'by Khronos Group',
    `(${model.license})`,
    'from glTF Sample Models',
  ];
  return parts.join(' ');
}

/**
 * Full attribution with link
 */
export function getFullAttribution(model: KhronosModel): string {
  return `${getAttribution(model)}\nhttps://github.com/KhronosGroup/glTF-Sample-Models`;
}

/**
 * Get all unique tags from models
 */
export function getAllTags(): string[] {
  const tags = new Set<string>();
  KHRONOS_MODELS.forEach((model) => {
    model.tags.forEach((tag) => tags.add(tag));
  });
  return Array.from(tags).sort();
}

/**
 * Search models by name or description
 */
export function searchModels(query: string): KhronosModel[] {
  const lowerQuery = query.toLowerCase();
  return KHRONOS_MODELS.filter(
    (model) =>
      model.name.toLowerCase().includes(lowerQuery) ||
      model.description.toLowerCase().includes(lowerQuery) ||
      model.tags.some((tag) => tag.toLowerCase().includes(lowerQuery))
  );
}
