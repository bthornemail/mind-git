/**
 * Procedural geometry components for different node types
 * Each geometry type has mathematical significance
 */

import React, { useRef } from 'react';
import { useGLTF } from '@react-three/drei';
import * as THREE from 'three';
import { NodeType } from '../types';
import { PROCEDURAL_GEOMETRIES } from '../services/modelLoader';

interface GeometryProps {
  nodeType: NodeType | null;
  color: string;
  width: number;
  height: number;
  depth: number;
  hovered: boolean;
  selected: boolean;
  onClick?: (e: any) => void;
  onPointerDown?: (e: any) => void;
  onPointerUp?: (e: any) => void;
  onPointerMove?: (e: any) => void;
  onPointerEnter?: () => void;
  onPointerLeave?: () => void;
  meshRef?: React.RefObject<THREE.Mesh | null>;
  customModelPath?: string;  // Path to custom GLTF/GLB model
}

/**
 * Main geometry selector component
 * Routes to appropriate geometry based on node type or custom model
 */
export const NodeGeometry: React.FC<GeometryProps> = (props) => {
  const { nodeType, customModelPath, ...otherProps } = props;

  // If custom model path is provided, use it
  if (customModelPath) {
    return <GLTFNode modelPath={customModelPath} nodeType={nodeType} {...otherProps} />;
  }

  // Otherwise use procedural geometry
  if (!nodeType) {
    return <BoxGeometry {...otherProps} />;
  }

  const geometryType = PROCEDURAL_GEOMETRIES[nodeType];

  switch (geometryType) {
    case 'sphere':
      return <SphereGeometry {...otherProps} />;
    case 'pyramid':
      return <PyramidGeometry {...otherProps} />;
    case 'torus':
      return <TorusGeometry {...otherProps} />;
    case 'cone':
      return <ConeGeometry {...otherProps} />;
    case 'inverseCone':
      return <InverseConeGeometry {...otherProps} />;
    case 'octahedron':
      return <OctahedronGeometry {...otherProps} />;
    case 'dodecahedron':
      return <DodecahedronGeometry {...otherProps} />;
    case 'box':
    default:
      return <BoxGeometry {...otherProps} />;
  }
};

/**
 * Box geometry - Storage (D6)
 * Simple rectangular container
 */
const BoxGeometry: React.FC<Omit<GeometryProps, 'nodeType'>> = ({
  color,
  width,
  height,
  depth,
  hovered,
  meshRef,
  ...handlers
}) => (
  <mesh ref={meshRef} {...handlers}>
    <boxGeometry args={[width, height, depth]} />
    <meshStandardMaterial
      color={color}
      emissive={hovered ? color : '#000000'}
      emissiveIntensity={hovered ? 0.3 : 0}
      metalness={0.2}
      roughness={0.4}
    />
  </mesh>
);

/**
 * Sphere geometry - Observer (D7)
 * Perfect symmetry representing identity element
 */
const SphereGeometry: React.FC<Omit<GeometryProps, 'nodeType'>> = ({
  color,
  width,
  height,
  hovered,
  meshRef,
  ...handlers
}) => {
  const radius = Math.max(width, height) / 2;
  return (
    <mesh ref={meshRef} {...handlers}>
      <sphereGeometry args={[radius, 32, 32]} />
      <meshStandardMaterial
        color={color}
        emissive={hovered ? color : '#000000'}
        emissiveIntensity={hovered ? 0.5 : 0}
        metalness={0.3}
        roughness={0.3}
      />
    </mesh>
  );
};

/**
 * Pyramid geometry - Activate (D0)
 * Pointing upward for activation/entry point
 */
const PyramidGeometry: React.FC<Omit<GeometryProps, 'nodeType'>> = ({
  color,
  width,
  height,
  hovered,
  meshRef,
  ...handlers
}) => {
  const size = Math.max(width, height);
  return (
    <mesh ref={meshRef} rotation={[0, 0, 0]} {...handlers}>
      <coneGeometry args={[size / 2, size, 4]} />
      <meshStandardMaterial
        color={color}
        emissive={hovered ? color : '#000000'}
        emissiveIntensity={hovered ? 0.3 : 0}
        metalness={0.2}
        roughness={0.4}
        flatShading
      />
    </mesh>
  );
};

/**
 * Torus geometry - Integrate (D1)
 * Ring shape representing addition/integration
 */
const TorusGeometry: React.FC<Omit<GeometryProps, 'nodeType'>> = ({
  color,
  width,
  height,
  hovered,
  meshRef,
  ...handlers
}) => {
  const radius = Math.max(width, height) / 3;
  const tube = radius * 0.4;
  return (
    <mesh ref={meshRef} rotation={[Math.PI / 2, 0, 0]} {...handlers}>
      <torusGeometry args={[radius, tube, 16, 32]} />
      <meshStandardMaterial
        color={color}
        emissive={hovered ? color : '#000000'}
        emissiveIntensity={hovered ? 0.3 : 0}
        metalness={0.4}
        roughness={0.3}
      />
    </mesh>
  );
};

/**
 * Cone geometry - Propagate (D2)
 * Directional shape for forward propagation
 */
const ConeGeometry: React.FC<Omit<GeometryProps, 'nodeType'>> = ({
  color,
  width,
  height,
  hovered,
  meshRef,
  ...handlers
}) => {
  const radius = Math.max(width, height) / 2.5;
  const coneHeight = height * 1.2;
  return (
    <mesh ref={meshRef} rotation={[0, 0, 0]} {...handlers}>
      <coneGeometry args={[radius, coneHeight, 32]} />
      <meshStandardMaterial
        color={color}
        emissive={hovered ? color : '#000000'}
        emissiveIntensity={hovered ? 0.3 : 0}
        metalness={0.25}
        roughness={0.4}
      />
    </mesh>
  );
};

/**
 * Inverted cone geometry - BackPropagate (D3)
 * Inverted cone for backward propagation
 */
const InverseConeGeometry: React.FC<Omit<GeometryProps, 'nodeType'>> = ({
  color,
  width,
  height,
  hovered,
  meshRef,
  ...handlers
}) => {
  const radius = Math.max(width, height) / 2.5;
  const coneHeight = height * 1.2;
  return (
    <mesh ref={meshRef} rotation={[0, 0, Math.PI]} {...handlers}>
      <coneGeometry args={[radius, coneHeight, 32]} />
      <meshStandardMaterial
        color={color}
        emissive={hovered ? color : '#000000'}
        emissiveIntensity={hovered ? 0.3 : 0}
        metalness={0.25}
        roughness={0.4}
      />
    </mesh>
  );
};

/**
 * Octahedron geometry - Transform (D4)
 * 8 faces representing 8-dimensional octonions
 * Perfect for transformation/multiplication operations
 */
const OctahedronGeometry: React.FC<Omit<GeometryProps, 'nodeType'>> = ({
  color,
  width,
  height,
  hovered,
  meshRef,
  ...handlers
}) => {
  const radius = Math.max(width, height) / 2;
  return (
    <mesh ref={meshRef} {...handlers}>
      <octahedronGeometry args={[radius, 0]} />
      <meshStandardMaterial
        color={color}
        emissive={hovered ? color : '#000000'}
        emissiveIntensity={hovered ? 0.4 : 0}
        metalness={0.5}
        roughness={0.2}
        flatShading
      />
    </mesh>
  );
};

/**
 * Dodecahedron geometry - Verify (D5)
 * 12 faces for verification/consensus
 */
const DodecahedronGeometry: React.FC<Omit<GeometryProps, 'nodeType'>> = ({
  color,
  width,
  height,
  hovered,
  meshRef,
  ...handlers
}) => {
  const radius = Math.max(width, height) / 2;
  return (
    <mesh ref={meshRef} {...handlers}>
      <dodecahedronGeometry args={[radius, 0]} />
      <meshStandardMaterial
        color={color}
        emissive={hovered ? color : '#000000'}
        emissiveIntensity={hovered ? 0.3 : 0}
        metalness={0.3}
        roughness={0.3}
        flatShading
      />
    </mesh>
  );
};

/**
 * GLTF Model Loader Component
 * Loads external GLTF/GLB files with fallback to procedural geometry
 */
interface GLTFNodeProps extends GeometryProps {
  modelPath: string;
}

export const GLTFNode: React.FC<GLTFNodeProps> = ({
  modelPath,
  nodeType,
  ...fallbackProps
}) => {
  try {
    const { scene } = useGLTF(modelPath);

    return (
      <primitive
        object={scene.clone()}
        {...fallbackProps}
      />
    );
  } catch (error) {
    console.warn(`Failed to load GLTF model: ${modelPath}, using procedural geometry`);
    return <NodeGeometry nodeType={nodeType} {...fallbackProps} />;
  }
};

// Preload GLTF models (optional, improves performance)
export function preloadGLTFModels(paths: string[]) {
  paths.forEach((path) => {
    useGLTF.preload(path);
  });
}
