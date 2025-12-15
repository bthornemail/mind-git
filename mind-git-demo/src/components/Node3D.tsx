import React, { useRef, useState } from 'react';
import { useFrame } from '@react-three/fiber';
import { Text } from '@react-three/drei';
import * as THREE from 'three';
import { CanvasNode, parseNodeType, getNodeColor } from '../types';
import { NodeGeometry } from './NodeGeometry';

interface Node3DProps {
  node: CanvasNode;
  onClick?: (node: CanvasNode) => void;
  onDrag?: (node: CanvasNode, position: [number, number, number]) => void;
}

export const Node3D: React.FC<Node3DProps> = ({ node, onClick, onDrag }) => {
  const meshRef = useRef<THREE.Mesh>(null);
  const [hovered, setHovered] = useState(false);
  const [selected, setSelected] = useState(false);
  const [isDragging, setIsDragging] = useState(false);

  // Convert 2D canvas coordinates to 3D space
  // Scale down canvas coordinates for better visualization
  const scale = 0.01;
  const position: [number, number, number] = [
    node.x * scale,
    -node.y * scale, // Invert Y for standard 3D coordinate system
    0,
  ];

  const nodeType = parseNodeType(node.text);
  const baseColor = node.color || getNodeColor(nodeType);

  // Animate on hover
  useFrame(() => {
    if (meshRef.current) {
      const targetZ = hovered ? 0.5 : 0;
      meshRef.current.position.z = THREE.MathUtils.lerp(
        meshRef.current.position.z,
        targetZ,
        0.1
      );

      const targetScale = hovered || selected ? 1.1 : 1.0;
      meshRef.current.scale.setScalar(
        THREE.MathUtils.lerp(meshRef.current.scale.x, targetScale, 0.1)
      );
    }
  });

  const handleClick = (e: any) => {
    e.stopPropagation();
    setSelected(!selected);
    onClick?.(node);
  };

  const handlePointerDown = (e: any) => {
    e.stopPropagation();
    setIsDragging(true);
  };

  const handlePointerUp = (e: any) => {
    e.stopPropagation();
    setIsDragging(false);
  };

  const handlePointerMove = (e: any) => {
    if (isDragging) {
      e.stopPropagation();
      const newPosition: [number, number, number] = [
        e.point.x,
        e.point.y,
        e.point.z,
      ];
      onDrag?.(node, newPosition);
    }
  };

  // Get display text (remove prefix for cleaner display)
  const displayText = node.text.split('\n')[0].replace(/^#\w+:\s*/, '');
  const detailText = node.text.split('\n').slice(1).join('\n');

  // Calculate box dimensions based on node size
  const width = node.width * scale * 0.8;
  const height = node.height * scale * 0.8;
  const depth = 0.3;

  return (
    <group position={position}>
      {/* Node geometry (supports multiple shapes based on type) */}
      <NodeGeometry
        nodeType={nodeType}
        color={baseColor}
        width={width}
        height={height}
        depth={depth}
        hovered={hovered}
        selected={selected}
        meshRef={meshRef}
        onClick={handleClick}
        onPointerDown={handlePointerDown}
        onPointerUp={handlePointerUp}
        onPointerMove={handlePointerMove}
        onPointerEnter={() => setHovered(true)}
        onPointerLeave={() => {
          setHovered(false);
          setIsDragging(false);
        }}
      />

      {/* Node label */}
      <Text
        position={[0, 0, depth / 2 + 0.01]}
        fontSize={0.5}
        color="#000000"
        anchorX="center"
        anchorY="middle"
        maxWidth={width * 0.9}
      >
        {displayText}
      </Text>

      {/* Node type indicator */}
      {nodeType && (
        <Text
          position={[0, height / 2 - 0.3, depth / 2 + 0.01]}
          fontSize={0.3}
          color="#666666"
          anchorX="center"
          anchorY="middle"
        >
          {nodeType}
        </Text>
      )}

      {/* Detail text when selected */}
      {selected && detailText && (
        <Text
          position={[0, -height / 2 - 0.5, depth / 2 + 0.01]}
          fontSize={0.25}
          color="#333333"
          anchorX="center"
          anchorY="top"
          maxWidth={width * 1.2}
        >
          {detailText}
        </Text>
      )}

      {/* Glow effect for observer node (0,0) */}
      {node.x === 0 && node.y === 0 && (
        <pointLight
          position={[0, 0, 1]}
          intensity={0.5}
          distance={5}
          color="#A8D8EA"
        />
      )}
    </group>
  );
};
