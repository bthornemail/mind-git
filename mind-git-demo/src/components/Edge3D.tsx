import React, { useMemo } from 'react';
import { Line, Text } from '@react-three/drei';
import * as THREE from 'three';
import { Canvas, CanvasEdge, CanvasNode } from '../types';

interface Edge3DProps {
  edge: CanvasEdge;
  canvas: Canvas;
}

export const Edge3D: React.FC<Edge3DProps> = ({ edge, canvas }) => {
  const scale = 0.01;

  // Find source and target nodes
  const fromNode = canvas.nodes.find((n) => n.id === edge.fromNode);
  const toNode = canvas.nodes.find((n) => n.id === edge.toNode);

  const points = useMemo(() => {
    if (!fromNode || !toNode) return [];

    const from: [number, number, number] = [
      fromNode.x * scale,
      -fromNode.y * scale,
      0,
    ];
    const to: [number, number, number] = [
      toNode.x * scale,
      -toNode.y * scale,
      0,
    ];

    // Create a curved path with a control point
    const midPoint: [number, number, number] = [
      (from[0] + to[0]) / 2,
      (from[1] + to[1]) / 2,
      0.5, // Lift the curve slightly in Z
    ];

    // Generate smooth curve using quadratic bezier
    const curve = new THREE.QuadraticBezierCurve3(
      new THREE.Vector3(...from),
      new THREE.Vector3(...midPoint),
      new THREE.Vector3(...to)
    );

    return curve.getPoints(20);
  }, [fromNode, toNode, scale]);

  const labelPosition = useMemo(() => {
    if (!fromNode || !toNode) return [0, 0, 0] as [number, number, number];

    return [
      (fromNode.x * scale + toNode.x * scale) / 2,
      (-fromNode.y * scale + -toNode.y * scale) / 2,
      0.6,
    ] as [number, number, number];
  }, [fromNode, toNode, scale]);

  if (!fromNode || !toNode || points.length === 0) return null;

  return (
    <group>
      {/* Connection line */}
      <Line
        points={points}
        color="#666666"
        lineWidth={2}
        opacity={0.6}
        transparent
        dashed
        dashScale={10}
        dashSize={0.5}
        gapSize={0.3}
      />

      {/* Arrow indicator at target */}
      <mesh position={[toNode.x * scale, -toNode.y * scale, 0]}>
        <coneGeometry args={[0.15, 0.3, 8]} />
        <meshStandardMaterial color="#666666" />
      </mesh>

      {/* Edge label */}
      {edge.label && (
        <Text
          position={labelPosition}
          fontSize={0.3}
          color="#444444"
          anchorX="center"
          anchorY="middle"
          outlineWidth={0.05}
          outlineColor="#FFFFFF"
        >
          {edge.label}
        </Text>
      )}
    </group>
  );
};
