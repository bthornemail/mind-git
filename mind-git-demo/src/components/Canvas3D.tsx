import React, { Suspense, useState } from 'react';
import { Canvas as ThreeCanvas } from '@react-three/fiber';
import { OrbitControls, PerspectiveCamera, Grid, Text } from '@react-three/drei';
import { Node3D } from './Node3D';
import { Edge3D } from './Edge3D';
import { CompilerPanel } from './CompilerPanel';
import { Canvas, CanvasNode } from '../types';

interface Canvas3DProps {
  canvas: Canvas;
}

export const Canvas3D: React.FC<Canvas3DProps> = ({ canvas }) => {
  const [selectedNode, setSelectedNode] = useState<CanvasNode | null>(null);

  const handleNodeClick = (node: CanvasNode) => {
    setSelectedNode(selectedNode?.id === node.id ? null : node);
  };

  const handleNodeDrag = (node: CanvasNode, position: [number, number, number]) => {
    console.log(`Node ${node.id} dragged to:`, position);
    // In a real app, this would update the canvas state
  };

  return (
    <div style={{ width: '100%', height: '100vh', background: '#1a1a2e' }}>
      {/* Compiler panel */}
      <CompilerPanel canvas={canvas} />

      {/* Info panel */}
      <div
        style={{
          position: 'absolute',
          top: 20,
          left: 20,
          color: 'white',
          fontFamily: 'monospace',
          backgroundColor: 'rgba(0, 0, 0, 0.7)',
          padding: '15px',
          borderRadius: '8px',
          zIndex: 1000,
          maxWidth: '300px',
        }}
      >
        <h2 style={{ margin: '0 0 10px 0', fontSize: '18px' }}>
          mind-git Canvas Visualizer
        </h2>
        <p style={{ margin: '5px 0', fontSize: '12px' }}>
          🖱️ Click & drag nodes to move
        </p>
        <p style={{ margin: '5px 0', fontSize: '12px' }}>
          🔄 Right-click & drag to rotate
        </p>
        <p style={{ margin: '5px 0', fontSize: '12px' }}>
          🔍 Scroll to zoom
        </p>
        <p style={{ margin: '10px 0 5px 0', fontSize: '12px', fontWeight: 'bold' }}>
          Nodes: {canvas.nodes.length} | Edges: {canvas.edges.length}
        </p>
        {selectedNode && (
          <div
            style={{
              marginTop: '10px',
              padding: '10px',
              backgroundColor: 'rgba(100, 100, 255, 0.2)',
              borderRadius: '5px',
            }}
          >
            <p style={{ margin: '0 0 5px 0', fontSize: '12px', fontWeight: 'bold' }}>
              Selected Node:
            </p>
            <p style={{ margin: '3px 0', fontSize: '11px' }}>
              ID: {selectedNode.id}
            </p>
            <p style={{ margin: '3px 0', fontSize: '11px' }}>
              Position: ({selectedNode.x}, {selectedNode.y})
            </p>
            <p style={{ margin: '3px 0', fontSize: '11px', whiteSpace: 'pre-wrap' }}>
              {selectedNode.text}
            </p>
          </div>
        )}
      </div>

      {/* Legend */}
      <div
        style={{
          position: 'absolute',
          bottom: 20,
          right: 20,
          color: 'white',
          fontFamily: 'monospace',
          backgroundColor: 'rgba(0, 0, 0, 0.7)',
          padding: '15px',
          borderRadius: '8px',
          zIndex: 1000,
          fontSize: '11px',
        }}
      >
        <h3 style={{ margin: '0 0 10px 0', fontSize: '14px' }}>
          Mathematical Node Types
        </h3>
        <div style={{ display: 'flex', flexDirection: 'column', gap: '5px' }}>
          <LegendItem color="#A8D8EA" label="Observe (D7)" desc="Identity element" />
          <LegendItem color="#FF6B6B" label="Activate (D0)" desc="Entry point" />
          <LegendItem color="#4ECDC4" label="Integrate (D1)" desc="Addition" />
          <LegendItem color="#95E1D3" label="Propagate (D2)" desc="Shift" />
          <LegendItem color="#F38181" label="BackPropagate (D3)" desc="Comparison" />
          <LegendItem color="#AA96DA" label="Transform (D4)" desc="Multiplication" />
          <LegendItem color="#FCBAD3" label="Verify (D5)" desc="Voting" />
          <LegendItem color="#FFFFD2" label="Store (D6)" desc="Memory" />
        </div>
      </div>

      {/* 3D Scene */}
      <ThreeCanvas>
        <Suspense fallback={null}>
          {/* Camera */}
          <PerspectiveCamera makeDefault position={[15, 10, 15]} />
          <OrbitControls
            enablePan
            enableZoom
            enableRotate
            minDistance={5}
            maxDistance={50}
          />

          {/* Lighting */}
          <ambientLight intensity={0.5} />
          <directionalLight position={[10, 10, 5]} intensity={0.8} />
          <directionalLight position={[-10, -10, -5]} intensity={0.3} />
          <pointLight position={[0, 5, 0]} intensity={0.5} color="#ffffff" />

          {/* Grid for spatial reference */}
          <Grid
            args={[30, 30]}
            cellSize={1}
            cellThickness={0.5}
            cellColor="#444444"
            sectionSize={5}
            sectionThickness={1}
            sectionColor="#666666"
            fadeDistance={40}
            fadeStrength={1}
            position={[0, 0, -0.5]}
          />

          {/* Origin marker */}
          <mesh position={[0, 0, 0]}>
            <sphereGeometry args={[0.2, 16, 16]} />
            <meshStandardMaterial
              color="#FFD700"
              emissive="#FFD700"
              emissiveIntensity={0.5}
            />
          </mesh>
          <Text
            position={[0, -1, 0]}
            fontSize={0.4}
            color="#FFD700"
            anchorX="center"
            anchorY="top"
          >
            Origin (0,0)
          </Text>

          {/* Render all edges first (so they appear behind nodes) */}
          {canvas.edges.map((edge) => (
            <Edge3D key={edge.id} edge={edge} canvas={canvas} />
          ))}

          {/* Render all nodes */}
          {canvas.nodes.map((node) => (
            <Node3D
              key={node.id}
              node={node}
              onClick={handleNodeClick}
              onDrag={handleNodeDrag}
            />
          ))}
        </Suspense>
      </ThreeCanvas>
    </div>
  );
};

// Helper component for legend items
const LegendItem: React.FC<{ color: string; label: string; desc: string }> = ({
  color,
  label,
  desc,
}) => (
  <div style={{ display: 'flex', alignItems: 'center', gap: '8px' }}>
    <div
      style={{
        width: '12px',
        height: '12px',
        backgroundColor: color,
        borderRadius: '2px',
      }}
    />
    <span>
      <strong>{label}:</strong> {desc}
    </span>
  </div>
);
