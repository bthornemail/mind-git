import React, { Suspense, useState } from 'react';
import { Canvas as ThreeCanvas } from '@react-three/fiber';
import { OrbitControls, PerspectiveCamera, Grid, Text } from '@react-three/drei';
import * as THREE from 'three';
import { Node3D } from './Node3D';
import { Edge3D } from './Edge3D';
import { CompilerPanel } from './CompilerPanel';
import { ModelSelector } from './ModelSelector';
import { SceneSwitcher } from './SceneSwitcher';
import { FlyControls } from './FlyControls';
import { Canvas, CanvasNode, NodeType, parseNodeType } from '../types';
import { KhronosModel } from '../services/modelLibrary';

interface Canvas3DProps {
  canvas: Canvas;
  onSceneChange?: (sceneId: string) => void;
  currentSceneId?: string;
}

export const Canvas3D: React.FC<Canvas3DProps> = ({ canvas, onSceneChange, currentSceneId }) => {
  const [selectedNode, setSelectedNode] = useState<CanvasNode | null>(null);
  const [customModels, setCustomModels] = useState<Map<NodeType, KhronosModel>>(new Map());
  const [transformMode, setTransformMode] = useState<'translate' | 'rotate' | 'scale'>('translate');
  const [useFlyControls, setUseFlyControls] = useState(false);
  const [cameraPosition, setCameraPosition] = useState<[number, number, number]>([15, 10, 15]);

  const handleNodeClick = (node: CanvasNode) => {
    setSelectedNode(selectedNode?.id === node.id ? null : node);
  };

  const handleNodeDrag = (node: CanvasNode, position: [number, number, number]) => {
    console.log(`Node ${node.id} dragged to:`, position);
    // In a real app, this would update the canvas state
  };

  const handleModelChange = (nodeType: NodeType, model: KhronosModel) => {
    setCustomModels(new Map(customModels.set(nodeType, model)));
    console.log(`Model changed for ${nodeType}:`, model.name);
  };

  const handleNodeTransform = (node: CanvasNode, position: [number, number, number], rotation: [number, number, number], scale: [number, number, number]) => {
    console.log(`Node ${node.id} transformed:`, { position, rotation, scale });
    // In a real app, this would update the canvas state
    // For now, just log the transformation
  };

  const handleCameraChange = (position: THREE.Vector3, rotation: THREE.Euler) => {
    setCameraPosition([position.x, position.y, position.z]);
  };

  return (
    <div style={{ width: '100%', height: '100vh', background: '#1a1a2e' }}>
      {/* Compiler panel */}
      <CompilerPanel canvas={canvas} />

      {/* Model selector */}
      <ModelSelector onModelChange={handleModelChange} />

      {/* Scene switcher */}
      {onSceneChange && currentSceneId && (
        <div style={{ position: 'absolute', top: 20, right: 320, zIndex: 1000 }}>
          <SceneSwitcher
            currentSceneId={currentSceneId}
            onSceneChange={onSceneChange}
          />
        </div>
      )}

      {/* Control panel */}
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
          🖱️ Click nodes to select
        </p>
        <p style={{ margin: '5px 0', fontSize: '12px' }}>
          🎛️ Transform selected nodes
        </p>
        <p style={{ margin: '5px 0', fontSize: '12px' }}>
          🚁 Switch to Fly mode for navigation
        </p>
        <p style={{ margin: '5px 0', fontSize: '12px' }}>
          🔄 Orbit mode: Right-click & drag to rotate
        </p>
        <p style={{ margin: '5px 0', fontSize: '12px' }}>
          🔍 Scroll to zoom
        </p>
        <p style={{ margin: '10px 0 5px 0', fontSize: '12px', fontWeight: 'bold' }}>
          Nodes: {canvas.nodes.length} | Edges: {canvas.edges.length}
        </p>

        {/* Transform controls */}
        <div style={{ margin: '10px 0' }}>
          <p style={{ margin: '5px 0', fontSize: '11px', fontWeight: 'bold' }}>
            Transform Mode:
          </p>
          <div style={{ display: 'flex', gap: '5px' }}>
            <button
              onClick={() => setTransformMode('translate')}
              style={{
                padding: '3px 6px',
                fontSize: '10px',
                backgroundColor: transformMode === 'translate' ? '#4CAF50' : '#666',
                color: 'white',
                border: 'none',
                borderRadius: '3px',
                cursor: 'pointer'
              }}
            >
              Move
            </button>
            <button
              onClick={() => setTransformMode('rotate')}
              style={{
                padding: '3px 6px',
                fontSize: '10px',
                backgroundColor: transformMode === 'rotate' ? '#4CAF50' : '#666',
                color: 'white',
                border: 'none',
                borderRadius: '3px',
                cursor: 'pointer'
              }}
            >
              Rotate
            </button>
            <button
              onClick={() => setTransformMode('scale')}
              style={{
                padding: '3px 6px',
                fontSize: '10px',
                backgroundColor: transformMode === 'scale' ? '#4CAF50' : '#666',
                color: 'white',
                border: 'none',
                borderRadius: '3px',
                cursor: 'pointer'
              }}
            >
              Scale
            </button>
          </div>
        </div>

        {/* Camera controls */}
        <div style={{ margin: '10px 0' }}>
          <p style={{ margin: '5px 0', fontSize: '11px', fontWeight: 'bold' }}>
            Camera Mode:
          </p>
          <div style={{ display: 'flex', gap: '5px' }}>
            <button
              onClick={() => setUseFlyControls(!useFlyControls)}
              style={{
                padding: '3px 6px',
                fontSize: '10px',
                backgroundColor: useFlyControls ? '#2196F3' : '#666',
                color: 'white',
                border: 'none',
                borderRadius: '3px',
                cursor: 'pointer'
              }}
            >
              {useFlyControls ? 'Fly Mode' : 'Orbit Mode'}
            </button>
          </div>
          <p style={{ margin: '3px 0', fontSize: '10px', color: '#888' }}>
            Position: ({cameraPosition[0].toFixed(1)}, {cameraPosition[1].toFixed(1)}, {cameraPosition[2].toFixed(1)})
          </p>
        </div>
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
          <PerspectiveCamera makeDefault position={cameraPosition} />
          
          {/* Camera controls */}
          {useFlyControls ? (
            <FlyControls
              enabled={true}
              movementSpeed={2}
              rollSpeed={0.005}
              dragToLook={false}
              autoForward={false}
              onControlChange={handleCameraChange}
            />
          ) : (
            <OrbitControls
              ref={(ref) => {
                if (ref) {
                  (window as any).__orbitControls = ref;
                  const camera = ref.object;
                  if (camera) {
                    (window as any).__camera = camera;
                  }
                }
              }}
              enablePan
              enableZoom
              enableRotate
              minDistance={5}
              maxDistance={50}
              onChange={() => {
                const camera = (window as any).__camera;
                if (camera) {
                  setCameraPosition([camera.position.x, camera.position.y, camera.position.z]);
                }
              }}
            />
          )}

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
          {canvas.nodes.map((node) => {
            const nodeType = parseNodeType(node.text);
            const customModel = nodeType ? customModels.get(nodeType) : undefined;
            // Use composite key to force re-render when model changes
            const nodeKey = customModel
              ? `${node.id}-${customModel.name}`
              : node.id;
            return (
              <Node3D
                key={nodeKey}
                node={node}
                onClick={handleNodeClick}
                onDrag={handleNodeDrag}
                onTransform={handleNodeTransform}
                customModel={customModel}
                isSelected={selectedNode?.id === node.id}
                transformMode={transformMode}
              />
            );
          })}
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
