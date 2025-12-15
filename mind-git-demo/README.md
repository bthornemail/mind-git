# mind-git 2.5D Visualizer

Interactive 3D visualization of CanvasL spatial programming language from the mind-git project.

## Overview

This demo provides a web-based 2.5D interactive visualizer for mind-git's Canvas spatial programming system. It transforms 2D canvas diagrams into interactive 3D scenes where you can:

- **Visualize** mathematical node types (Activate, Integrate, Transform, etc.)
- **Interact** with nodes by clicking and dragging
- **Navigate** the scene with orbit controls (rotate, zoom, pan)
- **Explore** the spatial programming paradigm

## Quick Start

```bash
npm install
npm start
```

Opens at [http://localhost:3000](http://localhost:3000)

## Features

### Interactive 3D Nodes
- **Procedural geometry** - Each node type has a unique mathematically meaningful shape
- **GLTF/GLB support** - Use custom 3D models (see GLTF-GUIDE.md)
- Color-coded by mathematical operation type (D0-D7 dimensions)
- Hover effects with glow and scale animations
- Click to select and view detailed information
- Drag nodes to reposition (in development)

### Mathematical Node Types & Geometries
- **Observe (D7)**: Sphere - Identity element at origin (0,0) - Quantum observation
- **Activate (D0)**: Pyramid - Entry point - Linear transformation
- **Integrate (D1)**: Torus - Polynomial addition over F₂
- **Propagate (D2)**: Cone - Polynomial shift operations
- **BackPropagate (D3)**: Inverted Cone - Polynomial comparison
- **Transform (D4)**: Octahedron (8 faces) - Norm-preserving multiplication
- **Verify (D5)**: Dodecahedron (12 faces) - Consensus voting
- **Store (D6)**: Box - Memory stack operations

### Visual Features
- 3D grid for spatial reference
- Curved edges connecting related nodes
- Edge labels showing data flow
- Origin marker at (0,0)
- Special glow effect for observer node
- Information panel with node details
- Interactive legend

## Controls

- **Left Click + Drag**: Rotate camera around scene
- **Right Click + Drag**: Pan camera
- **Scroll**: Zoom in/out
- **Click Node**: Select and view details
- **Hover Node**: Highlight with glow effect

## Architecture

### Components

#### `Canvas3D`
Main container component that sets up the Three.js scene with camera, lighting, and controls.

#### `Node3D`
Renders individual canvas nodes as 3D boxes with text labels, type indicators, and interactive states.

#### `Edge3D`
Visualizes connections between nodes using curved 3D lines with arrow indicators.

### Data Structure

Canvas data follows Obsidian Canvas JSON format:

```typescript
interface Canvas {
  nodes: CanvasNode[];
  edges: CanvasEdge[];
}
```

## Mathematical Foundation

Based on:
- **Adams' Theorem**: 8-dimensional limit for normed division algebras
- **Identity Chain**: Brahmagupta (2D) → Euler (4D) → Degen (8D)
- **Polynomial Algebra**: Operations over F₂ binary field
- **Hopf Fibrations**: S¹, S³, S⁷ (dimensions 1, 3, 7)

## Technology Stack

- React + TypeScript
- Three.js via React Three Fiber
- React Three Drei for controls and helpers

## Customizing 3D Models

### Using GLTF/GLB Models

The visualizer supports custom 3D models in GLTF (JSON) and GLB (binary) formats:

1. **Create or obtain** GLTF/GLB models (Blender, Maya, etc.)
2. **Place models** in `public/models/`
3. **Configure** in `src/services/modelLoader.ts`
4. **Restart** the dev server

**Quick example**:
```typescript
// src/services/modelLoader.ts
[NodeType.Transform]: {
  path: '/models/custom-transform.glb',
  scale: 1.0,
  useProcedural: false,  // Enable custom model
}
```

See **GLTF-GUIDE.md** for complete documentation and **MODELS-QUICK-REF.md** for quick reference.

### Default Geometries

Each node type uses a procedurally generated shape with mathematical significance:
- Sphere (Observe) - Perfect symmetry
- Octahedron (Transform) - 8 faces for 8D octonions
- Dodecahedron (Verify) - 12 faces for verification
- Torus (Integrate) - Ring for addition/integration

## Learn More

- [mind-git Repository](../README.md)
- [CanvasL Documentation](../logos-system/README.md)
- [GLTF/GLB Model Guide](GLTF-GUIDE.md)
- [Model Quick Reference](MODELS-QUICK-REF.md)
