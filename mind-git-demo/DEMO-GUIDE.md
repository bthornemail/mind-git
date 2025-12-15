# mind-git 2.5D Visualizer - Demo Guide

## Quick Start

```bash
npm install
npm start
```

The visualizer will open at [http://localhost:3000](http://localhost:3000)

## What You'll See

### The 3D Scene
When the demo loads, you'll see an interactive 3D visualization of a spatial programming canvas:

- **8 colored nodes** representing different mathematical operations
- **Curved connecting lines** showing data flow between operations
- **Grid plane** for spatial reference
- **Gold sphere** at origin (0,0) marking the identity element

### Interactive Features

#### Camera Controls
- **Left-click + drag**: Rotate camera around the scene
- **Right-click + drag**: Pan the camera view
- **Mouse scroll**: Zoom in and out
- **Double-click**: Reset view (if enabled)

#### Node Interaction
- **Hover over a node**: Watch it glow and scale up slightly
- **Click a node**: Select it to view detailed information
- **Click again**: Deselect to clear the info

#### Compiler Panel
- **Click "⚡ Open Compiler"** (top-right): Opens the compilation panel
- **Compile Canvas**: Generates code in multiple formats
- **View Output**: Switch between AAL assembly, JavaScript, and AST
- **Validation**: See if canvas structure is valid

## Understanding the Visualization

### Node Colors and Types

Each node type has a specific color and mathematical meaning:

| Color | Node Type | Dimension | Operation |
|-------|-----------|-----------|-----------|
| 🔵 Blue | Observe | D7 | Identity element (0,0) |
| 🔴 Red | Activate | D0 | Entry point / Linear transformation |
| 🔷 Teal | Integrate | D1 | Polynomial addition (F₂) |
| 🔹 Light Teal | Propagate | D2 | Polynomial shift |
| 🔸 Pink | BackPropagate | D3 | Polynomial comparison |
| 🟣 Purple | Transform | D4 | Norm-preserving multiplication |
| 🌸 Light Pink | Verify | D5 | Consensus voting |
| 🟡 Yellow | Store | D6 | Memory stack |

### The Example Canvas

The demo loads an example canvas that implements a mathematical computation flow:

1. **Observer (0,0)**: Identity element P₀ = 1 in polynomial algebra
2. **Activate**: Entry point that initiates the computation
3. **Integrate**: Adds two polynomials using XOR (F₂ field)
4. **Transform**: Multiplies polynomials with norm preservation
5. **Propagate**: Shifts polynomial degree
6. **BackPropagate**: Compares polynomial results
7. **Verify**: Validates results via consensus
8. **Store**: Pushes final result to memory stack

### Spatial Programming Concept

The key insight: **Position matters!**

- Nodes at different coordinates represent different polynomial degrees
- Distance from the observer (0,0) affects the computation
- The 2D spatial layout maps directly to polynomial algebra operations
- Edges show dependencies and data flow

## Using the Compiler

### Step 1: Open Compiler Panel
Click "⚡ Open Compiler" in the top-right corner.

### Step 2: Review Validation
The panel shows validation status:
- ✓ **Green**: Canvas structure is valid
- ⚠ **Yellow**: Warnings (e.g., missing observer node)
- ❌ **Red**: Errors that prevent compilation

### Step 3: Compile
Click "⚡ Compile Canvas" to generate code.

### Step 4: View Output
Switch between output formats:

#### AAL Assembly
```asm
; CanvasL Assembly-Algebra Language
; Graded modal type system: D0-D10

main:
  JMP main_body  ; D0: Linear transformation
  ADD P1, P2, P_result  ; D1: Polynomial addition over F₂
  MUL P1, P2, P_product  ; D4: Norm-preserving multiplication
```

#### JavaScript
```javascript
import { PolyF2, IdentityChain } from "mind-git";

function main() {
  const polynomial_add = PolyF2.add(p1, p2);
  const polynomial_mul = PolyF2.multiply(p1, p2);
  return result;
}
```

#### AST (Abstract Syntax Tree)
```json
{
  "type": "Program",
  "nodes": [...],
  "edges": [...],
  "metadata": {
    "nodeCount": 8,
    "hasObserver": true
  }
}
```

## Mathematical Foundation

### Why 8 Dimensions?
The system respects **Adams' Theorem**: only dimensions 1, 2, 4, and 8 support normed division algebras. The 8-dimensional limit is a fundamental mathematical constraint, not an arbitrary choice.

### Identity Chain
The compilation follows the historical chain of n-square identities:
- **Brahmagupta (628 AD)**: 2-square identity (complex numbers)
- **Euler (1748)**: 4-square identity (quaternions)
- **Degen (1818)**: 8-square identity (octonions)

### Polynomial Algebra over F₂
All operations use **binary field arithmetic**:
- Coefficients are 0 or 1 (false or true)
- Addition is XOR: `1 + 1 = 0` in F₂
- Example: `(1 + x²) + (1 + x) = x + x²`

### Observer Pattern
The node at **(0,0)** is special:
- Represents identity element P₀ = 1
- Glows with special lighting
- All other nodes are relative to this position
- Distance from observer affects polynomial degree

## Customizing the Demo

### Loading Your Own Canvas

To visualize your own canvas file:

1. Export a canvas from Obsidian (or create JSON)
2. Replace `exampleCanvas.ts` with your data
3. Restart the dev server

Example canvas format:
```typescript
const myCanvas: Canvas = {
  nodes: [
    {
      id: 'node1',
      type: 'text',
      x: 0, y: 0,
      width: 200, height: 80,
      text: '#Observe: Origin',
    },
    // ... more nodes
  ],
  edges: [
    {
      id: 'edge1',
      fromNode: 'node1',
      toNode: 'node2',
      label: 'flow',
    },
  ],
};
```

### Modifying Node Appearance

Edit `src/types.ts` to change node colors:
```typescript
export function getNodeColor(nodeType: NodeType | null): string {
  const colors = {
    [NodeType.Activate]: '#YOUR_COLOR_HERE',
    // ...
  };
}
```

### Adjusting Camera

Edit `Canvas3D.tsx` to change initial camera position:
```typescript
<PerspectiveCamera makeDefault position={[15, 10, 15]} />
```

## Next Steps

### Integration with Full Compiler
The current demo uses mock compilation. To integrate with the full mind-git compiler:

1. Install `mind-git` package: `npm install mind-git`
2. Update `src/services/compiler.ts` to use real compiler
3. Replace mock functions with actual compilation calls

### Adding Real-Time Execution
Future enhancement: execute the compiled code and visualize results in real-time.

### WebAssembly Integration
The logos-system includes Coq proofs that can be extracted to WebAssembly for in-browser verification.

### VR/AR Support
With minor modifications, this can run in VR headsets for immersive spatial programming.

## Troubleshooting

### Issue: 3D scene doesn't render
**Solution**: Check browser console for WebGL errors. Ensure your browser supports WebGL 2.0.

### Issue: Nodes appear too small/large
**Solution**: Adjust the `scale` constant in `Node3D.tsx`:
```typescript
const scale = 0.01; // Change this value
```

### Issue: Compilation fails
**Solution**: Check that all nodes have valid prefixes (`#Activate:`, `#Integrate:`, etc.)

### Issue: Performance issues
**Solution**: Reduce the number of nodes or simplify the grid. Edit `Grid` props in `Canvas3D.tsx`.

## Performance Notes

- **Optimal**: 5-20 nodes with 10-30 edges
- **Good**: 20-50 nodes with 30-100 edges
- **Acceptable**: 50-100 nodes with 100-200 edges
- **May lag**: 100+ nodes with 200+ edges

## Technology Details

### Stack
- React 19.2 + TypeScript 4.9
- Three.js 0.182
- React Three Fiber 9.4
- React Three Drei 10.7

### Browser Requirements
- WebGL 2.0 support
- Modern ES6+ JavaScript
- Recommended: Chrome 90+, Firefox 88+, Safari 14+

## Learn More

- [mind-git Main Repository](../../README.md)
- [CanvasL Language Specification](../../logos-system/README.md)
- [Mathematical Foundations](../../logos-system/formal/README.md)
- [Coq Proofs](../../logos-system/formal/Polynomials.v)

## Feedback and Issues

Found a bug or have a suggestion?
- Open an issue in the main mind-git repository
- Check existing issues first
- Provide browser info and steps to reproduce

---

**Enjoy exploring spatial programming in 3D!** 🚀
