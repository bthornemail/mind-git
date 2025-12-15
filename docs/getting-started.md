---
id: "mind-git:documentation:getting-started"
title: "Getting Started Guide"
type: ["documentation"]
category: documentation
layer: 4
dimensions: [0, 1, 7, 8, 9]
mathematicalFoundation: ["polynomial-algebra","hopf-fibration"]
hopfCompatible: true
normPreserving: false
status: "complete"
completeness: 80
tags: ["documentation","canvasl","mathematics","compiler","ast","api","polynomial","algebra"]
keywords: ["canvasl","aal","ast","compiler","polynomial","algebra","formal","verification","hopf","identity","typescript","javascript"]
lastUpdate: "2025-12-15"
canvasL:
  nodeTypes: ["Observe","Integrate","Transform","Activate","Compute"]
  compilationOrder: 4
  spatialCoordinates: {x: 400, y: 0}
  dimensionalMapping: [D7, D1, D4, D0]
  aalMnemonics: [MOV, ADD, MUL, CALL]
---

# Getting Started Guide

Welcome to CanvasL - a visual programming language that transforms spatial diagrams into mathematically verified executable programs.

## 🎯 Quick Start

### Installation

#### Global Installation (Recommended)
```bash
npm install -g mind-git
mind-git --help
```

#### Project Dependency
```bash
npm install mind-git
import { CanvasLCompiler } from 'mind-git';
```

#### Development Setup
```bash
git clone https://github.com/bthornemail/mind-git.git
cd mind-git
npm install
npm test
```

## 🎨 Your First Canvas Program

### 1. Create a Canvas File
Create `my-first-canvas.canvas`:

```json
{
  "nodes": [
    {
      "id": "observer",
      "type": "text",
      "x": 0,
      "y": 0,
      "width": 120,
      "height": 40,
      "text": "#Observe: Start computation"
    },
    {
      "id": "input",
      "type": "text", 
      "x": 150,
      "y": 0,
      "width": 100,
      "height": 40,
      "text": "#Integrate: Get user input"
    },
    {
      "id": "process",
      "type": "text",
      "x": 300,
      "y": 0,
      "width": 120,
      "height": 40,
      "text": "#Transform: Process data"
    },
    {
      "id": "output",
      "type": "text",
      "x": 450,
      "y": 0,
      "width": 100,
      "height": 40,
      "text": "#Activate: Display result"
    }
  ],
  "edges": [
    {
      "id": "flow1",
      "fromNode": "observer",
      "toNode": "input"
    },
    {
      "id": "flow2", 
      "fromNode": "input",
      "toNode": "process"
    },
    {
      "id": "flow3",
      "fromNode": "process", 
      "toNode": "output"
    }
  ]
}
```

### 2. Compile to JavaScript
```bash
mind-git compile my-first-canvas.canvas
```

### 3. Run Generated Code
```bash
node output.js
```

## 🧮 Understanding CanvasL

### Core Concepts

#### 1. Spatial Arrangement = Code
In CanvasL, the position and arrangement of nodes on the canvas directly encodes mathematical operations:

- **Node Position (x, y)** → Polynomial coefficients
- **Node Distance from Observer** → Polynomial degree
- **Edge Connections** → Algebraic operations

#### 2. Observer Pattern
The node at coordinates (0, 0) serves as the identity element:
- **Mathematical Role**: Polynomial constant P₀ = 1
- **Computation Role**: 1 · a = a (observation doesn't destroy data)
- **Self-Reference**: 1 · 1 = 1 (no paradox)

#### 3. Node Classification
Nodes are classified by text prefix, mapping to mathematical operations:

| Prefix | Dimension | Operation | Example |
|--------|-----------|-----------|---------|
| `#Integrate:` | D1 | ADD | Data input |
| `#Transform:` | D4 | MUL | Computation |
| `#Activate:` | D0 | JMP | Output |

## 🔧 Advanced Usage

### Programmatic Compilation
```typescript
import { CanvasLCompiler } from 'mind-git';

async function compileCanvas(canvasPath: string) {
  const compiler = new CanvasLCompiler();
  
  // Read canvas file
  const canvasData = await fs.readFile(canvasPath, 'utf-8');
  const canvas = JSON.parse(canvasData);
  
  // Compile to JavaScript
  const result = await compiler.compileCanvas(canvas);
  
  if (result.success) {
    console.log('Generated JavaScript:');
    console.log(result.generated_code.javascript_code);
    
    // Write to file
    await fs.writeFile('output.js', result.generated_code.javascript_code);
  } else {
    console.error('Compilation failed:', result.errors);
  }
}

// Usage
compileCanvas('my-canvas.canvas');
```

### Custom Compiler Options
```typescript
const compiler = new CanvasLCompiler({
  targetLanguages: ['javascript', 'typescript'],
  optimizationLevel: 'high',
  enableHopfOptimization: true,
  verifyNorms: true
});
```

## 📚 Canvas File Format

### Complete Node Schema
```json
{
  "id": "unique-identifier",
  "type": "text" | "file" | "link" | "group",
  "x": 0,
  "y": 0,
  "width": 100,
  "height": 40,
  "text": "#Transform: operation",
  "color": "#1e88e5"
}
```

### Edge Schema
```json
{
  "id": "edge-identifier", 
  "fromNode": "source-node-id",
  "toNode": "target-node-id",
  "color": "#0969da",
  "label": "data-flow"
}
```

## 🎨 Visual Design Tips

### Color Coding
Use standard colors to indicate mathematical operations:
- **Red** (#e74c3c): Control flow (D0)
- **Orange** (#f97316): Data operations (D1)
- **Yellow** (#fbbf24): Propagation (D2)
- **Green** (#4ade80): Comparison (D3)
- **Blue** (#1e88e5): Transformation (D4)
- **Indigo** (#6366f1): Verification (D5)
- **Purple** (#a855f7): Storage (D6)
- **Gray** (#6c757d): Observation (D7)

### Layout Best Practices
1. **Observer at Origin**: Place `#Observe:` node at (0, 0)
2. **Left to Right Flow**: Arrange computation flow left-to-right
3. **Group Related**: Place related operations near each other
4. **Avoid Edge Crossings**: Keep edges from crossing when possible
5. **Clear Spacing**: Leave room between logical sections

## 🧪 Testing Your Canvas

### Unit Testing
```bash
# Test mathematical operations
npm run test:unit

# Test formal verification
npm run test:formal

# Test compilation
npm run test:integration
```

### Debugging Compilation
```typescript
const compiler = new CanvasLCompiler({
  debug: true,
  verbose: true
});

const result = await compiler.compileCanvas(canvas);

// Check compilation details
console.log('AST:', result.ast);
console.log('Instructions:', result.aal_instructions);
console.log('Warnings:', result.warnings);
```

## 🌐 Integration Examples

### Web Application
```html
<!DOCTYPE html>
<html>
<head>
  <script type="module">
    import { CanvasLCompiler } from 'https://cdn.skypack.dev/mind-git';
    
    const compiler = new CanvasLCompiler();
    
    async function compileCanvas() {
      const canvasData = document.getElementById('canvas-input').value;
      const canvas = JSON.parse(canvasData);
      const result = await compiler.compileCanvas(canvas);
      
      if (result.success) {
        eval(result.generated_code.javascript_code);
      }
    }
  </script>
</head>
<body>
  <textarea id="canvas-input" placeholder="Paste canvas JSON..."></textarea>
  <button onclick="compileCanvas()">Compile & Run</button>
</body>
</html>
```

### Node.js Application
```javascript
import { CanvasLCompiler } from 'mind-git';
import express from 'express';

const app = express();
const compiler = new CanvasLCompiler();

app.post('/compile', async (req, res) => {
  try {
    const result = await compiler.compileCanvas(req.body);
    res.json(result);
  } catch (error) {
    res.status(400).json({ error: error.message });
  }
});

app.listen(3000, () => {
  console.log('CanvasL compiler server running on port 3000');
});
```

## 🔍 Troubleshooting

### Common Issues

#### 1. Observer Not at Origin
**Error**: "Observer node must be at (0, 0)"
**Solution**: Move your `#Observe:` node to coordinates (0, 0)

#### 2. Invalid Node Prefix
**Error**: "Unknown node type: #Compute:"
**Solution**: Use valid prefixes from [Canvas Node Types](canvas-nodes.md)

#### 3. Circular Dependencies
**Error**: "Canvas contains cycles"
**Solution**: Rearrange nodes to eliminate circular references

#### 4. Compilation Warnings
**Warning**: "Canvas structure is not fully Hopf-compatible"
**Solution**: This is normal - optimization is limited but compilation still works

### Debug Mode
```bash
# Enable verbose output
DEBUG=canvasl:* mind-git compile my-canvas.canvas

# Show AST structure
mind-git compile my-canvas.canvas --debug
```

## 📖 Next Steps

### Learning Resources
- [Mathematical Foundation](mathematical-foundation.md) - Understand the math
- [Canvas Node Types](canvas-nodes.md) - Complete node reference
- [Architecture Overview](architecture.md) - System design
- [API Reference](api-reference.md) - Complete API documentation

### Community
- **GitHub Issues**: [Report bugs](https://github.com/bthornemail/mind-git/issues)
- **Discussions**: [Ask questions](https://github.com/bthornemail/mind-git/discussions)
- **Examples**: [Share canvases](https://github.com/bthornemail/mind-git/tree/main/examples)

---

**Welcome to CanvasL! Where visual arrangement becomes mathematically verifiable computation.** 🎯