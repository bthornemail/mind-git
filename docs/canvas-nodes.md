# Canvas Node Types

CanvasL nodes are classified by text prefix, mapping directly to mathematical operations and dimensional levels.

## 🎨 Node Classification System

### Prefix Mapping
| Prefix | Dimension | Assembly Op | Mathematical Meaning | Canvas Color |
|--------|-----------|-------------|---------------------|--------------|
| `#Activate:` | D0 | JMP | Linear transformation | 🔴 Red |
| `#Integrate:` | D1 | ADD | Polynomial addition | 🟠 Orange |
| `#Propagate:` | D2 | SHL | Polynomial shift | 🟡 Yellow |
| `#BackPropagate:` | D3 | CMP | Polynomial comparison | 🟢 Green |
| `#Transform:` | D4 | MUL | Polynomial multiplication | 🔵 Blue |
| `#Verify:` | D5 | VOTE | Consensus voting | 🟣 Indigo |
| `#Store:` | D6 | PUSH | Memory stack operation | 🟣 Purple |
| `#Observe:` | D7 | SYNC | Quantum observation | ⚫ Gray |

### Extended Node Types
| Prefix | Dimension | Assembly Op | Mathematical Meaning | Canvas Color |
|--------|-----------|-------------|---------------------|--------------|
| `#GeometricPropagate:` | D2 | GEOM_EXP | Geometric expansion | 🟡 Yellow |
| `#GeometricObserve:` | D7 | GEOM_SYNC | Geometric observation | ⚫ Gray |
| `#EpistemicBound:` | D8 | EPI_BOUND | Uncertainty bounding | 🟤 Brown |
| `#SedenionTransform:` | D16 | SEDENION_MUL | 16D composition | 🟪 Pink |

## 📐 Dimensional Hierarchy

### Assembly-Algebra Language (AAL) Dimensions
CanvasL uses an 11-dimensional graded modal type system (D0-D10):

```
D0: Linear transformations (JMP/CALL)
D1: Polynomial addition (ADD/SUB)
D2: Polynomial shift (SHL/SHR)
D3: Polynomial comparison (CMP)
D4: Polynomial multiplication (MUL/DIV)
D5: Consensus voting (VOTE)
D6: Memory operations (PUSH/POP)
D7: Quantum observation (SYNC)
D8: Uncertainty bounding (EPI_BOUND)
D9: Geometric expansion (GEOM_EXP)
D10: Multi-agent coordination (COORD)
```

### Mathematical Constraints
- **Adams' Theorem**: Only dimensions 1, 2, 4, 8 support normed division algebras
- **Hopf Fibrations**: Only exist for S¹, S³, S⁷ (degrees 1, 3, 7)
- **Norm Preservation**: All operations must satisfy `||a × b|| = ||a|| × ||b||`

## 🔧 Canvas File Structure

### Node Format
```json
{
  "id": "unique-node-id",
  "type": "text",
  "x": 100,
  "y": 200,
  "width": 250,
  "height": 60,
  "text": "#Transform: multiply_data"
}
```

### Edge Format
```json
{
  "id": "edge-id",
  "fromNode": "source-node-id",
  "toNode": "target-node-id",
  "label": "data_flow"
}
```

## 🎯 Usage Examples

### Basic Computation
```canvas
# Node 1: Input data
#Integrate: input_data
x: 100, y: 100

# Node 2: Transform data  
#Transform: multiply_data
x: 300, y: 100

# Edge: Connect nodes
fromNode: input_data
toNode: multiply_data
```

### Geometric Operations
```canvas
# Geometric expansion
#GeometricPropagate: expand_region
x: 200, y: 200

# Geometric observation
#GeometricObserve: measure_boundary
x: 400, y: 200
```

### Advanced Operations
```canvas
# Uncertainty bounding
#EpistemicBound: estimate_confidence
x: 300, y: 300

# Multi-agent coordination
#SedenionTransform: coordinate_systems
x: 500, y: 300
```

## 🌐 Compilation Process

### 1. Canvas Parsing
- Extract nodes and edges from `.canvas` JSON
- Classify nodes by text prefix
- Validate spatial arrangement

### 2. AST Generation
- Build hierarchical syntax tree
- Identify dependencies and execution order
- Extract function signatures

### 3. Code Generation
- Map nodes to AAL instructions
- Apply dimensional optimizations
- Generate target language code

## 🎨 Visual Design Guidelines

### Color Coding
Use the standard color palette to indicate mathematical operations:
- **Red (D0)**: Control flow and jumps
- **Orange (D1)**: Data input and integration
- **Yellow (D2)**: Data propagation and shifting
- **Green (D3)**: Comparison and decision points
- **Blue (D4)**: Transformation and computation
- **Indigo (D5)**: Voting and consensus
- **Purple (D6)**: Memory and storage
- **Gray (D7)**: Observation and synchronization

### Spatial Layout
- **Left to Right**: Primary execution flow
- **Top to Bottom**: Data dependency hierarchy
- **Observer at Origin**: (0,0) for identity element
- **Distance Encoding**: Node distance from observer affects polynomial degree

### Best Practices
1. **Start with Observer**: Place `#Observe:` node at (0,0)
2. **Use Clear Prefixes**: Always begin node text with correct prefix
3. **Logical Flow**: Arrange nodes to show clear execution path
4. **Avoid Crossing**: Edges shouldn't cross when possible
5. **Group Related**: Place related operations near each other

---

**CanvasL nodes are not just visual elements - they're mathematical operations with precise semantics.** 🎯