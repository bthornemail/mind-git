# API Reference

Complete API documentation for CanvasL visual programming language and mathematical foundation.

## 🎯 Core Classes

### CanvasLCompiler
Main compiler class for transforming canvas files to executable code.

```typescript
import { CanvasLCompiler } from 'mind-git';

const compiler = new CanvasLCompiler({
  targetLanguages: ['javascript', 'typescript'],
  optimizationLevel: 'medium',
  enableHopfOptimization: true,
  verifyNorms: true
});
```

#### Constructor Options
| Option | Type | Default | Description |
|---------|------|---------|-------------|
| targetLanguages | string[] | ['javascript'] | Target output languages |
| optimizationLevel | 'low' \| 'medium' \| 'high' | 'medium' | Compilation optimization level |
| enableHopfOptimization | boolean | true | Enable Hopf fibration optimizations |
| verifyNorms | boolean | true | Verify norm preservation |
| debug | boolean | false | Enable debug output |

#### Methods

##### compileCanvas(canvas: CanvasJSON): Promise<CompilationResult>
Compiles a canvas file to executable code.

```typescript
const result = await compiler.compileCanvas(canvas);

if (result.success) {
  console.log('Generated JavaScript:', result.generated_code.javascript_code);
  console.log('AST:', result.ast);
  console.log('Instructions:', result.aal_instructions);
} else {
  console.error('Compilation failed:', result.errors);
}
```

##### compileCanvasFile(filePath: string): Promise<CompilationResult>
Compiles a canvas file from disk.

```typescript
const result = await compiler.compileCanvasFile('my-canvas.canvas');
```

## 🧮 Mathematical Foundation

### PolyF2
Polynomial algebra over the binary field F₂.

```typescript
import { PolyF2 } from 'mind-git';

// Create polynomials from boolean arrays
const p1 = [true, false, true];  // 1 + x²
const p2 = [true, true, false];  // 1 + x

// Operations
const sum = PolyF2.add(p1, p2);        // Addition (XOR)
const product = PolyF2.multiply(p1, p2);  // Multiplication
const gcd = PolyF2.gcd(p1, p2);        // Greatest common divisor
const divmod = PolyF2.divmod(p1, p2);   // Division with remainder

// Properties
const degree = PolyF2.degree(p1);         // Polynomial degree
const norm = PolyF2.norm(p1);            // Polynomial norm
const eval = PolyF2.evaluate(p1, 1);     // Evaluate at x=1
```

### IdentityChain
Complete n-square identity chain from Brahmagupta to Pfister.

```typescript
import { IdentityChain } from 'mind-git';

// 2D Complex multiplication (Brahmagupta-Fibonacci)
const complex = IdentityChain.brahmagupta2([3, 4], [5, 12]);

// 4D Quaternion multiplication (Euler Four-Square)
const quaternion = IdentityChain.euler4([1, 2, 3, 4], [5, 6, 7, 8]);

// 8D Octonion multiplication (Degen Eight-Square)
const octonion = IdentityChain.degen8([1,2,3,4,5,6,7,8], [8,7,6,5,4,3,2,1]);

// 16D Sedenion multiplication (Pfister 16-Square)
const sedenion = IdentityChain.pfister16(octonion1, octonion2);

// 32D Trigintaduonion multiplication (Pfister 32-Square)
const trigintaduonion = IdentityChain.pfister32(sedenion1, sedenion2);

// Norm preservation verification
const normA = IdentityChain.norm(complex);
const normB = IdentityChain.norm([3, 4]);
const normProduct = IdentityChain.norm(complex);
console.log(normProduct === normA * normB); // true
```

### AAL (Assembly-Algebra Language)
11-dimensional graded modal type system.

```typescript
import { AAL, Dimension, AssemblyOp } from 'mind-git';

// Generate instruction
const instruction = AAL.generate_instruction(
  'transform',           // Node type
  { x: 100, y: 200 }, // Spatial position
  'Process data',        // Semantic label
  Dimension.D4           // Dimension level
);

// Execute instruction
const result = AAL.execute(instruction, context);

// Type operations
const isValid = AAL.validate_type(instruction, Dimension.D4);
const type = AAL.infer_type([instruction1, instruction2]);
```

## 📊 Data Structures

### CanvasJSON
Complete canvas file structure.

```typescript
interface CanvasJSON {
  nodes: CanvasNode[];
  edges: CanvasEdge[];
}

interface CanvasNode {
  id: string;
  type: 'text' | 'file' | 'link' | 'group';
  x: number;
  y: number;
  width: number;
  height: number;
  text: string;
  color?: string;
}

interface CanvasEdge {
  id: string;
  fromNode: string;
  toNode: string;
  label?: string;
  color?: string;
}
```

### CompilationResult
Result from canvas compilation.

```typescript
interface CompilationResult {
  success: boolean;
  ast?: AST;
  aal_instructions?: AALInstruction[];
  generated_code?: GeneratedCode;
  warnings?: string[];
  errors?: string[];
  complexity?: number;
  execution_time?: number;
}

interface GeneratedCode {
  javascript_code?: string;
  typescript_code?: string;
  racket_code?: string;
  webassembly_code?: string;
}
```

### AST (Abstract Syntax Tree)
Hierarchical representation of canvas structure.

```typescript
interface AST {
  nodes: ASTNode[];
  edges: ASTEdge[];
  functions: FunctionDefinition[];
  variables: VariableDefinition[];
  entryPoints: string[];
}

interface ASTNode {
  id: string;
  type: 'activate' | 'integrate' | 'propagate' | 'backpropagate' | 
         'transform' | 'verify' | 'store' | 'observe';
  position: { x: number; y: number };
  dimension: Dimension;
  instruction: AALInstruction;
  dependencies: string[];
  metadata: NodeMetadata;
}
```

## 🔧 Compiler Options

### Optimization Levels
| Level | Features | Performance |
|--------|----------|-------------|
| low | Basic parsing only | Fastest |
| medium | Standard optimizations | Balanced |
| high | Hopf + polynomial optimization | Slowest but best results |

### Target Languages
| Language | Status | Features |
|----------|---------|----------|
| JavaScript | ✅ Complete | Full execution |
| TypeScript | ✅ Complete | Type definitions |
| Racket | 🚧 In progress | 2AFA engine |
| WebAssembly | 🚧 In progress | Coq-verified |

### Verification Options
| Option | Description |
|---------|-------------|
| verifyNorms | Check norm preservation in identity chain |
| checkDimensions | Enforce Adams' theorem limits |
| validateTypes | Verify AAL type correctness |
| formalProofs | Generate Coq proof artifacts |

## 🎨 Usage Examples

### Basic Compilation
```typescript
import { CanvasLCompiler } from 'mind-git';

async function compileExample() {
  const compiler = new CanvasLCompiler();
  
  // Simple canvas with observer and one operation
  const canvas = {
    nodes: [
      { id: "obs", type: "text", x: 0, y: 0, width: 80, height: 30, text: "#Observe:" },
      { id: "op1", type: "text", x: 100, y: 0, width: 120, height: 30, text: "#Integrate: data" }
    ],
    edges: [
      { id: "e1", fromNode: "obs", toNode: "op1" }
    ]
  };
  
  const result = await compiler.compileCanvas(canvas);
  console.log(result.generated_code.javascript_code);
}
```

### Advanced Options
```typescript
const compiler = new CanvasLCompiler({
  targetLanguages: ['javascript', 'typescript'],
  optimizationLevel: 'high',
  enableHopfOptimization: true,
  verifyNorms: true,
  debug: false
});

const result = await compiler.compileCanvasFile('complex-canvas.canvas');
```

### Error Handling
```typescript
const result = await compiler.compileCanvas(canvas);

if (!result.success) {
  console.error('Compilation failed:');
  result.errors?.forEach(error => {
    console.error(`- ${error}`);
  });
  
  if (result.warnings) {
    console.warn('Warnings:');
    result.warnings.forEach(warning => {
      console.warn(`- ${warning}`);
    });
  }
}
```

## 🧮 Mathematical Constants

### Identity Chain Constants
```typescript
import { IDENTITY_CHAIN_CONSTANTS } from 'mind-git';

// Brahmagupta identity (2D)
IDENTITY_CHAIN_CONSTANTS.BRAHMAGUPTA_IDENTITY;

// Euler identity (4D)  
IDENTITY_CHAIN_CONSTANTS.EULER_IDENTITY;

// Degen identity (8D)
IDENTITY_CHAIN_CONSTANTS.DEGEN_IDENTITY;

// Pfister identity (16D+)
IDENTITY_CHAIN_CONSTANTS.PFISTER_IDENTITY;
```

### Dimension Constants
```typescript
import { Dimension } from 'mind-git';

// Assembly operations
Dimension.D0  // Linear transformations
Dimension.D1  // Polynomial addition
Dimension.D2  // Polynomial shift
Dimension.D3  // Polynomial comparison
Dimension.D4  // Polynomial multiplication
Dimension.D5  // Consensus voting
Dimension.D6  // Memory operations
Dimension.D7  // Quantum observation
```

## 🔍 Debugging and Diagnostics

### Debug Mode
```typescript
const compiler = new CanvasLCompiler({
  debug: true,
  verbose: true
});

// Detailed compilation output
const result = await compiler.compileCanvas(canvas);
// Includes: AST structure, instruction sequence, optimization details
```

### Performance Profiling
```typescript
const result = await compiler.compileCanvas(canvas);

console.log(`Compilation time: ${result.execution_time}ms`);
console.log(`Complexity score: ${result.complexity}`);
console.log(`Instructions generated: ${result.aal_instructions?.length}`);
```

### Validation
```typescript
import { CanvasLValidator } from 'mind-git';

const validator = new CanvasLValidator();

// Validate canvas structure
const structureErrors = validator.validateStructure(canvas);

// Verify mathematical constraints
const mathErrors = validator.validateMathematics(canvas);

// Check type consistency
const typeErrors = validator.validateTypes(canvas);
```

---

**This API provides complete access to CanvasL's mathematical foundation and visual programming capabilities.** 🎯