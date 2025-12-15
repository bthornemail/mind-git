---
id: "mind-git:architecture:module-boundaries"
title: "Module Boundaries and Code Organization"
type: ["architecture","system"]
category: architecture
layer: 3
dimensions: [0, 1, 2, 4, 8, 9, 16]
mathematicalFoundation: ["polynomial-algebra","identity-chain","formal-verification","division-algebras"]
hopfCompatible: false
normPreserving: true
status: "complete"
completeness: 95
tags: ["documentation","canvasl","mathematics","compiler","ast","api","polynomial","algebra"]
keywords: ["canvasl","aal","ast","compiler","polynomial","algebra","mathematics","formal","verification","coq","proof","octonion","identity","chain","typescript","javascript"]
lastUpdate: "2025-12-15"

---

# Module Boundaries and Code Organization

## Mental Model

**"Clear boundaries enable mathematical purity."**

Think of it as concentric circles: pure mathematics at the center, with increasingly impure layers outward. Code can only depend inward, never outward.

---

## Directory Structure Overview

```
mind-git/
├── logos-system/                    ← Standalone mathematical library
│   ├── src/
│   │   ├── core/                   ← Layer 1: Pure mathematics
│   │   │   ├── polynomial/         ← F₂[x] algebra
│   │   │   ├── identity-chain/     ← Division algebra operations
│   │   │   └── aal/                ← Assembly-Algebra Language
│   │   ├── compiler/               ← Layer 2: Pipeline orchestration
│   │   │   ├── parser/             ← Canvas → ParsedCanvas
│   │   │   ├── ast/                ← ParsedCanvas → AST
│   │   │   └── codegen/            ← AST → Target code
│   │   └── runtime/                ← Layer 3: Execution engines
│   │       ├── js/                 ← JavaScript runtime
│   │       ├── wasm/               ← WebAssembly runtime
│   │       └── racket/             ← Racket backend interface
│   ├── formal/                     ← Coq formal verification
│   └── tests/                      ← Comprehensive test suite
├── .obsidian/plugins/              ← Layer 4: UI integration
│   └── logos-visual-compiler/      ← Obsidian plugin
├── docs/                           ← Documentation
├── dev-docs/                       ← Development documentation
└── examples/                       ← Example canvases and code
```

---

## logos-system (Standalone Library)

### Identity
**Pure TypeScript library for mathematical visual compilation**

### Dependencies
- **Zero external npm packages** for core
- TypeScript standard library only
- Coq for formal verification (dev dependency)

### Exports
```typescript
import {
  LogosSystem,           // Main orchestrator
  CanvasLCompiler,       // Complete compiler pipeline
  PolyF2,                // Polynomial algebra
  IdentityChain,         // Division algebra operations
  AAL                    // Assembly-Algebra Language
} from 'logos-system';
```

### Boundary Rules
- ✅ **Can import**: TypeScript standard library only
- ✅ **Can export**: All mathematical operations
- ❌ **Cannot import**: UI frameworks, Node.js APIs, browser APIs
- ❌ **Cannot depend**: Obsidian, React, Vue, or any framework

### Use Cases
- Embed in web applications
- Node.js CLI tools
- Compile canvas files programmatically
- Mathematical research

### File: `logos-system/package.json`
```json
{
  "name": "logos-system",
  "version": "1.0.0",
  "description": "Mathematical visual compilation library",
  "main": "dist/index.js",
  "types": "dist/index.d.ts",
  "dependencies": {},  // ZERO dependencies!
  "devDependencies": {
    "coq": "^8.16.0",
    "typescript": "^5.0.0"
  },
  "peerDependencies": {},  // No framework requirements
}
```

---

## Layer 1: Mathematical Core (`logos-system/src/core/`)

### Purpose
**Implement pure mathematical foundations with zero external dependencies.**

### Modules

#### `polynomial/` - F₂[x] Algebra
```typescript
// File: polynomial/index.ts
export class PolyF2 {
  // Pure functions only - no side effects
  static add(p: Polynomial, q: Polynomial): Polynomial { ... }
  static mul(p: Polynomial, q: Polynomial): Polynomial { ... }
  static gcd(p: Polynomial, q: Polynomial): Polynomial { ... }
  
  // No external dependencies
  // No I/O operations
  // No framework imports
}
```

**Boundary Rules**:
- ✅ **Can import**: TypeScript std lib only
- ✅ **Can export**: Polynomial operations
- ❌ **Cannot import**: Other core modules (circular dependency risk)
- ❌ **Cannot have**: Side effects, I/O, external APIs

#### `identity-chain/` - Division Algebra Operations
```typescript
// File: identity-chain/index.ts
import { PolyF2 } from '../polynomial';  // Only inward import!

export class IdentityChain {
  // 2D: Brahmagupta-Fibonacci identity
  static brahmagupta(a: number[], b: number[]): number[] { ... }
  
  // 4D: Euler four-square identity
  static euler4(a: number[], b: number[], c: number[], d: number[]): number[] { ... }
  
  // 8D: Degen eight-square identity (MAXIMUM SAFE)
  static degen8(octonion: number[]): number[] { ... }
}
```

**Boundary Rules**:
- ✅ **Can import**: `polynomial/` (inward)
- ✅ **Can export**: Division algebra operations
- ❌ **Cannot import**: `aal/` (outward)
- ❌ **Cannot use**: 16D+ for persistent state

#### `aal/` - Assembly-Algebra Language
```typescript
// File: aal/index.ts
import { PolyF2 } from '../polynomial';
import { IdentityChain } from '../identity-chain';

export interface AALInstruction {
  opcode: OpCode;
  operands: Operand[];
  dimension: Dimension;  // D0-D10
  proof_hash: string;    // Coq verification
}

export class AAL {
  static execute(instruction: AALInstruction): AALResult { ... }
  static verify(instruction: AALInstruction): boolean { ... }
}
```

**Boundary Rules**:
- ✅ **Can import**: `polynomial/`, `identity-chain/` (inward)
- ✅ **Can export**: AAL operations and types
- ❌ **Cannot import**: Compiler, runtime, UI (outward)
- ❌ **Cannot have**: Side effects, network calls

---

## Layer 2: Compiler Pipeline (`logos-system/src/compiler/`)

### Purpose
**Orchestrate data flow from visual canvas to executable code.**

### Import Rules (CRITICAL)
```typescript
// ✅ GOOD: Import from core (inward)
import { PolyF2 } from '../core/polynomial';
import { AAL } from '../core/aal';

// ❌ BAD: Import from runtime (outward)
import { JavaScriptRuntime } from '../runtime/js';  // FORBIDDEN!

// ❌ BAD: Import from UI (outward)
import { Notice } from 'obsidian';  // FORBIDDEN!
```

### Modules

#### `parser/` - Canvas JSON Parser
```typescript
// File: parser/index.ts
import { PolyF2 } from '../../core/polynomial';  // Inward import OK

export class CanvasParser {
  static parse(canvas: CanvasJSON): ParsedCanvas {
    // Extract structure, no business logic
    const nodes = this.extractNodes(canvas);
    const observer = this.findObserver(nodes);  // Must be at (0,0)
    const polynomials = nodes.map(n => 
      PolyF2.fromPosition(n.x, n.y)  // Use core math
    );
    
    return new ParsedCanvas(nodes, polynomials, observer);
  }
}
```

**Boundary Rules**:
- ✅ **Can import**: All core modules
- ✅ **Can export**: Parsed canvas structures
- ❌ **Cannot import**: Runtime, UI layers
- ❌ **Cannot have**: Business logic (delegate to core)

#### `ast/` - Abstract Syntax Tree Generator
```typescript
// File: ast/index.ts
import { PolyF2 } from '../../core/polynomial';
import { IdentityChain } from '../../core/identity-chain';

export class ASTGenerator {
  static generate(parsed: ParsedCanvas): AST {
    // Build tree structure, no mathematical operations
    const graph = this.buildDependencyGraph(parsed.nodes);
    const sorted = graph.topologicalSort();  // Must be DAG
    
    return new AST(sorted, parsed.types);
  }
}
```

**Boundary Rules**:
- ✅ **Can import**: All core modules
- ✅ **Can export**: AST structures and generators
- ❌ **Cannot import**: Codegen (circular dependency risk)
- ❌ **Cannot have**: Execution logic

#### `codegen/` - Code Generation
```typescript
// File: codegen/index.ts
import { AAL } from '../../core/aal';
import { IdentityChain } from '../../core/identity-chain';

export class TypeScriptCodegen {
  static generate(ast: AST): string {
    // Generate code, no execution
    const instructions = AAL.fromAST(ast);
    const optimized = this.optimize(instructions);
    
    return this.emitTypeScript(optimized);
  }
}
```

**Boundary Rules**:
- ✅ **Can import**: All core modules
- ✅ **Can export**: Generated code
- ❌ **Cannot import**: Runtime (would create circular dependency)
- ❌ **Cannot execute**: Generated code (delegate to runtime)

---

## Layer 3: Runtime Execution (`logos-system/src/runtime/`)

### Purpose
**Execute verified code with controlled side effects.**

### Import Rules
```typescript
// ✅ GOOD: Import from compiler and core
import { AAL } from '../core/aal';
import { TypeScriptCodegen } from '../compiler/codegen';

// ❌ BAD: Import from UI (outward)
import { Modal } from 'obsidian';  // FORBIDDEN!
```

### Modules

#### `js/` - JavaScript Runtime
```typescript
// File: js/index.ts
import { AAL } from '../../core/aal';

export class JavaScriptRuntime {
  async execute(aalCode: string): Promise<ExecutionResult> {
    // Execute AAL in JavaScript environment
    const instructions = AAL.parse(aalCode);
    const results = [];
    
    for (const instr of instructions) {
      const result = await this.executeInstruction(instr);
      results.push(result);
    }
    
    return new ExecutionResult(results);
  }
}
```

#### `wasm/` - WebAssembly Runtime
```typescript
// File: wasm/index.ts
import { AAL } from '../../core/aal';

export class WebAssemblyRuntime {
  async load(): Promise<void> {
    // Load Coq-verified WebAssembly module
    this.module = await WebAssembly.compile(wasmBytes);
  }
  
  async execute(aalCode: string): Promise<ExecutionResult> {
    // Execute with formal verification
    const verified = await this.verifyCode(aalCode);
    return this.module.execute(verified);
  }
}
```

#### `racket/` - Racket Backend Interface
```typescript
// File: racket/index.ts
import { TypeScriptCodegen } from '../compiler/codegen';

export class RacketBridge {
  async compileToRacket(ast: AST): Promise<string> {
    // Generate Racket code from AST
    const tsCode = TypeScriptCodegen.generate(ast);
    const racketCode = await this.convertToRacket(tsCode);
    
    return racketCode;
  }
  
  async executeRacket(code: string): Promise<any> {
    // Send to Racket server for execution
    const response = await fetch('http://localhost:8080/execute', {
      method: 'POST',
      body: JSON.stringify({ code })
    });
    
    return response.json();
  }
}
```

---

## Layer 4: UI Integration (`.obsidian/plugins/`)

### Purpose
**Provide visual canvas editing and compilation UI within Obsidian.**

### Boundary Rules
- ✅ **Can import**: All layers (UI needs everything)
- ✅ **Can use**: Obsidian APIs (required for plugin)
- ✅ **Can have**: Side effects, DOM manipulation
- ❌ **Should not duplicate**: Core mathematical logic

### Key Files

#### `src/parsers/NodeClassifier.ts`
```typescript
// UI-specific node classification
export function classifyNode(node: CanvasNode): ClassifiedNode | null {
  const content = node.text || '';
  const prefix = content.match(/^#(\w+):/)?.[1]?.toLowerCase();
  
  switch (prefix) {
    case 'activate':
      return {
        id: node.id,
        type: 'activate',
        assemblyOp: 'JMP',  // D0 linear transformation
        dimension: { from: '0D', to: '0D' },
        rawContent: content,
        position: { x: node.x, y: node.y }
      };
    // ... other cases
  }
}
```

#### `src/generators/TypeScriptGenerator.ts`
```typescript
// Simplified code generation for UI preview
export class TypeScriptGenerator {
  generate(nodes: ClassifiedNode[]): string {
    const functions = nodes.map(node => 
      this.generateFunction(node)
    );
    
    return functions.join('\n\n');
  }
  
  private generateFunction(node: ClassifiedNode): string {
    // Quick generation for preview, not production
    return `function ${node.rawContent.split(':')[1].trim()}() {
  // Generated from canvas node
}`;
  }
}
```

#### `src/RacketBridge.ts`
```typescript
// HTTP client to Racket backend
export class RacketBridge {
  async compile(canvas: CanvasJSON): Promise<CompilationResult> {
    // Send canvas to Racket server
    const response = await fetch('http://localhost:8080/compile', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(canvas)
    });
    
    return response.json();
  }
}
```

---

## Cross-Cutting Concerns

### Testing Boundaries
```typescript
// ✅ GOOD: Test core with pure unit tests
describe('PolyF2', () => {
  it('should preserve commutativity', () => {
    const a = PolyF2.from([true, false]);
    const b = PolyF2.from([false, true]);
    
    expect(PolyF2.add(a, b)).toEqual(PolyF2.add(b, a));
  });
});

// ✅ GOOD: Test compiler with integration tests
describe('CanvasLCompiler', () => {
  it('should compile canvas to AAL', () => {
    const canvas = createTestCanvas();
    const result = CanvasLCompiler.compile(canvas);
    
    expect(result.status).toBe('success');
    expect(result.aal).toBeDefined();
  });
});

// ❌ BAD: Test UI with core logic
describe('ObsidianPlugin', () => {
  it('should test polynomial math', () => {
    // Don't test core math in UI tests!
    // Test UI behavior only.
  });
});
```

### Error Handling Across Boundaries
```typescript
// Core: Mathematical errors
export class NormPreservationError extends Error {
  constructor(message: string) {
    super(`Norm preservation violated: ${message}`);
  }
}

// Compiler: Compilation errors
export class ParseError extends Error {
  constructor(message: string, public node?: CanvasNode) {
    super(`Parse error: ${message}`);
  }
}

// Runtime: Execution errors
export class ExecutionError extends Error {
  constructor(message: string, public instruction?: AALInstruction) {
    super(`Execution error: ${message}`);
  }
}

// UI: User errors
export class UserError extends Error {
  constructor(message: string, public suggestion?: string) {
    super(`User error: ${message}`);
  }
}
```

### Configuration Management
```typescript
// Core: No configuration (mathematical constants)
export const MAX_DIMENSION = 8;  // Mathematical limit, not config

// Compiler: Compilation options
export interface CompilerOptions {
  optimizationLevel: number;
  targetLanguage: 'typescript' | 'racket' | 'wasm';
  verificationLevel: 'strict' | 'relaxed';
}

// Runtime: Execution options
export interface RuntimeOptions {
  timeout: number;
  memory: number;
  debug: boolean;
}

// UI: User preferences
export interface UserPreferences {
  theme: 'light' | 'dark';
  autoCompile: boolean;
  showProofHashes: boolean;
}
```

---

## Migration Path

### Adding New Modules

1. **Determine the layer**:
   - Pure math? → `core/`
   - Data transformation? → `compiler/`
   - Execution? → `runtime/`
   - User interface? → Plugin

2. **Check dependencies**:
   - Can import from inward layers only
   - No circular dependencies
   - Follow boundary rules

3. **Write tests**:
   - Unit tests for core
   - Integration tests for compiler
   - End-to-end tests for runtime
   - UI tests for plugin

### Refactoring Across Layers

```typescript
// Moving logic DOWNWARD (safer)
// From compiler to core
export function extractMathematicalOperation(compilerLogic: any) {
  // Extract pure mathematical part
  const pureMath = isolateMathematicalCore(compilerLogic);
  
  // Move to core
  // core/math/new-operation.ts
  
  // Update compiler to use core
  // compiler/updated-logic.ts
}

// Moving logic UPWARD (riskier)
// From core to compiler
export function extractIOOperation(coreLogic: any) {
  // Only if core needs I/O (should be rare)
  // Move I/O part to compiler
  // Keep core pure
}
```

---

## Related Documentation

- [../overview.md](../overview.md) - Mental model introduction
- [layers.md](layers.md) - Layer architecture details
- [../research/](../research/) - Mathematical foundations
- [../../CONTRIBUTING.md](../../CONTRIBUTING.md) - Development guidelines

---

**Remember**: These boundaries exist for mathematical purity, not just engineering organization. The inward-only dependency rule ensures that the mathematical core remains pure, verifiable, and trustworthy. Every violation of these boundaries compromises the mathematical integrity of the system.