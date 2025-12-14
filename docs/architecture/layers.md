# The Four-Layer Architecture

## Mental Model

**Pure mathematics at the center, wrapped by increasingly impure layers.**

Like an onion: mathematical core → orchestration → execution → presentation. Each layer can only depend on layers more central than itself.

---

## Layer Overview

```
┌────────────────────────────────────────────────────────┐
│  Layer 4: UI / Presentation                            │
│  - Obsidian Canvas Editor                              │
│  - Visual node manipulation                            │
│  - Real-time code preview                              │
└────────────────────────────────────────────────────────┘
                         ↓ (imports)
┌────────────────────────────────────────────────────────┐
│  Layer 3: Runtime Execution                            │
│  - JavaScript runtime (browser/Node.js)                │
│  - WebAssembly (WASM) verified execution               │
│  - Racket backend (2AFA engine)                        │
└────────────────────────────────────────────────────────┘
                         ↓ (imports)
┌────────────────────────────────────────────────────────┐
│  Layer 2: Compiler Pipeline                            │
│  - Parser: Canvas → ParsedCanvas                       │
│  - AST: ParsedCanvas → Abstract Syntax Tree            │
│  - Codegen: AST → AAL/TypeScript/Racket/WASM          │
└────────────────────────────────────────────────────────┘
                         ↓ (imports)
┌────────────────────────────────────────────────────────┐
│  Layer 1: Mathematical Core                            │
│  - Polynomial: F₂[x] algebra, GCD, divisibility        │
│  - Identity Chain: Brahmagupta → Euler → Degen         │
│  - AAL: Assembly-Algebra Language (11D type system)    │
└────────────────────────────────────────────────────────┘
```

---

## Layer 1: Mathematical Core (Pure)

### Location
`logos-system/src/core/`

### Purpose
Implement the mathematical foundations with **zero dependencies** on anything external.

### Key Characteristics
- ✅ **Pure functions only** (no side effects)
- ✅ **Immutable data structures**
- ✅ **No external dependencies** (except TypeScript std lib)
- ✅ **Mathematically proven** (Coq verification)
- ❌ **No I/O, no network, no UI**

### Modules

#### `polynomial/` - F₂[x] Algebra
```typescript
// Boolean polynomial operations
const sum = PolyF2.add(p, q);        // XOR addition
const product = PolyF2.mul(p, q);   // Convolution multiplication
const gcd = PolyF2.gcd(p, q);       // Greatest common divisor
```

**Mathematical foundation**: Galois field of order 2, all operations verified in Coq.

#### `identity-chain/` - Division Algebra Operations
```typescript
// 2D: Brahmagupta-Fibonacci identity
const complex = IdentityChain.brahmagupta(a, b);

// 4D: Euler four-square identity  
const quaternion = IdentityChain.euler4(a, b, c, d);

// 8D: Degen eight-square identity (MAXIMUM SAFE)
const octonion = IdentityChain.degen8(a, b, c, d, e, f, g, h);
```

**Mathematical foundation**: Only 1, 2, 4, 8 dimensions allow normed division algebras (Hurwitz's theorem).

#### `aal/` - Assembly-Algebra Language
```typescript
// 11-dimensional graded modal type system
const instruction: AALInstruction = {
  opcode: 'MUL',
  operands: [reg1, reg2],
  dimension: 'D4',  // Quaternion multiplication
  proof_hash: 'sha256:...'
};
```

**Mathematical foundation**: 127 lemmas + 42 theorems proven in Coq, zero `Admitted` statements.

### Constraints
- **No imports** from outer layers
- **No side effects** (pure functions)
- **Immutable data** (readonly interfaces)
- **Formal verification** required for all operations

---

## Layer 2: Compiler Pipeline (Orchestration)

### Location
`logos-system/src/compiler/`

### Purpose
Transform visual canvas diagrams into executable code through multiple intermediate representations.

### Key Characteristics
- ✅ **Stateless transformations** (idempotent)
- ✅ **Uses Layer 1** for mathematical operations
- ✅ **Orchestrates data flow** (no business logic)
- ✅ **Multiple target languages** (TypeScript, Racket, WASM)
- ❌ **No domain logic** (delegates to Layer 1)

### Data Flow
```
Canvas JSON → Parser → ParsedCanvas → ASTGenerator → AST → AALCodegen → AAL → TargetCodegen → Executable
```

### Modules

#### `parser/` - Canvas JSON Parser
```typescript
// Extract structure from visual diagram
const parsed = CanvasParser.parse(canvasJSON);

// Classify nodes by prefix
const nodes = parsed.nodes.filter(n => n.type === 'activate');

// Encode positions as polynomial coefficients
const polynomials = nodes.map(n => 
  PolyF2.fromPosition(n.x, n.y)
);
```

**Key responsibilities**:
- Find observer node at (0,0) (required!)
- Classify nodes by prefix (`#Activate:`, `#Integrate:`, etc.)
- Encode spatial positions as polynomial coefficients
- Detect circular dependencies (canvas must be DAG)

#### `ast/` - Abstract Syntax Tree Generator
```typescript
// Build hierarchical structure from classified nodes
const ast = ASTGenerator.build(parsed);

// Identify functions and dependencies
const functions = ast.extractFunctions();
const dependencies = ast.analyzeDependencies();

// Topological sort for execution order
const sorted = ast.topologicalSort();
```

**Key responsibilities**:
- Transform flat node list into hierarchical AST
- Identify entry/exit points and function boundaries
- Dependency graph analysis (must be DAG)
- Extract type information and signatures

#### `codegen/` - AAL Code Generator
```typescript
// Generate Assembly-Algebra Language
const aal = AALCodegen.generate(ast);

// Optimize with mathematical passes
const optimized = AALCodegen.optimize(aal, [
  'dead-code-elimination',
  'hopf-fibration-reduction',  // 8D → 4D → 2D
  'polynomial-factorization'
]);

// Generate target language
const typescript = TypeScriptCodegen.generate(optimized);
```

**Key responsibilities**:
- Generate AAL instructions from AST nodes
- Multiple optimization passes (mathematical, not heuristic)
- Target language emission (TypeScript, Racket, WASM)
- Embed verification hashes in generated code

### Constraints
- **Can import Layer 1** (uses mathematical operations)
- **Cannot import Layer 3+** (no runtime, no UI)
- **Stateless transformations** (same input → same output)
- **No side effects** (pure orchestration)

---

## Layer 3: Runtime Execution (Side Effects)

### Location
`logos-system/src/runtime/`, Racket backend service

### Purpose
Execute verified code in target environments with controlled side effects.

### Key Characteristics
- ✅ **Executes only verified AAL code**
- ✅ **Side effects isolated** (I/O, network, file system)
- ✅ **Multiple runtime targets** (JS, WASM, Racket)
- ✅ **Performance optimized** (sub-millisecond operations)
- ❌ **Cannot modify Layers 1-2** (execution only)

### Runtime Targets

#### JavaScript Runtime
```typescript
// Execute AAL in Node.js or browser
const runtime = new JavaScriptRuntime();
const result = await runtime.execute(aalCode);

// Polynomial evaluation engine
const polynomials = runtime.evaluatePolynomials(expressions);
```

**Use case**: Lightweight execution, no formal verification overhead.

#### WebAssembly Runtime
```typescript
// Execute Coq-verified code
const wasm = await WebAssemblyRuntime.load();
const result = await wasm.execute(aalCode);

// Runtime verification via extracted proofs
const verified = wasm.verifyProof(result.proofHash);
```

**Use case**: Most trusted execution path, cryptographic verification.

#### Racket Backend
```scheme
;; 2AFA (Two-way Finite Automaton) execution
(define (execute-aal ast)
  (aal->2afa ast))  ;; Transform to 2AFA
  (run-2afa ast))   ;; Execute with metaprogramming
```

**Use case**: Parsing, macros, pure functional execution.

### Constraints
- **Can import Layers 1-2** (uses compiler output)
- **Cannot modify compiler or core** (execution only)
- **Side effects controlled** (isolated from pure math)
- **Performance critical** (optimization matters)

---

## Layer 4: UI / Presentation (Interface)

### Location
`.obsidian/plugins/logos-visual-compiler/`

### Purpose
Visual canvas editing and compilation UI within Obsidian.

### Key Characteristics
- ✅ **Obsidian-specific** (uses Obsidian APIs)
- ✅ **Real-time compilation** (instant feedback)
- ✅ **Visual manipulation** (drag-and-drop nodes)
- ✅ **Code preview** (generated TypeScript/JavaScript)
- ❌ **Should NOT duplicate mathematical core**

### Components

#### CanvasParser
```typescript
// Read .canvas files from Obsidian vault
const canvas = await CanvasParser.readFile(file.vaultPath);

// Parse visual structure
const parsed = CanvasParser.parse(canvas);
```

#### NodeClassifier
```typescript
// Classify nodes by content prefix
const classified = NodeClassifier.classifyAll(canvas.nodes);

// Validate mathematical constraints
const validation = NodeClassifier.validate(classified);
```

#### ASTGenerator
```typescript
// Build AST from parsed canvas
const ast = ASTGenerator.build(classified);

// Real-time error reporting
const errors = ast.validate();
```

#### TypeScriptGenerator
```typescript
// Generate preview code
const code = TypeScriptGenerator.generate(ast);

// Live preview updates
preview.update(code);
```

#### RacketBridge
```typescript
// Send AST to Racket backend
const response = await RacketBridge.compile(ast);

// Display compilation results
modal.showResults(response);
```

### Constraints
- **Can import all layers** (UI needs everything)
- **Obsidian API dependency** (platform-specific)
- **Simplified compiler** (for UI preview, not production)
- **No mathematical core duplication** (use logos-system)

---

## Inter-Layer Communication

### Dependency Rules
```
Layer 4 → Layer 3 → Layer 2 → Layer 1
```
- **Outer layers can import inner layers**
- **Inner layers CANNOT import outer layers**
- **Circular dependencies forbidden**

### Data Flow Between Layers
```
Layer 4: Canvas JSON
    ↓
Layer 2: Parse → AST → AAL
    ↓  
Layer 1: Mathematical operations
    ↓
Layer 2: Code generation
    ↓
Layer 3: Execute
    ↓
Layer 4: Display results
```

### Error Propagation
```typescript
// Layer 1: Mathematical errors
throw new NormPreservationError("||a × b|| ≠ ||a|| × ||b||");

// Layer 2: Compilation errors  
throw new ParseError("Observer not found at (0,0)");
throw new CircularDependencyError("Canvas must be DAG");

// Layer 3: Runtime errors
throw new ExecutionError("AAL instruction failed");

// Layer 4: UI errors
throw new UserError("Invalid node position");
```

---

## Benefits of This Architecture

### 1. Mathematical Purity
Core mathematics is isolated from all external concerns, enabling formal verification and mathematical certainty.

### 2. Testability
Each layer can be tested independently:
- Layer 1: Property-based mathematical tests
- Layer 2: Compilation pipeline tests
- Layer 3: Runtime execution tests  
- Layer 4: UI integration tests

### 3. Flexibility
Can swap implementations:
- Different runtimes (JS, WASM, Racket)
- Different UIs (Obsidian, VS Code, web)
- Different targets (TypeScript, Python, C++)

### 4. Performance
Optimization at each layer:
- Layer 1: Mathematical optimization
- Layer 2: Compilation optimization
- Layer 3: Runtime optimization
- Layer 4: UI responsiveness

### 5. Security
Clear security boundaries:
- Layer 1: Mathematically proven correct
- Layer 2: Verified compilation pipeline
- Layer 3: Sandboxed execution
- Layer 4: Controlled UI access

---

## Migration Path

If you need to refactor across layers:

### 1. Moving Logic Downward (Safer)
```typescript
// From Layer 2 to Layer 1 (good)
// Move mathematical operation to core for reuse
```

### 2. Moving Logic Upward (Riskier)
```typescript
// From Layer 1 to Layer 2 (careful)
// Only if it needs I/O or external dependencies
```

### 3. Adding New Layers
```typescript
// Add Layer 2.5 between compiler and runtime
// For optimization, caching, etc.
```

---

## Related Documentation

- [../overview.md](../overview.md) - Mental model introduction
- [data-flow.md](data-flow.md) - Complete pipeline details
- [module-boundaries.md](module-boundaries.md) - Code organization rules
- [verification-architecture.md](verification-architecture.md) - Formal verification pipeline

---

**Remember**: This layered architecture emerged from separating pure mathematics from impure reality. Each layer boundary exists for mathematical necessity, not engineering preference.