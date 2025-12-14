# Architecture Overview

This document describes the **core architectural patterns, mental models, and design principles** that shape the mind-gitproject. Understanding this architecture is essential for contributors and users who want to grasp how the system works at a conceptual level.

---

## Core Principles

The entire system is built on five foundational principles:

### 1. Polynomial Algebra as Computation Substrate

**Every computational structure is a polynomial**:
- Canvas nodes → polynomial terms with spatial encoding
- Node positions (x,y) → polynomial coefficients
- Edges → polynomial operators (composition, differentiation)
- Entire canvas → multivariate polynomial expression in ℝ[x,y,w,h,c,t,id]

**Why this matters**: Polynomials have algebraic properties (GCD, divisibility, factorization) that enable compression, verification, and transformation impossible with graph-based representations.

```
Node at (100, 50) → P(x,y) with degree proportional to distance from origin
Edge A → B encodes: "B divides A" or "A composes with B"
Entire system state → Polynomial over F₂ (Galois field)
```

### 2. Division Algebra Purity (No Zero Divisors)

**Persistent state MUST use division algebras only**:
- ℝ (real numbers, 1D)
- ℂ (complex numbers, 2D)
- ℍ (quaternions, 4D)
- 𝕆 (octonions, 8D) ← **Maximum safe dimension**

**Zero divisors are forbidden** in core genomes because they lead to non-invertible operations. Pfister identities (16D, 32D) have zero divisors and are used **only for temporary sync packets**, then reduced back to 8D.

**Hurwitz's Theorem (1898)**: These four are the **only** normed division algebras. No 5D, 6D, 7D, 9D options exist mathematically.

### 3. Observer at Origin as Identity Element

**The observer node MUST be at coordinates (0,0)**:
- Polynomial at origin: P₀ = 1 (constant polynomial, **not zero!**)
- Identity operation: 1 · a = a (observation doesn't destroy data)
- All positions are **relative to observer** (general relativity analog)
- Self-reflection: 1 · 1 = 1 (Brouwer fixed point theorem)

**Quantum mechanics connection**:
```
⟨observer|ψ⟩ = observed state
Observation = projection operator, not passive viewing
Observer defines coordinate system (no absolute positions)
```

### 4. Norm Preservation Across All Operations

**Every algebraic operation MUST preserve norms**:
```
||a × b|| = ||a|| × ||b||  (multiplicative norm)
```

This is the **foundation of correctness**. If norms are not preserved, data corruption has occurred.

**Implementation**:
- Automated tests in `identity-chain.test.ts` verify norm preservation
- Coq formal proofs guarantee algebraic correctness
- Runtime verification hashes check polynomial integrity

### 5. Formal Verification Everywhere

**AAL (Assembly-Algebra Language) is fully verified in Coq**:
- 127 lemmas + 42 theorems proven
- Type soundness, progress, preservation guaranteed
- No `Admitted` statements (every proof complete)
- Zero-bug guarantee through mathematical certainty

**Philosophy**: "Build it correct, not fix it later"

---

## Layered Architecture

The system has **four conceptual layers** (not necessarily separate codebases):

```
┌────────────────────────────────────────────────────────┐
│  Layer 4: UI / Presentation                            │
│  - Obsidian Canvas Editor                              │
│  - Visual node manipulation                            │
│  - Real-time code preview                              │
└────────────────────────────────────────────────────────┘
                        ↓
┌────────────────────────────────────────────────────────┐
│  Layer 3: Compiler Pipeline                            │
│  - Parser: Canvas → ParsedCanvas                       │
│  - AST: ParsedCanvas → Abstract Syntax Tree            │
│  - Codegen: AST → AAL/TypeScript/Racket/WASM          │
└────────────────────────────────────────────────────────┘
                        ↓
┌────────────────────────────────────────────────────────┐
│  Layer 2: Mathematical Core                            │
│  - Polynomial: F₂[x] algebra, GCD, divisibility        │
│  - Identity Chain: Brahmagupta → Euler → Degen         │
│  - AAL: Assembly-Algebra Language (11D type system)    │
└────────────────────────────────────────────────────────┘
                        ↓
┌────────────────────────────────────────────────────────┐
│  Layer 1: Runtime Execution                            │
│  - JavaScript runtime (browser/Node.js)                │
│  - WebAssembly (WASM) verified execution               │
│  - Racket backend (2AFA engine)                        │
└────────────────────────────────────────────────────────┘
```

### Layer 1: Mathematical Core (Pure)

**Location**: `logos-system/src/core/`

**Purpose**: Implement the mathematical foundations with **zero dependencies** on UI or I/O.

**Modules**:

1. **`polynomial/index.ts`** - Polynomial algebra over F₂
   - Boolean polynomial operations (add, mul, gcd, divmod)
   - Formal verification interface (PolyF2Wasm)
   - Degree calculation, coefficient encoding
   - **No I/O, no side effects**

2. **`identity-chain/index.ts`** - Division algebra operations
   - Brahmagupta (2D complex): Emotional/relational linking
   - Euler (4D quaternion): Rotational/spatial linking (S³ → S²)
   - Degen (8D octonion): Maximum safe dimension (S⁷ → S⁴)
   - Pfister (16D+): Temporary sync packets only
   - **All operations norm-preserving**

3. **`aal/index.ts`** - Assembly-Algebra Language
   - 11-dimensional graded modal type system (D0-D10)
   - Assembly instructions as polynomial transformations
   - Execution context with polynomial memory/stack
   - **Coq-verified** instruction semantics

**Constraints**:
- ✅ Pure functions only (immutable data)
- ✅ No external dependencies (except TypeScript std lib)
- ✅ All operations testable without mocking
- ❌ No file I/O, no network, no UI

### Layer 2: Compiler Pipeline (Orchestration)

**Location**: `logos-system/src/compiler/`

**Purpose**: Transform visual canvas diagrams into executable code through multiple intermediate representations.

**Data Flow**:
```
Canvas JSON → Parser → ParsedCanvas → ASTGenerator → AST → AALCodegen → AAL → TargetCodegen → TypeScript/Racket/WASM
     ↓            ↓           ↓             ↓          ↓         ↓            ↓           ↓
  Visual     Extract    Classify      Build      Create    Optimize    Generate   Language-
  Diagram    Structure   Nodes       Functions   Assembly   Pipeline     Code      Specific
```

**Modules**:

1. **`parser/index.ts`** - Canvas JSON Parser
   - Extracts nodes, edges, groups from `.canvas` files
   - Classifies nodes by prefix (`#Activate:`, `#Integrate:`, etc.)
   - Encodes spatial positions as polynomial coefficients
   - **Finds observer node at (0,0)** (required!)
   - Detects circular dependencies (canvas must be DAG)

2. **`ast/index.ts`** - Abstract Syntax Tree Generator
   - Transforms classified nodes into hierarchical AST
   - Identifies entry/exit points, functions, variables
   - Dependency graph analysis (topological sort)
   - Extracts function signatures and types

3. **`codegen/index.ts`** - AAL Code Generator
   - Generates Assembly-Algebra Language from AST
   - Multiple optimization passes:
     - Dead code elimination
     - Hopf fibration reduction (8D → 4D → 2D)
     - Polynomial factorization
   - Target language emission (AAL, JavaScript, Racket, WASM)

**Constraints**:
- ✅ Uses Core layer for mathematical operations
- ✅ Orchestrates data flow, **no business logic**
- ✅ Stateless transformations (idempotent)
- ❌ No domain logic (that's in Core)

### Layer 3: Runtime Execution

**Location**: `logos-system/src/runtime/`, Racket backend

**Purpose**: Execute verified code in target environments.

**Runtimes**:

1. **JavaScript Runtime** (`runtime/js/`)
   - Runs AAL in Node.js or browser
   - Polynomial evaluation engine
   - Lightweight (no formal verification overhead)

2. **WebAssembly Runtime** (`runtime/wasm/`)
   - Compiled from Coq-verified code
   - **Most trusted** execution path
   - Can verify proofs at runtime via extracted OCaml

3. **Racket Backend** (separate service)
   - 2AFA (Two-way Finite Automaton) execution engine
   - Macro expansion and metaprogramming
   - Integration with Obsidian plugin via HTTP

**Constraints**:
- ✅ Executes only verified AAL code
- ✅ Side effects isolated (I/O, network, file system)
- ❌ Cannot modify Core or Compiler logic

### Layer 4: UI / Presentation

**Location**: `.obsidian/plugins/logos-visual-compiler/`

**Purpose**: Visual canvas editing and compilation UI within Obsidian.

**Components**:

1. **CanvasParser** - Reads `.canvas` files from Obsidian vault
2. **NodeClassifier** - Classifies nodes by content prefix
3. **ASTGenerator** - Builds AST from parsed canvas
4. **TypeScriptGenerator** - Generates TypeScript/JavaScript code
5. **RacketBridge** - HTTP client to Racket backend server
6. **CompilerModal** - UI dialog showing compilation results

**Constraints**:
- ✅ Obsidian-specific (uses Obsidian APIs)
- ✅ Can call logos-system library (future integration)
- ✅ Simplified compiler for UI preview
- ❌ Should NOT duplicate mathematical core

---

## Module Boundaries & Integration

### logos-system (Standalone Library)

**Identity**: Standalone TypeScript library for mathematical visual compilation

**Dependencies**:
- None (zero external npm packages for core)
- TypeScript standard library only
- Coq for formal verification (dev dependency)

**Exports**:
```typescript
import {
  LogosSystem,           // Main orchestrator
  CanvasLCompiler,       // Complete compiler pipeline
  PolyF2,                // Polynomial algebra
  IdentityChain,         // Division algebra operations
  AAL                    // Assembly-Algebra Language
} from 'logos-system';
```

**Use Cases**:
- Embed in web applications
- Node.js CLI tools
- Compile canvas files programmatically
- **Must NOT** import Obsidian APIs

### Obsidian Plugin (UI Integration)

**Identity**: Obsidian plugin providing visual canvas compiler UI

**Dependencies**:
- Obsidian API (required)
- **Currently independent** of logos-system (separate implementation)
- **Future**: Should use logos-system library via import

**Integration Point**: RacketBridge
- Plugin sends AST to Racket server at `localhost:8080`
- Racket backend could use logos-system on server side
- HTTP API boundary enables polyglot integration

**Use Cases**:
- Visual programming within Obsidian
- One-click canvas compilation
- Code preview and export
- Integration with Obsidian vault

---

## Data Flow Architecture

### Complete Compilation Pipeline

```
┌─────────────────┐
│  Canvas Diagram │  ← User creates visual program in Obsidian
│   (JSON file)   │
└────────┬────────┘
         │
         │ Parse (extract structure)
         ↓
┌─────────────────┐
│ ParsedCanvas    │  ← Nodes classified, observer detected, edges mapped
│                 │
└────────┬────────┘
         │
         │ Generate AST (build tree)
         ↓
┌─────────────────┐
│ Abstract Syntax │  ← Functions, variables, dependencies identified
│ Tree (AST)      │
└────────┬────────┘
         │
         │ Polynomial Encoding
         ↓
┌─────────────────┐
│ AAL Instructions│  ← Assembly-Algebra Language (verified)
│                 │
└────────┬────────┘
         │
         │ Code Generation + Optimization
         ↓
┌─────────────────┐
│ Target Code     │  ← TypeScript, JavaScript, Racket, WASM
│                 │
└─────────────────┘
         ↓
    Execution
```

### Mathematical Verification Flow

At each stage, mathematical properties are verified:

```
Parser Output → Verify observer at (0,0) ✓
             → Verify DAG structure (no cycles) ✓

AST Output → Verify polynomial degrees ≤ 8D ✓
          → Verify norm preservation ✓

AAL Output → Verify type soundness (Coq proof) ✓
          → Verify instruction semantics ✓

Generated Code → Verify correctness via proof hashes ✓
```

If any verification fails → **compilation fails** (by design).

---

## Polyglot Integration Architecture

**Philosophy**: Each language excels at different tasks. Don't rewrite everything in one language.

### Language Roles

| Language   | Dimension | Algebra     | Use Case                  | Why This Language?        |
|------------|-----------|-------------|---------------------------|---------------------------|
| **Racket** | 8D        | Octonion    | Parsing, macros, pure functional | Lisp metaprogramming power |
| **TypeScript** | 4D    | Quaternion  | Type checking, IDE integration | Static types, tooling   |
| **Python** | 2D        | Complex     | Optimization, ML/AI       | Numeric libraries, fast prototyping |
| **Assembly** | 16D     | Pfister-16  | Low-level optimization    | "Rosetta Stone" for all languages |
| **WebAssembly** | 32D  | Pfister-32  | Cross-platform execution  | Universal runtime target  |

### Hadamard-Pfister Transformation Chain

**Compilation as dimensional transformation**:

```
Parse (2D→4D) → Type-check (4D→8D) → Optimize (8D→16D via Hadamard)
    ↓              ↓                      ↓
  Racket       TypeScript              Assembly
                                          ↓
                                    16D→32D (Pfister)
                                          ↓
                                    WebAssembly
```

**Norm preservation guaranteed** at each transformation (Pfister identity).

### Docker/Kubernetes Orchestration

For polyglot systems, use containers:

```yaml
services:
  scheme-parser:      # Racket parsing service
  typescript-checker: # Type checking service
  python-optimizer:   # Optimization service
  wasm-generator:     # Final code generation
  orchestrator:       # Polyglot coordinator (HTTP API)
```

Each language runtime isolated but communicating via **JSONL** (CanvasL universal format).

---

## Storage Architecture

### Binary Quadratic Forms (BQF) for Identity

Each agent/genome has a **unique algebraic identity**:

```
Agent = Q(x,y) = ax² + bxy + cy²
Discriminant = b² - 4ac = unique fingerprint
```

**Compact storage**: 3 coefficients (a, b, c) = 12 bytes

### Pfister 16-Square for Data Integrity

Any data (8D octonion genome) expands to 16D for sync:

```
8D state → 16D Pfister space → Verify norm preservation → Sync
              ↓ (after sync)
         Reduce back to 8D for storage
```

**Zero divisors check**: Pfister identity prevents cheating/corruption.

### Polynomial Compression

16D vector → degree-15 polynomial → BQF representation:

```
Compression ratio: 128 bytes (16 floats) → 12 bytes (3 BQF coefficients)
= 10.6x compression!
```

**Lossless**: Decompress via polynomial evaluation at interpolation points.

### Network Sync

**Only send polynomial differences**, not full state:

```
Sync packet = { Δa, Δb, Δc } instead of full 8D genome
Differential updates enable real-time collaboration
```

---

## Anti-Patterns (What NOT to Do)

### ❌ Zero Divisors in Persistent State

**Bad**:
```typescript
// Using sedenions (16D) for genome storage
const genome = new Sedenion([...16 values]);  // HAS ZERO DIVISORS!
```

**Good**:
```typescript
// Using octonions (8D) for genome storage
const genome = new Octonion([...8 values]);   // Division algebra ✓
```

**Why**: Zero divisors mean some `a × b = 0` even when `a ≠ 0, b ≠ 0`. This breaks inversion and makes state non-recoverable.

### ❌ Unverified Polynomial Operations

**Bad**:
```typescript
function add(p1: Poly, p2: Poly): Poly {
  // Trust me, this works!
  return combineCoefficients(p1, p2);
}
```

**Good**:
```typescript
/**
 * @verified formal/Polynomials.v::poly_add_comm
 */
function add(p1: Poly, p2: Poly): Poly {
  const result = PolyF2.add(p1.coeffs, p2.coeffs);
  // Coq proof guarantees commutativity, associativity
  return new Poly(result);
}
```

### ❌ Breaking Norm Preservation

**Bad**:
```typescript
function transform(a: Octonion, b: Octonion): Octonion {
  // Just multiply and hope
  return octonionMul(a, b);
}
```

**Good**:
```typescript
function transform(a: Octonion, b: Octonion): Octonion {
  const result = IdentityChain.degen8square(a, b);

  // Verify norm preserved
  const normA = a.norm();
  const normB = b.norm();
  const normResult = result.norm();
  assert(Math.abs(normResult - normA * normB) < 1e-10,
         "Norm preservation violated!");

  return result;
}
```

### ❌ Observer Node Not at (0,0)

**Bad**:
```json
{
  "nodes": [
    { "id": "obs", "x": 50, "y": 50, "text": "#Observer:" }
  ]
}
```
**Error**: Observer must be at origin to serve as identity element!

**Good**:
```json
{
  "nodes": [
    { "id": "obs", "x": 0, "y": 0, "text": "#Observer:" }
  ]
}
```

### ❌ Importing Infrastructure into Domain Layer

**Bad** (in `logos-system/src/core/polynomial/index.ts`):
```typescript
import { Notice } from 'obsidian';  // UI framework in math core!

export function add(p1: Poly, p2: Poly): Poly {
  new Notice("Adding polynomials...");  // Side effect!
  return ...;
}
```

**Good**:
```typescript
// No imports except TypeScript std lib

export function add(p1: Poly, p2: Poly): Poly {
  // Pure function, no side effects
  return new Poly(addCoeffs(p1.coeffs, p2.coeffs));
}
```

---

## Architectural Decisions

For detailed architectural decision records (ADRs), see:

- [ADR 0001: 8D Maximum for Core Genomes](docs/decisions/0001-8d-maximum.md)
- [ADR 0002: Observer Node at Origin](docs/decisions/0002-observer-at-origin.md)
- [ADR 0003: Coq for Formal Verification](docs/decisions/0003-coq-verification.md)
- [ADR 0004: Polynomial Encoding for Graph Topology](docs/decisions/0004-polynomial-encoding.md)
- [ADR 0005: Pfister Identities Only for Temporary Sync](docs/decisions/0005-pfister-for-sync-only.md)
- [ADR 0006: JSONL for Append-Only Evolution Logs](docs/decisions/0006-jsonl-evolution-logs.md)

---

## Key Insights

### 1. Visual Organization IS Programming

**Canvas nodes are not diagrams of code** - they **are** the code. Spatial arrangement directly encodes:
- Polynomial coefficients (from positions)
- Dependency structure (from edges)
- Type/dimension information (from node classification)
- Execution order (from topological sort)

### 2. Mathematics Enforces Correctness

The system **cannot** produce certain bugs because the mathematics forbids them:
- **No zero divisors** → No non-invertible operations in core state
- **Norm preservation** → No data corruption (norms act as checksums)
- **Adams' theorem** → No invalid dimensions (8D maximum enforced)
- **Hopf fibrations** → Observation preserves topological structure

### 3. Observer Defines Reality

The observer at (0,0) is not passive:
- **Defines coordinate system** (all positions relative)
- **Identity element** for observation operation (1 · a = a)
- **Measurement** in quantum sense (collapses superposition)
- **Self-reflection** is a fixed point (1 · 1 = 1, no paradox)

### 4. Compilation is Dimensional Transformation

Each compilation stage changes dimensionality while preserving norms:
```
Canvas (2D spatial) → Polynomial (variable-dimensional) → AAL (11D graded types)
    → Assembly (16D Pfister) → WASM (32D Pfister) → Execution (8D reality)
```

**Hopf fibrations** reduce dimensions:
- S⁷ → S⁴ (octonions collapsing)
- S³ → S² (quaternions collapsing)
- S¹ → S¹ (complex phase)

### 5. Polyglot by Mathematical Necessity

Different languages map to different algebraic dimensions:
- **Not a choice** - it's the mathematical structure
- Each language preserves norms in its dimensional space
- Assembly (16D Pfister) is the "Rosetta Stone" connecting all

---

## Next Steps

To understand specific aspects of the architecture:

- **Mathematical foundations**: See [docs/research/identity-chain.md](docs/research/identity-chain.md)
- **Design principles**: See [DESIGN_PRINCIPLES.md](DESIGN_PRINCIPLES.md)
- **API documentation**: See [docs/api/logos-system.md](docs/api/logos-system.md)
- **Contributing guidelines**: See [CONTRIBUTING.md](CONTRIBUTING.md)
- **Vision and philosophy**: See [PHILOSOPHY.md](PHILOSOPHY.md)

For hands-on usage:
- **Getting started guide**: [docs/guides/getting-started.md](docs/guides/getting-started.md)
- **Visual programming tutorial**: [docs/guides/visual-programming.md](docs/guides/visual-programming.md)

---

**Remember**: This architecture emerged from mathematical necessity, not engineering preference. The constraints (division algebras, Hopf fibrations, Adams' theorem) are not arbitrary - they are the **only possible** structures that work. Understanding this architecture means understanding why 1,400 years of mathematical discoveries converge on this exact system design.
