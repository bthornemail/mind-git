# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

**mind-git** implements CanvasL - a visual programming language that transforms spatial diagrams (Obsidian Canvas files) into mathematically verified executable programs. The system embodies 1,400 years of mathematical development, from Brahmagupta's complex numbers (628 AD) to Adams' proof of dimensional limits (1960).

The core innovation: **visual spatial arrangement of canvas nodes directly corresponds to polynomial algebra over F₂**, with formal verification via Coq proofs and execution through a multi-language compilation pipeline.

## Architecture

The system has three main components that work together:

### 1. Logos System (`logos-system/`)
The mathematical engine and compiler pipeline:
- **Core Mathematical Foundation** (`src/core/`):
  - `polynomial/`: Polynomial algebra over F₂ (binary field) with Coq formalization
  - `identity-chain/`: Complete n-square identity chain (Brahmagupta → Euler → Degen → Pfister)
  - `aal/`: Assembly-Algebra Language with 11-dimensional graded modal type system (D0-D10)
- **Compiler Pipeline** (`src/compiler/`):
  - `parser/`: Parses Canvas JSON and classifies nodes by mathematical prefixes
  - `ast/`: Generates abstract syntax tree from spatial canvas structure
  - `codegen/`: Multi-language code generation (AAL, JavaScript, TypeScript, Racket, WebAssembly)
- **Formal Verification** (`formal/`):
  - Coq proofs for polynomial operations (`Polynomials.v`)
  - Coq proofs for identity chain norm preservation (`IdentityChain.v`)
  - Makefile for proof verification and WebAssembly extraction

### 2. Obsidian Plugin (`.obsidian/plugins/logos-visual-compiler/`)
Visual interface for compiling canvas files within Obsidian:
- Parses `.canvas` files from Obsidian vault
- Classifies nodes using mathematical prefixes (`#Activate:`, `#Integrate:`, etc.)
- Displays AST structure and compilation results
- Generates TypeScript and Racket code via modal UI
- Integrates with Racket backend server for advanced compilation

### 3. Racket Backend Integration
Multi-language compilation server:
- `racket-server.rkt`: Full-featured HTTP server with code generation
- `racket-server-minimal.rkt`: Lightweight version for testing
- `test-integration.sh`: Integration test script for end-to-end verification

## Mathematical Foundation

### Critical Constraints (NEVER violate these):
1. **Adams' Theorem**: Only dimensions 1, 2, 4, 8 support normed division algebras
2. **Hopf Fibrations**: Only exist for S¹, S³, S⁷ (degrees 1, 3, 7)
3. **Norm Preservation**: Identity chain operations must satisfy `||a × b|| = ||a|| × ||b||` exactly
4. **8D Ceiling**: 8 dimensions is the absolute mathematical maximum for division algebras

### Canvas Node Classification
Nodes are classified by text prefix, mapping to assembly operations and dimensions:

| Prefix | Assembly Op | Dimension | Mathematical Meaning |
|--------|-------------|-----------|---------------------|
| `#Activate:` | JMP/CALL | D0 | Linear transformation |
| `#Integrate:` | ADD/SUB | D1 | Polynomial addition |
| `#Propagate:` | SHL/SHR | D2 | Polynomial shift |
| `#BackPropagate:` | CMP | D3 | Polynomial comparison |
| `#Transform:` | MUL/DIV | D4 | Polynomial multiplication |
| `#Verify:` | VOTE | D5 | Consensus voting |
| `#Store:` | PUSH/POP | D6 | Memory stack operation |
| `#Observe:` | SYNC | D7 | Quantum observation |

### Observer Pattern
The node at coordinates (0, 0) serves as the identity element (P₀ = 1) in polynomial algebra. Node distance from observer determines polynomial degree.

## Development Commands

### Logos System (Mathematical Engine)
```bash
# Development
cd logos-system
npm install
npm run build          # Compile TypeScript to JavaScript
npm run dev            # Watch mode for development
npm test              # Run all tests (unit + formal verification)

# Testing
npm run test:unit      # Run Jest unit tests only
npm run test:formal    # Verify Coq proofs
npm run verify         # Run Coq verification directly

# Formal Verification
cd formal
make verify           # Compile Coq proofs
make all              # Build and extract to WebAssembly
make clean            # Clean build artifacts
```

### Obsidian Plugin
```bash
# Development
cd .obsidian/plugins/logos-visual-compiler
npm install
npm run dev            # Watch mode with hot reload
npm run build          # Production build

# Testing
./test-integration.sh  # Full integration test with Racket server
```

### Racket Backend
```bash
# Start server (choose one):
racket racket-server-minimal.rkt    # Minimal server on port 8080
racket racket-server.rkt            # Full-featured server

# Test endpoints:
curl http://localhost:8080/health                    # Health check
curl -X POST http://localhost:8080/generate \        # Code generation
  -H "Content-Type: application/json" \
  -d '{"nodes": [...], "edges": [...]}'
```

## Code Quality & Testing

### Before Committing
1. **Run full test suite**: `npm test` in `logos-system/`
2. **Verify Coq proofs**: `cd formal && make verify`
3. **Check TypeScript compilation**: `npm run build`
4. **Run integration tests**: `./test-integration.sh`

### After File Edits (REQUIRED by Cursor rules)
- Run `codacy_cli_analyze` tool from Codacy MCP Server for each edited file
- After dependency changes, run `codacy_cli_analyze` with `tool: "trivy"` for security checks

### Test Files
- Unit tests: `logos-system/src/**/*.test.ts`
- Formal verification: `logos-system/formal/*.v`
- Integration: `test-integration.sh`

## Key Implementation Patterns

### Polynomial Operations (F₂ Algebra)
All polynomials use boolean coefficient arrays over the binary field F₂:
```typescript
// Example: 1 + x² is represented as [true, false, true]
const p1 = [true, false, true];  // 1 + x²
const p2 = [true, true, false];  // 1 + x
const sum = PolyF2.add(p1, p2);  // x + x² (XOR operation)
```

### Identity Chain Implementation
Follows the historical chain with exact norm preservation:
```typescript
// Brahmagupta (2D): (a₁² + a₂²)(b₁² + b₂²) = (c₁² + c₂²)
const complex = IdentityChain.brahmagupta2([3, 4], [5, 12]);

// Euler (4D): Four-square identity
const quaternion = IdentityChain.euler4([1, 2, 3, 4], [5, 6, 7, 8]);

// Degen (8D): Eight-square identity
const octonion = IdentityChain.degen8([1,2,3,4,5,6,7,8], [8,7,6,5,4,3,2,1]);
```

### Canvas Compilation Pipeline
The compilation follows this strict order:
1. **Parse**: Canvas JSON → Classified nodes with spatial metadata
2. **AST**: Nodes + edges → Hierarchical tree with dependencies
3. **Codegen**: AST → AAL assembly → Target language (JS/TS/Racket/WASM)
4. **Verify**: Generated code → Proof hash → Formal verification check

### AAL (Assembly-Algebra Language)
11-dimensional graded modal type system with proof tracking:
```typescript
const instruction = AAL.generate_canvasl_instruction(
  'activate',              // Node type
  { x: 100, y: 200 },     // Spatial position
  'Initialize computation' // Semantic label
);
```

## Important Conventions

### File Organization
- **Never create new files** unless absolutely necessary - always prefer editing existing files
- TypeScript strict mode is enforced throughout
- All mathematical operations require comprehensive JSDoc comments explaining the mathematical reasoning
- Coq formalization must match TypeScript implementation exactly

### Naming Conventions
- Mathematical types: PascalCase (`Polynomial`, `Vector8D`)
- Functions: camelCase with mathematical context (`brahmagupta2`, `compute_norm_preserving_product`)
- Constants: SCREAMING_SNAKE_CASE for mathematical constants (`IDENTITY_CHAIN_CONSTANTS`)
- Files: kebab-case (`identity-chain.ts`, `polynomial.test.ts`)

### Documentation Requirements
When adding mathematical operations:
1. Add JSDoc with mathematical formula in LaTeX-style notation
2. Include historical context if part of identity chain
3. Reference Coq theorem by name in comments
4. Add comprehensive test cases covering edge cases
5. Update formal verification proofs to match

### Performance Requirements
- Polynomial operations: Sub-millisecond for degree ≤ 100
- Identity chain operations: Constant time O(1)
- AST traversal: O(n) where n = number of canvas nodes
- Code generation: Linear with respect to node count

## Integration with External Systems

### Obsidian Canvas Format
Canvas files are JSON with this structure:
```json
{
  "nodes": [
    {
      "id": "unique-id",
      "type": "text" | "file" | "link" | "group",
      "x": 100, "y": 200,
      "width": 250, "height": 60,
      "text": "#Activate: main"
    }
  ],
  "edges": [
    {
      "id": "edge-id",
      "fromNode": "node-id-1",
      "toNode": "node-id-2",
      "label": "optional-label"
    }
  ]
}
```

### Racket Server API
The Racket backend expects AST-like JSON:
```json
{
  "nodes": [...],
  "edges": [...],
  "functions": [...],
  "variables": [...],
  "entryPoints": [...]
}
```

## Philosophical Context (from AGENTS.md)

This project has a unique philosophical foundation that shapes development decisions:

- **Mathematical Certainty**: Every operation must be formally verified - mathematics doesn't lie
- **Dimensional Transference**: The 8D limit isn't arbitrary - it's fundamental to reality (Adams' Theorem)
- **Observer Pattern**: The (0,0) position as identity element reflects deep mathematical structure
- **Vision**: Building computational substrate for evolving systems, not just another compiler

When making architectural decisions, prioritize:
1. Mathematical correctness above performance
2. Formal verification above convenience
3. Preservation of dimensional constraints above feature additions
4. Maintaining the identity chain lineage exactly as historically proven

## Common Gotchas

1. **Polynomial Coefficients**: Always use boolean arrays over F₂, never integers
2. **Norm Preservation**: Test with `||a × b|| === ||a|| × ||b||` exactly, not approximately
3. **Dimension Limits**: Never attempt to extend beyond 8D - it's mathematically impossible
4. **Observer Position**: (0,0) is special - don't use it for regular computation nodes
5. **Hopf Optimization**: Only applicable for degrees 1, 3, 7 - check before applying
6. **WebAssembly Integration**: Coq proof extraction requires specific build flags (see `formal/Makefile`)

## Project Status

Current implementation (v1.0.0):
- ✅ Complete mathematical foundation with formal verification
- ✅ Canvas parser with node classification
- ✅ AST generation from spatial structure
- ✅ Multi-language code generation (AAL, TypeScript, Racket)
- ✅ Obsidian plugin with visual UI
- ✅ Racket backend integration
- ✅ Coq formalization for core operations

See README.md for roadmap of future phases (WebGL visualization, P2P canvas sharing, AI/ML integration).
