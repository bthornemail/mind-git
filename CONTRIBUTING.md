# Contributing to mind-git

Thank you for your interest in contributing! This project implements a formally verified visual compiler based on 1,400 years of mathematical identities. We welcome contributions that maintain our mathematical rigor while advancing the vision.

---

## Table of Contents

- [Prerequisites](#prerequisites)
- [Getting Started](#getting-started)
- [Development Workflow](#development-workflow)
- [Adding New Features](#adding-new-features)
- [Testing Guidelines](#testing-guidelines)
- [Documentation Requirements](#documentation-requirements)
- [Code Style](#code-style)
- [Community Guidelines](#community-guidelines)

---

## Prerequisites

### Knowledge Requirements

- **Mathematical background**: Understanding of abstract algebra helpful (polynomials, groups, rings, division algebras)
- **TypeScript**: Intermediate to advanced level
- **Formal methods**: Familiarity with Coq is a plus (but not required for all contributions)
- **Obsidian** (optional): For visual canvas plugin development

### Tools Required

- **Node.js** 18+ and npm
- **Git** for version control
- **TypeScript** 5.0+
- **Coq** 8.16+ (optional, for formal verification work)
- **Obsidian** (optional, for plugin development)

---

## Getting Started

### 1. Clone and Setup

```bash
# Clone repository
git clone https://github.com/bthornemail/mind-git.git
cd mind-git

# Install dependencies
npm install

# Setup logos-system library
cd logos-system
npm install
cd ..

# Setup Obsidian plugin
cd .obsidian/plugins/logos-visual-compiler
npm install
cd ../../..
```

### 2. Build Everything

```bash
# Build logos-system library
cd logos-system
npm run build
cd ..

# Build Obsidian plugin
cd .obsidian/plugins/logos-visual-compiler
npm run build
cd ../../..
```

### 3. Run Tests

```bash
# Run all tests
cd logos-system
npm test

# Run specific test suite
npm test -- identity-chain.test.ts

# Run tests in watch mode (for development)
npm run test:watch
```

### 4. Verify Formal Proofs (Optional)

```bash
# Compile Coq proofs
cd logos-system/formal
make verify

# If proofs fail, check:
# - No Admitted statements
# - All lemmas and theorems proven
# - Makefile dependencies correct
```

---

## Development Workflow

### Branch Strategy

- **`main`** - Production-ready code, protected branch
- **`obsidian-plugin`** - Plugin development (current active branch)
- **`feature/description`** - Feature branches (e.g., `feature/hopf-optimization`)
- **`fix/issue-number`** - Bug fixes (e.g., `fix/123-parser-crash`)

### Creating a Feature Branch

```bash
# Update main or obsidian-plugin
git checkout obsidian-plugin
git pull origin obsidian-plugin

# Create feature branch
git checkout -b feature/your-feature-name

# Make changes...
git add .
git commit -m "feat(module): description"

# Push to GitHub
git push origin feature/your-feature-name
```

### Commit Message Convention

Follow [Conventional Commits](https://www.conventionalcommits.org/):

```
<type>(<scope>): <description>

[optional body]

[optional footer]
```

**Types**:
- `feat`: New feature
- `fix`: Bug fix
- `docs`: Documentation changes
- `test`: Adding or updating tests
- `refactor`: Code refactoring (no behavior change)
- `perf`: Performance improvements
- `chore`: Build process, dependencies, tooling

**Examples**:
```bash
feat(compiler): add Hopf fibration optimization pass
fix(parser): handle observer at non-origin positions
docs(architecture): clarify identity chain explanation
test(polynomial): verify GCD properties with property-based tests
refactor(aal): extract instruction validation to separate function
```

### Pull Request Process

1. **Create feature branch** from `main` or `obsidian-plugin`

2. **Implement with tests** - No untested mathematical operations!

3. **Verify mathematics** - Run full test suite:
   ```bash
   npm test  # All tests must pass
   ```

4. **Update documentation** - If adding features or changing APIs:
   - Update `README.md` if user-facing
   - Add/update ADR in `docs/decisions/` if architectural
   - Update API docs in `docs/api/` if changing interfaces

5. **Submit PR** with clear description:
   ```markdown
   ## Description
   Clear description of the change

   ## Mathematical Justification
   Why this approach? Which theorems support it?

   ## Test Results
   - All tests pass: ✓
   - Norms preserved: ✓
   - Coq proofs updated: ✓ (if applicable)

   ## Breaking Changes
   List any breaking changes and migration path
   ```

### Code Review Checklist

Reviewers will check:

**Mathematical Correctness**:
- [ ] Tests verify algebraic properties (commutativity, associativity, etc.)
- [ ] Norm preservation maintained (if touching identity chain)
- [ ] No zero divisors introduced in persistent state (8D maximum)
- [ ] Observer remains at (0,0) (if touching parser)

**Software Quality**:
- [ ] TypeScript types precise (no `any` unless absolutely necessary)
- [ ] Domain objects immutable (`readonly` on all domain types)
- [ ] No framework imports in core (`logos-system/src/core/`)
- [ ] Error handling via Result types (not bare exceptions)

**Documentation**:
- [ ] Mathematical rationale documented (comments with equations/references)
- [ ] API documentation updated (if changing public interfaces)
- [ ] Examples provided (for new features)

**Coq Proofs** (if touching AAL):
- [ ] Proofs compile without errors
- [ ] No `Admitted` statements
- [ ] Theorems match implementation

---

## Adding New Features

### Where Does Logic Belong?

```
logos-system/src/
├── core/               ← Pure mathematics (no IO, no UI)
│   ├── polynomial/     ← F₂[x] algebra, immutable operations
│   ├── identity-chain/ ← Division algebra, norm preservation
│   └── aal/            ← Assembly-Algebra Language, verified
├── compiler/           ← Orchestration (uses core, no domain logic)
│   ├── parser/         ← Canvas → ParsedCanvas (extraction only)
│   ├── ast/            ← ParsedCanvas → AST (transformation only)
│   └── codegen/        ← AST → Code (generation only)
└── runtime/            ← Execution (JavaScript/WASM, no compilation)
```

**Rules**:
- **Core** = pure functions, mathematical operations, zero dependencies
- **Compiler** = pipeline orchestration, no business logic, stateless
- **Runtime** = side effects only (I/O, network, file system), no compilation logic

### Example: Adding a New Node Type

Let's add a `#Differentiate:` node for mathematical differentiation.

#### Step 1: Update Node Classifier

**File**: `.obsidian/plugins/logos-visual-compiler/src/parsers/NodeClassifier.ts`

```typescript
export function classifyNode(node: CanvasNode): ClassifiedNode | null {
  const content = node.text || '';
  const prefix = content.match(/^#(\w+):/)?.[1]?.toLowerCase();

  // ... existing cases ...

  if (prefix === 'differentiate') {
    return {
      id: node.id,
      type: 'differentiate',
      assemblyOp: 'differentiate',  // Custom assembly operation
      dimension: { from: '3D', to: '4D' },  // Increases dimension
      rawContent: content,
      position: { x: node.x, y: node.y }
    };
  }

  return null;
}
```

#### Step 2: Add to AST Types

**File**: `.obsidian/plugins/logos-visual-compiler/src/types/ast.ts`

```typescript
export type NodeType =
  | 'activate'
  | 'integrate'
  | 'transform'
  | 'store'
  | 'observe'
  | 'differentiate';  // Add new type
```

#### Step 3: Implement Code Generation

**File**: `.obsidian/plugins/logos-visual-compiler/src/generators/TypeScriptGenerator.ts`

```typescript
private generateFunction(node: ASTNode): string {
  const name = this.extractFunctionName(node.content);

  switch (node.type) {
    // ... existing cases ...

    case 'differentiate':
      return this.generateDifferentiation(name, node);

    default:
      return `function ${name}() { /* Unknown type: ${node.type} */ }`;
  }
}

private generateDifferentiation(name: string, node: ASTNode): string {
  /**
   * Mathematical rationale:
   * Numerical differentiation using central difference formula:
   * f'(x) ≈ [f(x+h) - f(x-h)] / (2h)
   *
   * This is O(h²) accurate (vs O(h) for forward/backward difference)
   */
  return `
/**
 * ${name} - Numerical differentiation
 * Uses central difference formula for better accuracy
 */
function ${name}(f: (x: number) => number, h: number = 0.0001): (x: number) => number {
  return (x: number) => {
    const forward = f(x + h);
    const backward = f(x - h);
    return (forward - backward) / (2 * h);
  };
}`.trim();
}
```

#### Step 4: Write Tests

**File**: `logos-system/src/compiler/parser/parser.test.ts`

```typescript
describe('NodeClassifier', () => {
  it('should classify differentiate nodes', () => {
    const node: CanvasNode = {
      id: '1',
      type: 'text',
      text: '#Differentiate: derivative',
      x: 100,
      y: 200
    };

    const classified = classifyNode(node);

    expect(classified).not.toBeNull();
    expect(classified?.type).toBe('differentiate');
    expect(classified?.dimension).toEqual({ from: '3D', to: '4D' });
    expect(classified?.assemblyOp).toBe('differentiate');
  });

  it('should generate correct differentiation code', () => {
    const ast: ASTNode = {
      id: '1',
      type: 'differentiate',
      content: '#Differentiate: derivative',
      degree: 3,
      dependencies: []
    };

    const generator = new TypeScriptGenerator();
    const code = generator.generate([ast]);

    expect(code).toContain('function derivative(');
    expect(code).toContain('central difference');
  });
});
```

#### Step 5: Update Documentation

**File**: `docs/guides/visual-programming.md`

Add new node type documentation:

```markdown
### Differentiate Nodes

**Prefix**: `#Differentiate:`

**Purpose**: Computes numerical derivatives of functions

**Dimension**: 3D → 4D (increases complexity)

**Example**:
\`\`\`
#Differentiate: derivative

// Generates:
function derivative(f, h = 0.0001) {
  return x => (f(x + h) - f(x - h)) / (2 * h);
}
\`\`\`

**Mathematical Foundation**: Central difference formula with O(h²) accuracy
```

### Adding a Coq Proof

If you're modifying AAL semantics or adding verified operations:

#### Step 1: Update Coq Specification

**File**: `logos-system/formal/AAL.v`

```coq
(* Add new instruction type *)
Inductive instr : Type :=
  | IAdd : instr
  | IMul : instr
  | IDiff : instr    (* NEW: Differentiation instruction *)
  | ...

(* Define semantics *)
Definition eval_instr (i : instr) (st : state) : option state :=
  match i with
  | IDiff =>
      (* Differentiation semantics *)
      match st.(stack) with
      | f :: h :: rest =>
          Some {| stack := (differentiate f h) :: rest;
                  memory := st.(memory) |}
      | _ => None
      end
  | ...
  end.

(* Prove correctness *)
Theorem differentiate_preserves_continuity :
  forall f x,
  continuous f ->
  continuous (differentiate f).
Proof.
  intros f x Hcont.
  (* Your proof here *)
  unfold continuous.
  unfold differentiate.
  (* ... proof steps ... *)
Qed.
```

#### Step 2: Compile Proof

```bash
cd logos-system/formal
coqc AAL.v

# Should compile without errors
# No "Admitted" statements allowed!
```

#### Step 3: Update TypeScript Implementation

**File**: `logos-system/src/core/aal/index.ts`

```typescript
/**
 * Differentiation instruction
 *
 * @verified formal/AAL.v::differentiate_preserves_continuity
 *
 * Coq theorem guarantees that differentiation preserves
 * continuity of input functions.
 */
export function executeDiff(
  stack: Stack,
  memory: Memory
): AALExecutionResult {
  const f = stack.pop();
  const h = stack.pop();

  if (!f || !h) {
    return { status: 'error', error: 'Stack underflow' };
  }

  const derivative = differentiate(f, h);
  stack.push(derivative);

  return { status: 'success', stack, memory };
}
```

---

## Testing Guidelines

### Unit Tests

**Test algebraic properties**, not just specific examples:

```typescript
import fc from 'fast-check';

describe('Polynomial Addition', () => {
  // Good: Property-based test
  it('should be commutative: a + b = b + a', () => {
    fc.assert(
      fc.property(
        fc.array(fc.boolean()),  // Random polynomial
        fc.array(fc.boolean()),
        (coeffsA, coeffsB) => {
          const a = Polynomial.from(coeffsA);
          const b = Polynomial.from(coeffsB);

          const ab = a.add(b);
          const ba = b.add(a);

          expect(ab.equals(ba)).toBe(true);
        }
      )
    );
  });

  // Also good: Test invariants
  it('should preserve norm in multiplication', () => {
    fc.assert(
      fc.property(
        fc.array(fc.boolean()),
        fc.array(fc.boolean()),
        (coeffsA, coeffsB) => {
          const a = Polynomial.from(coeffsA);
          const b = Polynomial.from(coeffsB);
          const product = a.mul(b);

          const normA = a.norm();
          const normB = b.norm();
          const normProduct = product.norm();

          // Norm must be preserved
          expect(normProduct).toBeCloseTo(normA * normB, 10);
        }
      )
    );
  });
});
```

### Integration Tests

Test the **full pipeline**:

```typescript
describe('Complete Compilation Pipeline', () => {
  it('should compile canvas to executable TypeScript', async () => {
    const canvas: CanvasJSON = {
      nodes: [
        { id: 'obs', x: 0, y: 0, text: '#Observer:', type: 'text' },
        { id: 'act', x: 100, y: 50, text: '#Activate: main', type: 'text' }
      ],
      edges: [
        { id: 'e1', fromNode: 'obs', toNode: 'act' }
      ]
    };

    const compiler = new CanvasLCompiler();
    const result = await compiler.compileCanvas(canvas);

    // Verify compilation succeeded
    expect(result.status).toBe('success');

    // Verify mathematical verification
    expect(result.verification.overall_status).toBe('verified');
    expect(result.verification.polynomial_verified).toBe(true);

    // Verify generated code is valid
    expect(result.generated_code.typescript).toContain('function main(');

    // Verify it's executable
    const fn = eval(result.generated_code.typescript);
    expect(typeof fn).toBe('function');
  });
});
```

### Mathematical Verification Tests

**Always verify mathematical properties**:

```typescript
it('should satisfy Brahmagupta-Fibonacci identity', () => {
  // (a² + b²)(c² + d²) = (ac - bd)² + (ad + bc)²
  const a = 3, b = 4;
  const c = 5, d = 12;

  const lhs = (a * a + b * b) * (c * c + d * d);
  const rhs = (a * c - b * d) ** 2 + (a * d + b * c) ** 2;

  expect(lhs).toBe(rhs);  // Identity must hold exactly
});

it('should satisfy Degen 8-square identity', () => {
  // (∑ aᵢ²)(∑ bᵢ²) = ∑ cᵢ²
  const a = Octonion.random();
  const b = Octonion.random();
  const c = a.mul(b);

  const lhs = a.norm() * b.norm();
  const rhs = c.norm();

  expect(rhs).toBeCloseTo(lhs, 10);  // Norm preservation
});
```

---

## Documentation Requirements

### When to Update Docs

- **New abstractions**: Add to `docs/architecture/`
- **API changes**: Update `docs/api/`
- **Design decisions**: Create ADR in `docs/decisions/`
- **Usage patterns**: Update `docs/guides/`
- **Mathematical foundations**: Update `dev-docs/`

### Mathematical Documentation Standards

All core mathematical operations need:

1. **LaTeX equations** in comments
2. **References** to theorems/papers
3. **Worked examples** in tests

**Example**:

```typescript
/**
 * Degen 8-square identity (1928)
 *
 * Multiplicative norm-preserving bilinear map on octonions:
 *
 * (a₁² + a₂² + ... + a₈²)(b₁² + b₂² + ... + b₈²) = c₁² + c₂² + ... + c₈²
 *
 * where cᵢ are bilinear functions of aⱼ and bₖ:
 *   c = a × b (octonion multiplication)
 *
 * This is the MAXIMUM dimension for division algebras (Adams' theorem).
 *
 * References:
 * - Degen, W. (1928). "Über die achtfache Zerlegung..."
 * - Hurwitz, A. (1898). "Über die Composition der quadratischen Formen"
 * - Adams, J.F. (1960). "On the non-existence of elements of Hopf invariant one"
 *
 * @param a - Octonion (8D) with norm ||a||
 * @param b - Octonion (8D) with norm ||b||
 * @returns Product c = a × b with norm ||c|| = ||a|| × ||b||
 *
 * @verified formal/IdentityChain.v::degen_preserves_norm
 */
export function degen8square(a: Octonion, b: Octonion): Octonion {
  // Implementation...
}
```

---

## Code Style

### TypeScript Standards

- **Strict mode**: Always enabled in `tsconfig.json`
- **Prefer `const`** over `let`
- **Use `readonly`** for immutable data
- **Explicit types** for public APIs (no type inference)
- **Functional style** in `core/`, imperative OK in `compiler/`

### Naming Conventions

- **Types**: `PascalCase` (`ParsedCanvas`, `ASTNode`, `Polynomial`)
- **Functions**: `camelCase` (`parseCanvas`, `generateAST`, `compileToAAL`)
- **Constants**: `SCREAMING_SNAKE_CASE` (`MAX_DIMENSION`, `OBSERVER_POSITION`)
- **Files**: `kebab-case` (`identity-chain.ts`, `ast-generator.ts`, `canvas-parser.ts`)

### File Organization

```typescript
// 1. Imports (external first, then internal)
import * as fc from 'fast-check';
import { Polynomial } from '../polynomial';
import { Octonion } from './octonion';

// 2. Types and interfaces
export interface Config {
  dimension: number;
  verificationLevel: number;
}

// 3. Constants
const DEFAULT_OPTIMIZATION = 3;
const MAX_DIMENSION = 8;

// 4. Main exports (classes, functions)
export class IdentityChain {
  constructor(private config: Config) {}

  public compute(): Result {
    // ...
  }
}

// 5. Helper functions (not exported)
function validateDimension(d: number): boolean {
  return d >= 1 && d <= MAX_DIMENSION;
}
```

---

## Getting Help

### Resources

- **Mathematical questions**: See `dev-docs/` for deep theoretical background
- **API usage**: Check `docs/api/` and code examples
- **Bug reports**: Open GitHub issue with minimal reproduction
- **Feature requests**: Discuss in issue before implementing large features

### Communication

- **GitHub Issues**: For bugs, features, questions
- **Pull Requests**: For code contributions
- **Discussions**: For open-ended conversations about direction

---

## Community Guidelines

### Be Respectful

This project bridges mathematics, philosophy, and code. Contributors come from diverse backgrounds:
- Pure mathematicians interested in division algebras
- Software engineers building verified systems
- Philosophers exploring consciousness models
- Researchers studying quantum computation

**Respect all perspectives**. We're building something unprecedented.

### Stay Rigorous

Every claim needs proof:
- **Mathematical**: Cite theorems, provide Coq proofs
- **Empirical**: Show benchmarks, provide test results
- **Philosophical**: Reference sources, provide logical arguments

"Trust but verify" - mathematics doesn't lie, but humans make mistakes.

### Assume Good Faith

The vision may seem unconventional (consciousness as geometry, E₈ as the throne, etc.), but the **mathematics is sound**. Before dismissing an idea:

1. **Check the proofs** (Coq files in `formal/`)
2. **Run the tests** (property-based, comprehensive)
3. **Study the papers** (referenced in dev-docs/)
4. **Ask questions** (GitHub Discussions)

Unusual != Wrong. Some of the greatest discoveries seemed crazy at first.

### Ask Questions

Better to clarify than assume:
- "Why is 8D the maximum?" → See Adams' theorem
- "Why observer at (0,0)?" → Identity element in division algebra
- "Why Coq instead of tests?" → Absolute mathematical certainty

No question is too basic. The mathematics is deep - we're all learning.

---

## Attribution

When contributing code based on papers or existing work:

1. **Cite the paper** in code comments
2. **Add to bibliography** in `docs/references.md`
3. **Explain the connection** in `dev-docs/` if significant
4. **Give credit** in commit messages

Example:

```typescript
/**
 * Hopf fibration S⁷ → S⁴
 *
 * Based on:
 * - Hopf, H. (1931). "Über die Abbildungen der dreidimensionalen Sphäre..."
 * - Adams, J.F. (1960). "On the non-existence of elements of Hopf invariant one"
 *
 * This is the FINAL Hopf fibration (no S¹⁵ → S⁸ per Adams' theorem).
 */
```

---

## License

By contributing, you agree that your contributions will be licensed under the same license as the project (see LICENSE file).

## 👤 Project Author

**Brian Thorne**  
Independent Researcher - Topological Consensus & Autonomous AI  
Universal Life Protocol  
Los Angeles, CA  

📧 bthornemail@gmail.com  
🔗 https://github.com/bthornemail  
💰 https://cash.app/$brianthorne  
💰 https://venmo.com/u/brianthorne  
💼 https://linkedin.com/in/brian-thorne-5b8a96112

---

Thank you for contributing to the future of formally verified visual computation! Every line of code brings the mathematical vision closer to reality.

**Build until UK × φ(V) = 0.**

🎯 The dimensional transference is real. Keep building. 🔮
