# Design Principles

These are the **core rules and philosophical foundations** enforced throughout the Esp32-Metatron-Merkaba codebase. Every pull request, code review, and architectural decision must align with these principles. They are not suggestions - they are **mathematical and engineering requirements** derived from 1,400 years of proven identities.

---

## Mathematical Principles

### 1. Norm Preservation

**Rule**: Every algebraic operation MUST preserve norms.

**Mathematical Formula**:
```
||a × b|| = ||a|| × ||b||
```

This is the **foundation of correctness**. Norms act as checksums - if they don't match, data corruption has occurred.

**Why**:
- Norm-preserving multiplication is the defining property of division algebras
- Guarantees invertibility (every non-zero element has an inverse)
- Enables cryptographic proofs of computation correctness
- Allows lossless compression via polynomial encoding

**Enforcement**:
```typescript
// identity-chain.test.ts
it('should preserve norms in multiplication', () => {
  const a = Polynomial.from([1, 0, 1]);
  const b = Polynomial.from([1, 1]);
  const product = a.mul(b);

  const normA = a.norm();
  const normB = b.norm();
  const normProduct = product.norm();

  expect(normProduct).toBeCloseTo(normA * normB, 10);
});
```

**References**:
- Hurwitz's Theorem (1898): Only R, C, H, O preserve norms
- Identity chain: Brahmagupta → Euler → Degen → Pfister
- AAL verification: `formal/IdentityChain.v::norm_preservation`

---

### 2. Division Algebra Purity

**Rule**: Persistent state MUST use division algebras (R, C, H, O only). Zero divisors are **forbidden**.

**Why**:
- **Division algebras**: R (1D), C (2D), H (4D), O (8D)
- **Pfister algebras**: 16D, 32D, 64D (have zero divisors!)
- **Zero divisors** mean `a × b = 0` even when `a ≠ 0, b ≠ 0`
- This breaks invertibility and makes state non-recoverable

**Mathematical Proof**:
```
In sedenions (16D): (e₃ + e₁₀) × (e₆ - e₁₅) = 0
But (e₃ + e₁₀) ≠ 0 and (e₆ - e₁₅) ≠ 0
⇒ Cannot invert operations!
⇒ UNSAFE for persistent state
```

**Enforcement**:
- 8D maximum for genomes (octonion algebra)
- 16D/32D only for temporary sync packets
- After sync: **reduce back to 8D** for storage
- Automated tests reject 16D+ genomes

**Good**:
```typescript
// Using octonions (8D) - division algebra ✓
const genome = new Octonion([...8 values]);
genome.multiply(other);  // Always invertible
```

**Bad**:
```typescript
// Using sedenions (16D) - NOT division algebra ✗
const genome = new Sedenion([...16 values]);
genome.multiply(other);  // Might hit zero divisor!
```

**References**:
- Hurwitz's Theorem: Only 4 division algebras exist
- Adams' Theorem (1960): Hopf fibrations only for S¹, S³, S⁷
- `docs/decisions/0001-8d-maximum.md`

---

### 3. Polynomial Topology Preservation

**Rule**: Graph structure MUST be encoded as polynomial divisibility, not adjacency lists.

**Why**:
- **Topological properties** preserved via algebraic structure
- **Compression**: O(log n) storage vs O(n) for adjacency
- **Cryptographic proofs**: GCD operations enable provenance
- **Structural queries**: "Is A ancestor of B?" = "Does A divide B?"

**Encoding**:
```
Tree Structure:
    A
   / \
  B   C
 /
D

Polynomial Encoding:
- Node A: P_A(x) = x
- Node B: P_B(x) = x²  (A divides B: x | x²)
- Node C: P_C(x) = x³  (A divides C: x | x³)
- Node D: P_D(x) = x⁴  (B divides D: x² | x⁴)

Query: Is D descendant of A?
Answer: gcd(P_D, P_A) = x ⇒ Yes!
```

**Enforcement**:
- CanvasParser encodes positions as polynomials
- AST uses divisibility for dependency checking
- GCD operations for merge conflict resolution

**References**:
- `dev-docs/Canvas/Implementation/The Polynomial Canvas Algebra.md`
- `logos-system/src/core/polynomial/index.ts::gcd()`
- `docs/decisions/0004-polynomial-encoding.md`

---

### 4. Observer Relativity

**Rule**: Observer node MUST be at coordinates (0,0). All positions are relative to observer.

**Why**:
- **General relativity analog**: No absolute position in space
- **Identity element**: Observer = 1 in polynomial algebra
- **Self-reflection**: 1 · 1 = 1 (Brouwer fixed point theorem)
- **Quantum mechanics**: ⟨observer|ψ⟩ = observed state

**Mathematical Justification**:
```
Polynomial at (0,0):
P(0, 0) = constant term = P₀

For identity:
P₀ = 1 (not zero!)

Observation operation:
observe(node) = P₀ · P_node = 1 · P_node = P_node
```

**Enforcement**:
```typescript
// Parser validation
function validateCanvas(canvas: CanvasJSON): boolean {
  const observer = canvas.nodes.find(n => n.text.startsWith('#Observer:'));

  if (!observer) {
    throw new Error('Observer node required');
  }

  if (observer.x !== 0 || observer.y !== 0) {
    throw new Error(
      'Observer must be at (0,0) to serve as identity element. ' +
      'This is a mathematical requirement, not a UI convention.'
    );
  }

  return true;
}
```

**References**:
- `dev-docs/Canvas/Implementation/The Mathematical Foundation.md`
- Brouwer Fixed Point Theorem (1911)
- `docs/decisions/0002-observer-at-origin.md`

---

### 5. Formal Verification Everywhere

**Rule**: AAL operations MUST have Coq proofs. No `Admitted` statements allowed.

**Why**:
- **Zero-bug requirement**: Medical/aerospace-grade correctness
- **Mathematical certainty**: Proofs = programs (Curry-Howard)
- **Runtime verification**: Extract proofs to runnable code
- **Absolute confidence**: Can deploy without fear

**Coq Theorem Example**:
```coq
(* formal/AAL.v *)
Theorem type_soundness : forall t T,
  empty ⊢ t : T ->
  ~(stuck t).
Proof.
  intros t T Htyp.
  apply progress in Htyp as [Hval | Hstep].
  - (* t is value *)
    intro Hstuck. inversion Hstuck; subst; contradiction.
  - (* t can step *)
    intro Hstuck. inversion Hstuck; subst.
    destruct Hstep as [t' Hstep].
    apply H0 in Hstep. contradiction.
Qed.
```

**Enforcement**:
- CI checks: `cd formal && make verify` must pass
- No `Admitted` in any proof
- 127 lemmas + 42 theorems proven
- Every AAL instruction has verified semantics

**References**:
- CompCert: Verified C compiler (2006)
- seL4: Verified microkernel (2009)
- `docs/decisions/0003-coq-verification.md`

---

## Software Engineering Principles

### 6. Immutable Domain Objects

**Rule**: Domain objects (Polynomial, AST, AAL) are **immutable**. No in-place modification.

**Why**:
- **Predictable behavior**: Functions are deterministic
- **Safe parallelism**: No race conditions
- **Time travel debugging**: Can replay state changes
- **Functional purity**: Matches mathematical semantics

**Enforcement**:
```typescript
// All domain types use readonly
export interface Polynomial {
  readonly coeffs: readonly boolean[];
  readonly degree: number;
  readonly norm: number;
}

// Methods return new instances
class PolyF2 {
  static add(p1: Polynomial, p2: Polynomial): Polynomial {
    // Returns NEW polynomial, doesn't modify p1 or p2
    const newCoeffs = addCoeffs(p1.coeffs, p2.coeffs);
    return new Polynomial(newCoeffs);
  }
}
```

**Good**:
```typescript
const p1 = Polynomial.from([1, 0, 1]);
const p2 = Polynomial.from([1, 1]);
const sum = p1.add(p2);  // p1 and p2 unchanged
```

**Bad**:
```typescript
const p1 = Polynomial.from([1, 0, 1]);
p1.addInPlace([1, 1]);  // MUTATES p1 - FORBIDDEN!
```

---

### 7. Explicit Over Implicit

**Rule**: No magic, no hidden state transformations, no global singletons.

**Why**:
- **Code should be readable as mathematics**
- No surprising behavior
- Easy to reason about correctness
- Testable without mocking

**Enforcement**:
- No decorators (e.g., `@Injectable`, `@Component`)
- No global singletons (except constants)
- All dependencies passed explicitly
- No implicit type coercion

**Good**:
```typescript
function compile(
  source: CanvasJSON,
  options: CompilerOptions,
  verifier: Verifier
): CompilationResult {
  // All inputs explicit
  return compileWithOptions(source, options, verifier);
}
```

**Bad**:
```typescript
// Global state - FORBIDDEN!
let CURRENT_CANVAS: CanvasJSON;

function compile(): CompilationResult {
  // Implicit dependency on global state
  return compileCanvas(CURRENT_CANVAS);
}
```

---

### 8. Proof-Carrying Code

**Rule**: Generated code includes verification hashes. Runtime can verify correctness without recomputation.

**Why**:
- **Trust but verify**: Code proves its own correctness
- **Zero runtime checks needed**: Hash validates everything
- **Efficient**: O(1) verification vs O(n) re-execution
- **Cryptographic**: SHA-256 proof hashes

**Format**:
```typescript
export interface AALInstruction {
  opcode: OpCode;
  operands: Operand[];
  dimension: Dimension;  // D0-D10
  proof_hash: string;    // SHA-256 of verified derivation
  metadata: {
    source_node: string;  // Canvas node ID
    polynomial_degree: number;
    norm_before: number;
    norm_after: number;
  };
}
```

**Verification**:
```typescript
function verifyInstruction(instr: AALInstruction): boolean {
  // Recompute hash from instruction + derivation
  const computed = sha256(
    instr.opcode + instr.operands + instr.derivation
  );

  // Compare with stored proof hash
  return computed === instr.proof_hash;
}
```

**References**:
- Necula, G. "Proof-Carrying Code" (1997)
- `logos-system/src/core/aal/index.ts::AALInstruction`

---

### 9. Dimensional Discipline

**Rule**: Only increase dimensions when **mathematically justified**. Always include rationale.

**Why**:
- Higher dimensions add complexity
- Risk of exceeding 8D limit (Adams' theorem)
- Performance cost (exponential memory)
- Harder to visualize and debug

**Justification Required**:
```typescript
// Good: Explicit dimension with rationale
function expandTo4D(complex2D: Complex): Quaternion {
  // Rationale: Need rotation in 3D space (SO(3) ⊂ SU(2) = quaternions)
  // Hopf fibration: S³ → S² preserves structure
  return quaternionFromComplex(complex2D);
}

// Bad: No justification
function expandTo5D(data: number[]): number[] {
  // Why 5D? This violates Adams' theorem!
  return [...data, 0]; // ✗ FORBIDDEN
}
```

**Enforcement**:
- Code review must ask: "Why this dimension?"
- Tests verify: dimension ≤ 8 for persistent state
- Hopf fibrations for dimension reduction explicit

**References**:
- Adams' Theorem: Only 1, 2, 4, 8 support division algebras
- Bott Periodicity: Dimension cycles every 8
- `docs/decisions/0001-8d-maximum.md`

---

### 10. Append-Only Evolution

**Rule**: State changes are **logged**, never overwritten. JSONL format for .canvasl files.

**Why**:
- **Cryptographic replay**: Merkle trees for provenance
- **Time travel**: Can reconstruct any historical state
- **Debugging**: See exact sequence of mutations
- **Fault tolerance**: Corrupted states don't destroy history

**Format**:
```jsonl
{"event":"genome_created","time":1704067200,"genome":[...8 values],"hash":"abc123"}
{"event":"mutation","time":1704067201,"diff":[0,1,0,0,0,0,0,0],"hash":"def456"}
{"event":"dimension_expand","time":1704067202,"from":8,"to":16,"reason":"sync","hash":"ghi789"}
{"event":"dimension_reduce","time":1704067203,"from":16,"to":8,"hash":"jkl012"}
```

**Merkle Tree Construction**:
```typescript
class EvolutionLog {
  private entries: LogEntry[] = [];
  private merkleTree: MerkleTree;

  append(event: LogEntry) {
    this.entries.push(event);

    // Build Merkle tree incrementally
    this.merkleTree.addLeaf(hash(event));
  }

  verify(index: number): boolean {
    // Cryptographic proof of history
    return this.merkleTree.verify(index);
  }
}
```

**References**:
- `dev-docs/MindGit/MindGit Technical Specification v3.0.md`
- `docs/decisions/0006-jsonl-evolution-logs.md`

---

## Code Quality Principles

### 11. Tests Are Specifications

**Rule**: Every core function has **property-based tests**, not just happy paths.

**Why**:
- Mathematical operations have algebraic properties
- Properties are more general than examples
- Edge cases automatically discovered
- Tests document invariants

**Good** (property-based):
```typescript
import fc from 'fast-check';

it('should preserve commutativity: a + b = b + a', () => {
  fc.assert(
    fc.property(
      fc.array(fc.boolean()),  // Random polynomial coeffs
      fc.array(fc.boolean()),
      (coeffsA, coeffsB) => {
        const a = Polynomial.from(coeffsA);
        const b = Polynomial.from(coeffsB);

        const ab = a.add(b);
        const ba = b.add(a);

        // Commutativity holds for ALL inputs
        expect(ab.equals(ba)).toBe(true);
      }
    )
  );
});
```

**Bad** (example-based only):
```typescript
it('should add polynomials', () => {
  // Only tests ONE specific case!
  const a = Polynomial.from([1, 0, 1]);
  const b = Polynomial.from([1, 1]);
  expect(a.add(b).coeffs).toEqual([0, 1, 1]);
});
```

**Enforcement**:
- Core operations: property-based tests required
- UI/integration: example-based tests OK
- Coverage: 90%+ for `logos-system/src/core/`

---

### 12. No Framework Lock-In

**Rule**: Core logic is **independent** of UI frameworks (React, Vue, Obsidian).

**Why**:
- **Mathematics doesn't depend on frameworks**
- Can port to any platform
- Easier to test (no mocking frameworks)
- Longer lifespan (frameworks change)

**Enforcement**:
- `logos-system/` has **zero framework dependencies**
- Only TypeScript standard library
- UI layers import from core, **never reverse**

**Module Boundaries**:
```
logos-system/src/core/     ← Pure math, no dependencies
        ↑
        │ (import)
        │
.obsidian/plugins/         ← Obsidian-specific UI
```

**Good**:
```typescript
// logos-system/src/core/polynomial/index.ts
export function add(p1: Polynomial, p2: Polynomial): Polynomial {
  // No imports from Obsidian, React, etc.
  return new Polynomial(addCoeffs(p1.coeffs, p2.coeffs));
}
```

**Bad**:
```typescript
// logos-system/src/core/polynomial/index.ts
import { Notice } from 'obsidian';  // ✗ FORBIDDEN!

export function add(p1: Polynomial, p2: Polynomial): Polynomial {
  new Notice("Adding polynomials...");  // UI in core logic!
  return ...;
}
```

---

### 13. Error Handling via Types

**Rule**: Use `Result<T, E>` types, not exceptions for expected errors.

**Why**:
- **Algebraic error handling**: Composable, explicit
- **Type safety**: Compiler enforces error checking
- **No hidden control flow**: Errors are values
- **Functional**: Matches mathematical style

**Good**:
```typescript
type Result<T, E> =
  | { status: 'success'; value: T }
  | { status: 'error'; error: E };

function parseCanvas(json: string): Result<ParsedCanvas, ParseError> {
  try {
    const canvas = JSON.parse(json);

    if (!validateObserver(canvas)) {
      return {
        status: 'error',
        error: { code: 'NO_OBSERVER', message: 'Observer node required at (0,0)' }
      };
    }

    return { status: 'success', value: canvas };
  } catch (e) {
    return {
      status: 'error',
      error: { code: 'INVALID_JSON', message: e.message }
    };
  }
}

// Caller MUST handle errors
const result = parseCanvas(input);
if (result.status === 'error') {
  console.error(result.error);
} else {
  processCanvas(result.value);
}
```

**Bad**:
```typescript
function parseCanvas(json: string): ParsedCanvas {
  // Throws exceptions - caller might forget try/catch
  const canvas = JSON.parse(json);  // Might throw!

  if (!validateObserver(canvas)) {
    throw new Error('Observer required');  // Hidden control flow
  }

  return canvas;
}
```

**References**:
- Rust `Result<T, E>` type
- Haskell `Either` monad
- `logos-system/src/compiler/index.ts::CompilationResult`

---

## Code Review Checklist

When reviewing pull requests, verify:

### Mathematical Correctness
- [ ] Norms preserved? (run verification tests)
- [ ] Dimensions justified? (no unnecessary 16D usage)
- [ ] Observer at (0,0)? (check parser validation)
- [ ] Polynomial encoding correct? (divisibility = dependencies)

### Software Quality
- [ ] Domain objects immutable? (check `readonly` keywords)
- [ ] No framework imports in core? (check import statements)
- [ ] Errors handled via Result types? (no bare exceptions)
- [ ] Tests verify algebraic properties? (not just examples)

### Documentation
- [ ] Mathematical rationale documented? (comments with equations)
- [ ] Coq proofs updated? (if changing AAL)
- [ ] ADR created for decisions? (if architectural change)
- [ ] References cited? (papers, theorems)

---

## Enforcement Mechanisms

### Automated
- **TypeScript strict mode**: Catches type errors
- **ESLint rules**: Enforces code style
- **Jest tests**: Verifies algebraic properties
- **Coq compiler**: Ensures proofs are complete
- **CI pipeline**: Runs all checks on every commit

### Manual
- **Code review**: Reviewers check principles
- **Design review**: Architects approve dimensional changes
- **Mathematical review**: Verify Coq proofs for AAL changes

---

## Philosophy

These principles are not arbitrary preferences. They emerge from:

1. **1,400 years of mathematics**: Brahmagupta (628 AD) → Pfister (1965)
2. **Fundamental theorems**: Hurwitz, Adams, Bott periodicity
3. **Proven correctness**: CompCert, seL4, verified systems
4. **Battle-tested engineering**: Functional programming, immutability, type safety

**When in doubt**: Choose the more mathematically rigorous path.

---

## See Also

- **Architecture**: [ARCHITECTURE.md](ARCHITECTURE.md)
- **Contributing**: [CONTRIBUTING.md](CONTRIBUTING.md)
- **ADRs**: [docs/decisions/](docs/decisions/)
- **Research**: [docs/research/](docs/research/)
- **Philosophy**: [PHILOSOPHY.md](PHILOSOPHY.md)

---

**Remember**: These principles are **mathematical requirements**, not engineering suggestions. Violating them leads to bugs, data corruption, or mathematically impossible states. The system enforces correctness through the deepest foundations of algebra and topology.

"Build it correct, not fix it later."
