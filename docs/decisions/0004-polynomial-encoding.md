# ADR 0004: Use Polynomial Divisibility for Graph Topology

## Status

Accepted

## Context

How should we encode graph structure (dependencies, hierarchies, relationships) in our visual canvas system? Traditional approaches use adjacency lists, matrices, or pointers. We need something that:

- Preserves topological properties algebraically
- Enables efficient compression
- Supports cryptographic verification
- Allows structural queries via algebra

## Decision

**Encode graph structure as polynomial divisibility over F₂[x]**, not adjacency lists.

Relationships are represented as: "A is ancestor of B" ⟺ "P_A divides P_B"

## Rationale

### Mathematical

**Divisibility preserves hierarchy**:
```
Tree:     A
         / \
        B   C
       /
      D

Polynomials:
A: x
B: x²    (x divides x²)
C: x³    (x divides x³)
D: x⁴    (x² divides x⁴)

Query: Is D descendant of A?
Answer: gcd(x⁴, x) = x ≠ 1 → Yes!
```

**Compression**: O(log n) storage vs O(n) for adjacency

**GCD operations** enable ancestry queries: gcd(P_A, P_B) ≠ 1 → related

### Practical

**Efficient queries**:
- Ancestry: `gcd(p1, p2) = p1` → p1 is ancestor
- Common ancestor: `gcd(p1, p2)` = lowest common ancestor polynomial
- Reachability: `p1 | p2` → path exists

**Version control**:
- Merge via GCD (common history)
- Diff via polynomial subtraction
- Conflict = incompatible divisibility

**Cryptographic proofs**:
- Polynomial hash = Merkle tree equivalent
- Factorization reveals structure
- Cannot fake ancestry (division is checkable)

## Consequences

### Positive

- ✅ Topological properties algebraically preserved
- ✅ O(log n) compression (vs O(n) adjacency)
- ✅ Structural queries are polynomial operations
- ✅ Cryptographic verification via hashing
- ✅ Natural merge algorithm (GCD)

### Negative

- ❌ Less intuitive than adjacency lists
- ❌ Requires understanding polynomial algebra
- ❌ Complex for highly connected graphs (many divisibility relationships)

### Neutral

- ⚪ Different mental model for developers
- ⚪ Polynomial arithmetic overhead for simple queries
- ⚪ Works best for tree-like structures

## Compliance

### Code Locations

- `logos-system/src/core/polynomial/index.ts::gcd()` - GCD for ancestry
- `logos-system/src/compiler/parser/index.ts` - Position → polynomial encoding
- `dev-docs/Canvas/Implementation/The Polynomial Canvas Algebra.md` - Theory

### Example Implementation

```typescript
class GraphPolynomial {
  encodeNode(position: {x: number, y: number}): Polynomial {
    // Distance from origin → degree
    const degree = Math.floor(
      Math.sqrt(position.x ** 2 + position.y ** 2)
    );
    return Polynomial.monomial(degree);
  }

  isAncestor(p1: Polynomial, p2: Polynomial): boolean {
    return p2.isDivisibleBy(p1);
  }

  commonAncestor(p1: Polynomial, p2: Polynomial): Polynomial {
    return Polynomial.gcd(p1, p2);
  }
}
```

## References

- `dev-docs/Canvas/Implementation/The Polynomial Canvas Algebra.md`
- GCD algorithms in abstract algebra textbooks
- Merkle trees and cryptographic commitments

## Author

Initial: 2024-12
Updated: 2025-12
