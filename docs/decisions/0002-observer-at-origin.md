# ADR 0002: Observer Node Must Be Positioned at Canvas Origin (0,0)

## Status

Accepted

## Context

In visual canvas programming, where should the "observer" node (the perspective from which the computation is viewed) be positioned? Is this just a UI convention, or does it have mathematical significance?

Canvas systems typically allow arbitrary node placement. However, our polynomial encoding uses position to determine coefficients and degrees. The question arises: where should the observer be positioned for mathematical consistency?

## Decision

**The observer node MUST be positioned at coordinates (0,0) in the canvas**. This is not a UI preference - it's a mathematical requirement for the observer to serve as the identity element in polynomial algebra.

## Rationale

### Mathematical Foundation

In division algebras, the **identity element** is the value that leaves other values unchanged when multiplied:

```
1 · a = a · 1 = a   (for all a)
```

For polynomial representation:
- **P₀ = 1** (the constant polynomial)
- **Observer = multiplicative identity**
- **Observation = multiplication by 1**

Position encoding in our system:
```
Polynomial degree ∝ distance from origin
Node at (x, y) → polynomial P(x,y) with coefficients encoded from position
Node at (0, 0) → P(0,0) = constant term = P₀ = 1
```

**Therefore**: Observer at (0,0) is the **only** position where observation = identity operation.

Mathematically:
```
observe(node) = P₀ · P_node = 1 · P_node = P_node
```

The observation doesn't change the observed (identity property).

### General Relativity Analog

In general relativity:
- **No absolute position** in space
- All coordinates are **observer-relative**
- Observer defines the coordinate system origin

Similarly in our canvas system:
- No "absolute" node positions
- All node positions **relative to observer**
- **Observer IS the coordinate system zero point**

This mirrors the principle that there's no privileged reference frame.

### Quantum Mechanics Connection

In quantum mechanics, observation is a projection operator:
```
⟨observer|ψ⟩ = observed state
```

If observer is at (0,0) with P₀ = 1:
```
P₀ · P(x,y) = P(x,y)  (identity operation)
```

Self-observation (observer observing itself):
```
P₀ · P₀ = P₀
1 · 1 = 1  (fixed point, no paradox)
```

### Self-Reflection: Brouwer Fixed Point Theorem

**Brouwer's Fixed Point Theorem**: Every continuous function from a compact convex space to itself has at least one fixed point.

For the observer:
```
observe(observer) = observer
f(P₀) = P₀
```

This **resolves the infinite regress** problem: "Who observes the observer?"

**Answer**: The observer IS the fixed point. Self-observation doesn't change the observer because it's the identity element.

## Consequences

### Positive

- ✅ Observation is well-defined algebraically (multiplication by 1)
- ✅ Self-reflection has no paradox (fixed point theorem)
- ✅ All positions are relative (like general relativity)
- ✅ Polynomial encoding is clean (origin = constant polynomial)
- ✅ Matches quantum mechanics (projection operator at origin)
- ✅ No special cases (identity element is standard algebra)

### Negative

- ❌ Parser must detect and validate observer position
- ❌ Diagrams without observer at (0,0) are malformed
- ❌ UI must constrain observer node placement (can't be arbitrary)
- ❌ Users must understand mathematical significance of (0,0)

### Neutral

- ⚪ "Convention" is actually a mathematical requirement (not arbitrary)
- ⚪ Error messages need to explain why (0,0) is mandatory
- ⚪ Adds constraint to otherwise free canvas layout
- ⚪ Makes system more mathematical, less "visual tool"

## Compliance

### Code Locations

**Parser validation**:
- `logos-system/src/compiler/parser/index.ts::findObserver()` - Detects observer at (0,0)
- `logos-system/src/compiler/parser/index.ts::validateObserver()` - Validates position
- `.obsidian/plugins/logos-visual-compiler/src/parsers/CanvasParser.ts::parse()` - Checks observer

**Implementation**:
```typescript
export function findObserver(canvas: CanvasJSON): CanvasNode | null {
  return canvas.nodes.find(node =>
    node.text?.startsWith('#Observer:') &&
    node.x === 0 &&
    node.y === 0
  ) || null;
}

export function validateObserver(canvas: CanvasJSON): ValidationResult {
  const observer = findObserver(canvas);

  if (!observer) {
    return {
      valid: false,
      error: {
        code: 'NO_OBSERVER',
        message: 'Observer node required at (0,0)',
        explanation:
          'The observer serves as the identity element (P₀ = 1) in polynomial algebra. ' +
          'It must be at the origin (0,0) to function as the multiplicative identity. ' +
          'This is a mathematical requirement, not a UI convention.'
      }
    };
  }

  if (observer.x !== 0 || observer.y !== 0) {
    return {
      valid: false,
      error: {
        code: 'OBSERVER_NOT_AT_ORIGIN',
        message: `Observer at (${observer.x}, ${observer.y}) must be at (0,0)`,
        explanation:
          'For the observer to serve as the identity element (P₀ = 1), ' +
          'it must be positioned at the coordinate system origin. ' +
          'All other node positions are computed relative to this point.'
      }
    };
  }

  return { valid: true };
}
```

### Validation Rules

1. **Exactly one observer node** per canvas (no more, no less)
2. **Observer at (0,0)** (with tolerance: ±1 pixel for UI imprecision)
3. **Observer is identity element** (P₀ = 1 in polynomial encoding)
4. **Observer text starts with `#Observer:`** (content marker)

### Error Handling

**Comprehensive error with explanation**:
```typescript
if (!observer || observer.x !== 0 || observer.y !== 0) {
  throw new CompilationError({
    code: 'INVALID_OBSERVER_POSITION',
    message: 'Observer node must be at (0,0)',
    details: {
      found: observer ? `(${observer.x}, ${observer.y})` : 'none',
      required: '(0,0)',
      rationale: [
        'The observer serves as the identity element (P₀ = 1)',
        'Identity element in polynomial algebra must be at origin',
        'All positions computed relative to observer',
        'Observation = multiplication by identity (1 · a = a)',
        'Self-reflection is fixed point (1 · 1 = 1)'
      ],
      mathematicalBasis: [
        'Division algebra: 1 is multiplicative identity',
        'Brouwer fixed point theorem: f(1) = 1',
        'General relativity: observer defines reference frame'
      ],
      howToFix: 'Add observer node at (0,0) with text "#Observer:"'
    }
  });
}
```

### Tests

**Test files**:
- `parser.test.ts::should find observer at origin` - Validates (0,0) detection
- `parser.test.ts::should reject observer at non-origin` - Ensures validation
- `parser.test.ts::should reject missing observer` - Requires observer existence
- `integration.test.ts::should compile canvas with observer at origin` - End-to-end

**Example tests**:
```typescript
describe('Observer Position Validation', () => {
  it('should accept observer at (0,0)', () => {
    const canvas = {
      nodes: [
        { id: 'obs', x: 0, y: 0, text: '#Observer:', type: 'text' }
      ],
      edges: []
    };

    const result = validateObserver(canvas);
    expect(result.valid).toBe(true);
  });

  it('should reject observer at non-origin', () => {
    const canvas = {
      nodes: [
        { id: 'obs', x: 50, y: 50, text: '#Observer:', type: 'text' }
      ],
      edges: []
    };

    const result = validateObserver(canvas);
    expect(result.valid).toBe(false);
    expect(result.error?.code).toBe('OBSERVER_NOT_AT_ORIGIN');
  });

  it('should verify observer is identity element', () => {
    const canvas = createValidCanvas();
    const parsed = parseCanvas(canvas);

    // Observer polynomial should be P₀ = 1
    expect(parsed.observer.polynomial.degree).toBe(0);
    expect(parsed.observer.polynomial.constant).toBe(1);

    // Observation should be identity operation
    const node = parsed.nodes[0];
    const observed = observe(parsed.observer, node);
    expect(observed.polynomial).toEqual(node.polynomial);  // 1 · a = a
  });
});
```

### Documentation

- **DESIGN_PRINCIPLES.md** - Principle #4: Observer Relativity
- **ARCHITECTURE.md** - Section: "Core Principles → Observer at Origin as Identity Element"
- **PHILOSOPHY.md** - Section: "Observer as Identity Element"
- **dev-docs/Canvas/Implementation/The Mathematical Foundation.md** - Original derivation

## Examples

### Valid Canvas

```json
{
  "nodes": [
    {
      "id": "obs",
      "x": 0,
      "y": 0,
      "text": "#Observer:\nThe point of consciousness.\nAll observation happens here.",
      "type": "text"
    },
    {
      "id": "n1",
      "x": 100,
      "y": 50,
      "text": "#Activate: main",
      "type": "text"
    }
  ],
  "edges": [
    { "id": "e1", "fromNode": "obs", "toNode": "n1" }
  ]
}
```

✅ **VALID**: Observer at (0,0), other nodes positioned relative to it.

### Invalid Canvas: Observer at Non-Origin

```json
{
  "nodes": [
    {
      "id": "obs",
      "x": 50,
      "y": 50,
      "text": "#Observer:",
      "type": "text"
    },
    {
      "id": "n1",
      "x": 100,
      "y": 50,
      "text": "#Activate: main",
      "type": "text"
    }
  ],
  "edges": []
}
```

❌ **INVALID**: Observer at (50,50) instead of (0,0).

**Error**: "Observer must be at (0,0) to serve as identity element"

### Invalid Canvas: Missing Observer

```json
{
  "nodes": [
    {
      "id": "n1",
      "x": 100,
      "y": 50,
      "text": "#Activate: main",
      "type": "text"
    }
  ],
  "edges": []
}
```

❌ **INVALID**: No observer node present.

**Error**: "Observer node required at (0,0)"

## Migration Path

For existing canvases with observer at non-origin positions:

### Step 1: Detect Current Observer Position

```typescript
const observer = canvas.nodes.find(n => n.text?.startsWith('#Observer:'));
const offset = { x: observer.x, y: observer.y };
```

### Step 2: Translate All Nodes

```typescript
const translatedNodes = canvas.nodes.map(node => ({
  ...node,
  x: node.x - offset.x,  // Move observer to (0,0)
  y: node.y - offset.y
}));
```

### Step 3: Verify Observer at Origin

```typescript
const newObserver = translatedNodes.find(n => n.text?.startsWith('#Observer:'));
console.assert(newObserver.x === 0 && newObserver.y === 0);
```

### Step 4: Update Canvas

```typescript
const migratedCanvas = { ...canvas, nodes: translatedNodes };
await saveCanvas(migratedCanvas);
```

### Automated Migration Script

```bash
# migrate-observer-to-origin.sh
for file in vault/**/*.canvas; do
  node scripts/migrate-observer.js "$file"
done
```

## UI Considerations

### Obsidian Plugin Implementation

**Constrain observer node placement**:
```typescript
// In canvas editor
function onNodeMove(node: CanvasNode, newX: number, newY: number) {
  if (isObserver(node)) {
    // Prevent moving observer from origin
    if (newX !== 0 || newY !== 0) {
      showNotice(
        'Observer node must remain at (0,0). ' +
        'This is a mathematical requirement for identity element.'
      );
      return; // Cancel move
    }
  }

  // Allow other nodes to move freely
  node.x = newX;
  node.y = newY;
}
```

**Visual indication**:
```typescript
// Render observer with special styling
function renderObserver(observer: CanvasNode) {
  return {
    ...observer,
    style: {
      border: '2px solid gold',
      backgroundColor: '#fff9e6',
      position: 'pinned',  // Cannot be dragged
      label: '🎯 Observer (0,0)'
    }
  };
}
```

## References

**Mathematical foundations**:
- Division Algebra Identity: `1 · a = a`
- Brouwer Fixed-Point Theorem (1911)
- General Relativity: Observer-relative coordinates
- Quantum Mechanics: Projection operator `⟨ψ|φ⟩`

**Papers**:
- Brouwer, L. E. J. (1911). "Beweis der Invarianz der Dimensionenzahl"
- Einstein, A. (1905). "On the Electrodynamics of Moving Bodies" (relativity of position)

**Related ADRs**:
- ADR 0001: 8D Maximum for Core Genomes (identity element in division algebras)
- ADR 0004: Polynomial Encoding for Graph Topology (position → coefficients)

## Author

Initial: 2024-12 (extracted from mathematical foundation docs)
Updated: 2025-12 (formalized as ADR)
