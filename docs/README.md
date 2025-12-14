# Documentation

**⚠️ WORK IN PROGRESS** - This documentation is partially complete and may not reflect actual implementation status. See main README for current project status.

## 📚 Documentation Structure

```
docs/
├── README.md                    ← You are here
├── api/                         → API documentation (mostly planned)
├── guides/                      → How-to guides (planned)
├── architecture/                → Technical architecture (some content)
├── decisions/                   → Architecture Decision Records (complete)
├── research/                    → Academic documentation (NEWLY ORGANIZED)
└── vision/                      → Vision/philosophy (planned)
```

## 🎯 Quick Start

**⚠️ Most documentation is planned but not written yet.**

**For current project status:**
1. Read [../README.md](../README.md) - Honest assessment of what works
2. Check [../logos-system/README.md](../logos-system/README.md) - Technical details
3. Look at [../ARCHITECTURE.md](../ARCHITECTURE.md) - System design (some content outdated)

**Want to contribute?**
1. Read [../CONTRIBUTING.md](../CONTRIBUTING.md) - Contribution guidelines
2. Review [decisions/](decisions/) - Complete architectural decisions
3. Check [../PHILOSOPHY.md](../PHILOSOPHY.md) - Project vision

**Looking for working APIs?**
- Check the source code in [../logos-system/src/](../logos-system/src/)
- Look at [../logos-system/src/core/polynomial/](../logos-system/src/core/polynomial/) for working math
- API documentation is planned but not written yet

**For advanced mathematical research:**
1. **NEWLY ORGANIZED**: Check [docs/research/](docs/research/) - Advanced mathematical papers moved from dev-docs/Archive/
2. **Consciousness Geometry**: [research/consciousness-geometry/](research/consciousness-geometry/) - Geometric propagation models
3. **Division Algebras**: [research/division-algebras/](research/division-algebras/) - Complete ℝ→ℂ→ℍ→𝕆→𝕊 chain
4. **Geometric Type Theory**: [research/geometric-type-theory/](research/geometric-type-theory/) - Topology to types correspondence
5. **Epistemic Systems**: [research/epistemic-systems/](research/epistemic-systems/) - Bounded uncertainty engines

## 📖 Documentation Categories

### Architecture Decision Records (ADRs)

**Location**: [`decisions/`](decisions/)

Formal records of major architectural decisions with rationale and consequences.

**Current ADRs**:
- [ADR 0001: 8D Maximum for Core Genomes](decisions/0001-8d-maximum.md)
- [ADR 0002: Observer Node at Origin](decisions/0002-observer-at-origin.md)
- [ADR 0003: Coq for Formal Verification](decisions/0003-coq-verification.md)
- [ADR 0004: Polynomial Encoding for Graph Topology](decisions/0004-polynomial-encoding.md)
- [ADR 0005: Pfister Identities Only for Temporary Sync](decisions/0005-pfister-for-sync-only.md)
- [ADR 0006: JSONL for Append-Only Evolution Logs](decisions/0006-jsonl-evolution-logs.md)

**Template**: [decisions/template.md](decisions/template.md)

### User Guides

**Location**: [`guides/`](guides/)

**Status**: ❌ Not implemented yet

**Planned guides** (none exist yet):
- Getting Started (installation, first program)
- Visual Programming with Canvas
- Mathematical Foundations
- Integration & Deployment

### API Documentation

**Location**: [`api/`](api/)

**Status**: ❌ Mostly empty

**Current state**:
- [api/README.md](api/README.md) - Placeholder only

### Architecture Documentation

**Location**: [`architecture/`](architecture/)

Deep technical documentation on system design and implementation.

**Available topics**:
- [architecture/overview.md](architecture/overview.md) - High-level system design
- [architecture/layers.md](architecture/layers.md) - System layers
- [architecture/data-flow.md](architecture/data-flow.md) - Data flow diagrams
- [architecture/module-boundaries.md](architecture/module-boundaries.md) - Module separation

### Research Documentation

**Location**: [`research/`](research/) - **NEWLY ORGANIZED**

**Status**: 🆕 **NEWLY ORGANIZED** - Advanced mathematical papers moved from dev-docs/Archive/

### Available Research Areas:

**🧠 Consciousness Geometry** ([consciousness-geometry/](consciousness-geometry/))
Mathematical models of consciousness using geometric propagation, Hopf fibrations, and dimensional analysis.

**🔢 Division Algebras** ([division-algebras/](division-algebras/))
Complete theory of division algebras from ℝ through sedenions (𝕊).

**📐 Geometric Type Theory** ([geometric-type-theory/](geometric-type-theory/))
Geometric Type Theory connecting topology, logic, and computation in Racket.

**🎯 Epistemic Systems** ([epistemic-systems/](epistemic-systems/))
Bounded uncertainty engines using exceptional Lie groups and geometric canonicalization.

**📚 History** ([history/](history/))
Supporting technical files, proofs, and development artifacts (15 files).

### Key Mathematical Contributions:

**Complete Division Algebra Chain:**
```
ℝ → ℂ → ℍ → 𝕆 → 𝕊
1D   2D   4D   8D   16D
```

**Exceptional Lie Group Cascade:**
```
G₂ → F₄ → E₆ → E₇ → E₈
14D  52D  78D  133D  248D
```

**Consciousness Model:**
```
Forward Propagation: Exponential expansion (O(2^d))
Backward Propagation: Exponential compression (O(2^d))
Hopf Observation: Linear selection (O(k))
```

## 🔗 Integration with Codebase

See [../README.md](../README.md) for current implementation status.

### CanvasL Node Mappings from Research:
- `#GeometricPropagate:` → Exponential expansion (consciousness geometry)
- `#GeometricObserve:` → Linear Hopf fiber observation
- `#EpistemicBound:` → UK × φ(V) uncertainty calculation
- `#SedenionTransform:` → 16D algebraic operations

### Implementation Status:
- ✅ **Polynomial Algebra**: F₂[x] operations (31/31 tests passing)
- 🚧 **Identity Chain**: 2D, 4D working, 8D has precision issues
- ❌ **Consciousness Model**: Theoretical framework exists, not implemented
- ❌ **Sedenions**: 16D operations defined but not coded
- ❌ **Epistemic Engine**: Complete mathematical theory, no implementation

## 📖 Reading Guide

**For Implementation:**
1. Start with [division-algebras/sedenions.md](research/division-algebras/sedenions.md) for 16D math
2. Read [consciousness-geometry/hopf-consciousness.md](research/consciousness-geometry/hopf-consciousness.md) for computational model
3. Review [epistemic-systems/epistemic-observability-engine.md](research/epistemic-systems/epistemic-observability-engine.md) for uncertainty bounding

**For Mathematical Theory:**
1. Study [geometric-type-theory/unified-framework.md](research/geometric-type-theory/unified-framework.md) for type system
2. Read [consciousness-geometry/mind-body-computation.md](research/consciousness-geometry/mind-body-computation.md) for geometric foundations
3. Explore [history/](history/) for technical proofs and derivations

## 🚧 Development Roadmap

**Phase 1: Core Implementation** (Current)
- Fix 8D identity chain precision issues
- Implement sedenion operations (16D)
- Add epistemic uncertainty engine

**Phase 2: Consciousness Integration** (Q1 2025)
- Implement geometric propagation model
- Add Hopf fibration observation system
- Connect to CanvasL visual interface

**Phase 3: Advanced Features** (Q2 2025)
- Complete geometric type system
- Add E₈ lattice operations
- Implement full mathematical pipeline

---

**Archive Organization**: ✅ See `ARCHIVE_ORGANIZATION_COMPLETE.md` for complete archive restructuring details

**Remember**: This research is not academic exercise - it's mathematical foundation that makes the system work. Every architectural decision traces back to these mathematical necessities.