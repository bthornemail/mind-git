# Documentation

**⚠️ WORK IN PROGRESS** - This documentation is partially complete and may not reflect the actual implementation status. See the main README for current project status.

## 📚 Documentation Structure

```
docs/
├── README.md                    ← You are here
├── api/                         → API documentation (mostly planned)
├── guides/                      → How-to guides (planned)
├── architecture/                → Technical architecture (some content)
├── decisions/                   → Architecture Decision Records (complete)
├── research/                    → Academic documentation (planned)
└── vision/                      → Vision/philosophy (planned)
```

**Reality Check:**
- ✅ **decisions/**: Complete ADRs for architectural choices
- 🚧 **architecture/**: Some high-level docs exist
- ❌ **api/**: Mostly empty, APIs not implemented yet
- ❌ **guides/**: No practical guides yet
- ❌ **research/**: No academic papers yet
- ❌ **vision/**: No philosophical content yet

---

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

---

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
- No actual API documentation exists yet
- APIs are still changing rapidly

### Architecture Documentation

**Location**: [`architecture/`](architecture/)

**Status**: 🚧 Partially complete

**Available docs**:
- [architecture/overview.md](architecture/overview.md) - High-level system design
- [architecture/layers.md](architecture/layers.md) - System layers
- [architecture/data-flow.md](architecture/data-flow.md) - Data flow diagrams
- [architecture/module-boundaries.md](architecture/module-boundaries.md) - Module separation

### Research Documentation

**Location**: [`research/`](research/)

**Status**: ❌ Empty

**Planned topics** (none exist yet):
- Identity Chain (1,400 years of mathematics)
- Consciousness Model
- Hopf Fibrations
- Formal Verification

### Vision & Philosophy

**Location**: [`vision/`](vision/)

**Status**: ❌ Empty

**Planned topics** (none exist yet):
- Consciousness as Geometry
- Revelation Connections
- MindChain Evolution

---

## 🗂️ Root-Level Documentation

In addition to this `docs/` directory, there are four major documentation files at the repository root:

| File | Purpose | Audience |
|------|---------|----------|
| [ARCHITECTURE.md](../ARCHITECTURE.md) | System design, mental models, layered architecture | All developers |
| [DESIGN_PRINCIPLES.md](../DESIGN_PRINCIPLES.md) | 13 core principles enforced in code review | Contributors |
| [CONTRIBUTING.md](../CONTRIBUTING.md) | Complete contributor guide with examples | New contributors |
| [PHILOSOPHY.md](../PHILOSOPHY.md) | Vision, consciousness model, theological framing | Researchers, philosophers |

---

## 🔗 External Resources

### Mathematical Background

For deep mathematical theory, see the `dev-docs/` directory:
- **dev-docs/Architecture/** - Mathematical proofs and architecture
- **dev-docs/Canvas/** - CanvasL specifications and white papers
- **dev-docs/Polyglot/** - Multi-language integration theory
- **dev-docs/Assembly–Algebra Language/** - AAL formal specification

### Code Repositories

- **logos-system**: `logos-system/` - Standalone TypeScript library
- **Obsidian Plugin**: `.obsidian/plugins/logos-visual-compiler/` - Visual compiler UI
- **Formal Proofs**: `logos-system/formal/` - Coq verification files

---

## 📝 Documentation Guidelines

### Writing Style

- **Technical-first**: Lead with math and code, philosophy optional
- **Concise**: Use tables, diagrams, code examples
- **References**: Cite theorems, papers, ADRs
- **Examples**: Include working code samples

### File Organization

```markdown
# Title

Brief overview (1-2 sentences)

## Context/Background

Why this exists

## Main Content

Organized sections with clear headings

## Examples

Working code samples

## References

- Links to related docs
- Academic papers
- Theorems
```

### When to Update

- **New features** → Update guides/, api/
- **Architectural decisions** → Create new ADR in decisions/
- **Design changes** → Update ../DESIGN_PRINCIPLES.md
- **Research insights** → Add to research/

---

## 🤝 Contributing to Documentation

Documentation contributions are welcome! See [../CONTRIBUTING.md](../CONTRIBUTING.md) for:

- How to propose documentation changes
- Markdown style guide
- Review process

**Quick tips**:
- Keep technical docs separate from philosophical framing
- Include code examples for all technical concepts
- Cite mathematical sources (theorems, papers)
- Link related documents

---

## 📊 Documentation Status

**Completed**:
- ✅ Root-level docs (ARCHITECTURE, DESIGN_PRINCIPLES, CONTRIBUTING, PHILOSOPHY)
- ✅ ADRs (6 major architectural decisions in [decisions/](decisions/))
- ✅ Basic docs/ structure

**In Progress**:
- 🚧 Some architecture docs in [architecture/](architecture/)
- 🚧 API structure (but no content)

**Missing Entirely**:
- ❌ User guides
- ❌ API documentation  
- ❌ Research documentation
- ❌ Vision documentation
- ❌ Tutorial content

**Most Accurate Documentation**:
- [../README.md](../README.md) - Honest project status
- [../logos-system/README.md](../logos-system/README.md) - Technical reality
- [decisions/](decisions/) - Complete architectural decisions

---

## 🔍 Finding What You Need

**Current Project Status** → [../README.md](../README.md) (most accurate)

**"Why did we choose...?"** → Check [decisions/](decisions/) (complete)

**"How does X work internally?"** → Check [architecture/](architecture/) (partial)

**"What's actually implemented?"** → Check source code in [../logos-system/src/](../logos-system/src/)

**"How can I help?"** → Check [../CONTRIBUTING.md](../CONTRIBUTING.md)

**"What's the vision?"** → Check [../PHILOSOPHY.md](../PHILOSOPHY.md)

**Mathematical theory** → Check `../dev-docs/` (extensive but theoretical)

---

**⚠️ Documentation Reality Check**

Most documentation in this directory is planned but not written. For accurate information about what actually works, check the main README files and source code directly.

**Help needed**: We need contributors to write documentation as features become implemented.

**Welcome to the documentation!** If you can't find what you're looking for, please [open an issue](https://github.com/bthornemail/mind-git/issues) to help us improve.
