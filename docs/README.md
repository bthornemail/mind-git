# Documentation

Welcome to the Esp32-Metatron-Merkaba documentation! This directory contains comprehensive technical documentation organized by topic.

## 📚 Documentation Structure

```
docs/
├── README.md                    ← You are here
├── api/                         → API documentation
├── guides/                      → How-to guides and tutorials
├── architecture/                → Deep technical architecture docs
├── decisions/                   → Architecture Decision Records (ADRs)
├── research/                    → Academic/theoretical documentation
└── vision/                      → Philosophical and visionary content
```

---

## 🎯 Quick Start

**New to the project?**
1. Start with [Getting Started Guide](guides/getting-started.md) (coming soon)
2. Read [../ARCHITECTURE.md](../ARCHITECTURE.md) for system overview
3. Check [../DESIGN_PRINCIPLES.md](../DESIGN_PRINCIPLES.md) for coding standards

**Want to contribute?**
1. Read [../CONTRIBUTING.md](../CONTRIBUTING.md)
2. Review [decisions/](decisions/) for architectural decisions
3. Check [../PHILOSOPHY.md](../PHILOSOPHY.md) to understand the vision

**Looking for APIs?**
- [api/logos-system.md](api/logos-system.md) - Core library API (coming soon)
- [api/obsidian-plugin.md](api/obsidian-plugin.md) - Plugin API (coming soon)

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

Step-by-step tutorials and how-to guides for common tasks.

**Planned guides**:
- Getting Started (installation, first program)
- Visual Programming with Canvas
- Mathematical Foundations
- Integration & Deployment

### API Documentation

**Location**: [`api/`](api/)

Reference documentation for all public APIs.

**Planned API docs**:
- logos-system library
- Obsidian plugin
- Racket backend bridge

### Architecture Documentation

**Location**: [`architecture/`](architecture/)

Deep technical documentation on system design and implementation.

**Planned topics**:
- Compiler Pipeline
- Mathematical Core
- Polyglot Integration
- Module Boundaries

### Research Documentation

**Location**: [`research/`](research/)

Academic and theoretical documentation for researchers.

**Planned topics**:
- Identity Chain (1,400 years of mathematics)
- Consciousness Model
- Hopf Fibrations
- Formal Verification

### Vision & Philosophy

**Location**: [`vision/`](vision/)

Philosophical context and broader vision.

**Planned topics**:
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
- ✅ ADRs (6 major architectural decisions)
- ✅ docs/ structure

**In Progress**:
- 🚧 API documentation
- 🚧 User guides
- 🚧 Architecture deep-dives

**Planned**:
- 📋 Research documentation
- 📋 Vision documentation
- 📋 Tutorial videos (future)

---

## 🔍 Finding What You Need

**"How do I...?"** → Check [guides/](guides/)

**"Why did we choose...?"** → Check [decisions/](decisions/)

**"What does this API do?"** → Check [api/](api/)

**"How does X work internally?"** → Check [architecture/](architecture/) or [../ARCHITECTURE.md](../ARCHITECTURE.md)

**"What's the mathematical basis?"** → Check [research/](research/) or `dev-docs/`

**"What's the vision?"** → Check [../PHILOSOPHY.md](../PHILOSOPHY.md) or [vision/](vision/)

---

**Welcome to the documentation!** If you can't find what you're looking for, please [open an issue](https://github.com/youruser/Esp32-Metatron-Merkaba/issues) to help us improve.
