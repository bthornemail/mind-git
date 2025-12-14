# MIND-GIT Metadata Framework

A comprehensive metadata framework for the MIND-GIT system that provides unified organization, export capabilities, and relationship mapping for all components.

## 🎯 Features

- **Unified Metadata Schema**: Standardized front matter with mathematical and CanvasL context
- **Hidden Metadata System**: `.metadata/` folders with fingerprinting and relationship mapping
- **AGENTS.md Templates**: Auto-generated development directives for each component
- **Export System**: Org-mode style tags for selective documentation export
- **CanvasL Integration**: Deep integration with CanvasL visual programming language
- **Mathematical Context**: Tracking of mathematical foundations and formal verification

## 📁 Directory Structure

```
metadata/
├── core/                    # Core metadata service
│   ├── MetadataService.ts   # Main metadata processing
│   └── ExportSystem.ts      # Export functionality
├── scripts/                 # CLI and integration scripts
│   ├── cli.ts              # Command-line interface
│   ├── integrate-metadata.js # Integration script
│   └── export-system.js    # Export system
├── templates/               # AGENTS.md templates
│   ├── AGENTS.md.template  # Full template
│   └── AGENTS-simple.md.template # Simple template
├── schemas/                 # Metadata validation schemas
├── exports/                 # Generated exports
└── .hidden/                 # Runtime-only metadata
    ├── cache/              # Cached metadata
    └── registry/           # File metadata registry
```

## 🚀 Quick Start

### 1. Initialize Metadata

```bash
# Install dependencies
cd metadata && npm install

# Run integration script
npm run integrate

# Update all metadata
npm run update
```

### 2. Generate AGENTS.md

```bash
# Generate for specific directory
npm run generate-agents -- logos-system/src/compiler

# Generate with specific template
npm run generate-agents -- . --template mathematical
```

### 3. Export Documentation

```bash
# Export all documentation
npm run export:docs

# Export API reference
npm run export:api

# Export for npm package
npm run export:npm

# Export research papers
npm run export:research
```

### 4. Validate Metadata

```bash
# Validate all metadata
npm run validate

# Validate specific file
npm run validate -- --file logos-system/src/core/polynomial/index.ts
```

## 📊 Metadata Schema

### Core Fields

```yaml
---
# Core Identification
id: "mind-git:component:name"
title: "Component Title"
type: ["implementation", "compiler", "typescript"]
category: "core-compiler"

# Mathematical Context
dimensional: ["D4", "D5"]
mathematicalFoundation: ["polynomial-algebra", "identity-chain"]
hopfCompatible: true
normPreserving: true

# CanvasL Integration
canvasNodes: ["#Transform:", "#Verify:", "#Store:"]
nodeTypes: ["D4", "D5", "D6"]
compilationOrder: 3
spatialCoordinates: {x: -240, y: 180}

# Development Metadata
layer: 3
difficulty: 4
status: "complete"
completeness: 95
tested: true
verified: true

# Export Tags
tags: ["compiler", "ast", "canvasl", "typescript", "verified"]
keywords: ["abstract", "syntax", "tree", "generation", "spatial"]
exportTargets: ["npm", "docs", "api"]
noRef: false
---
```

### CanvasL Integration

The metadata system deeply integrates with CanvasL visual programming:

- **Node Types**: Automatic extraction of CanvasL patterns
- **AAL Mapping**: Conversion to Assembly-Algebra Language mnemonics
- **Spatial Coordinates**: Tracking of canvas node positions
- **Dimensional Mapping**: Mapping to AAL dimensions (D0-D10)

### Mathematical Context

Mathematical foundations are tracked and verified:

- **Foundation Types**: Polynomial algebra, identity chain, Hopf fibrations
- **Formal Verification**: Links to Coq proofs and verification status
- **Dimensional Constraints**: Adams' theorem compliance (1,2,4,8 dimensions)
- **Norm Preservation**: Mathematical correctness verification

## 🏷️ Export Tags

Use org-mode style tags in your files:

```markdown
#EXPORT_TAGS: #research #mathematics #canvasl #noexport
#EXPORT_TARGETS: docs, api, npm
#EXPORT_FORMATS: markdown, html, pdf
#NO_REF: true  # Don't include in reference indexes
#CLASSIFIED: internal  # Access level
```

## 🤖 AGENTS.md Templates

The framework provides templates for different component types:

### Full Template
For complex components with comprehensive requirements:
- Mathematical integrity
- Compiler integration
- CanvasL → AAL transformation
- Performance metrics
- Quality gates

### Simple Template
For smaller components:
- Core responsibilities
- File organization
- Basic testing requirements
- Status tracking

## 🔧 CLI Commands

### Metadata Management

```bash
# Update all metadata
mind-git-metadata update

# Validate metadata
mind-git-metadata validate

# Show metadata for file
mind-git-metadata show <path>

# Search metadata
mind-git-metadata search <query>

# Show system status
mind-git-metadata status
```

### Export Commands

```bash
# Export with filters
mind-git-metadata export docs --min-completeness 80 --only-verified

# Export specific layers
mind-git-metadata export api --layers 3,4,5

# Custom output directory
mind-git-metadata export research --output ./exports
```

### AGENTS.md Generation

```bash
# Generate for directory
mind-git-metadata generate-agents <path>

# Specify template type
mind-git-metadata generate-agents <path> --template compiler
```

## 📈 Integration with MIND-GIT

### Existing Components

The framework automatically integrates with existing MIND-GIT components:

- **CLI Tool**: `bin/mind-git-simple.cjs`
- **Obsidian Plugin**: `.obsidian/plugins/logos-visual-compiler/`
- **Core System**: `logos-system/src/`
- **Formal Verification**: `logos-system/formal/`
- **Research**: `docs/research/`

### Mathematical Foundation

Built upon the existing mathematical foundation:

- **Polynomial Algebra**: F₂[x] operations
- **Identity Chain**: Brahmagupta → Euler → Degen → Pfister → Adams
- **CanvasL Compiler**: Visual to mathematical transformation
- **Formal Verification**: Coq proofs and WebAssembly extraction

### Development Workflow

Integrated into the existing development workflow:

1. **Before Coding**: Check mathematical foundation requirements
2. **Implementation**: Follow CanvasL → AAL patterns
3. **Verification**: Run formal proofs and tests
4. **Documentation**: Auto-generate from metadata

## 🔍 Advanced Features

### Fingerprinting

Multi-factor fingerprinting for files:

1. **Content Hash**: SHA-256 of file content
2. **CanvasL Structure**: Hash of canvas node structure
3. **AAL Signature**: Mathematical signature of patterns
4. **File Metadata**: Size, modification time

### Relationship Mapping

Automatic relationship extraction:

- **Dependencies**: Input/output relationships
- **Cross-references**: Document references
- **Mathematical Lineage**: Foundation dependencies
- **Integration Points**: System connections

### Performance Monitoring

Built-in performance tracking:

- **Compilation Time**: Sub-100ms target
- **Memory Usage**: Linear complexity
- **Cache Hit Rate**: >85% target
- **Error Rate**: <0.1% target

## 📚 Examples

### Adding Metadata to a File

```markdown
---
id: "mind-git:compiler:ast-generator"
title: "CanvasL AST Generator"
type: ["implementation", "compiler", "typescript"]
category: "core-compiler"
layer: 3
dimensional: ["D4", "D5"]
mathematicalFoundation: ["polynomial-algebra", "identity-chain"]
hopfCompatible: true
normPreserving: true
canvasNodes: ["#Transform:", "#Verify:", "#Store:"]
nodeTypes: ["D4", "D5", "D6"]
compilationOrder: 3
spatialCoordinates: {x: -240, y: 180}
status: "complete"
completeness: 95
tested: true
verified: true
tags: ["compiler", "ast", "canvasl", "typescript", "verified"]
exportTargets: ["npm", "docs", "api"]
---

# CanvasL AST Generator

Implementation of CanvasL to AST transformation...
```

### Exporting Specific Components

```bash
# Export only verified components
npm run export:docs -- --only-verified

# Export specific layers
npm run export:api -- --layers 3,4

# Export with minimum completeness
npm run export:research -- --min-completeness 90
```

## 🔮 Future Enhancements

- **AI-Assisted Metadata**: Automatic metadata generation
- **Visual Relationship Mapping**: Interactive dependency graphs
- **Advanced Fingerprinting**: Mathematical structure analysis
- **IDE Integration**: VSCode and Obsidian plugin enhancements

## 📞 Support

For questions or issues:

1. Check the existing documentation in `dev-docs/`
2. Review the mathematical foundation in `logos-system/formal/`
3. Consult the CanvasL compiler documentation
4. Check the AGENTS.md files in each component

---

*This metadata framework is part of the MIND-GIT system for mathematical foundation of self-evolving computational systems.*