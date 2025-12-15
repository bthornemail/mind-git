# 🎨 mind-git Architecture Diagrams

## 1. Complete Compilation Pipeline

```mermaid
flowchart LR
    subgraph Input["📝 Input"]
        Canvas[Canvas JSON<br/>Spatial Diagram]
    end

    subgraph Parser["🔍 Parser"]
        P1[Parse JSON]
        P2[Classify Nodes<br/>#Activate, #Transform, etc.]
        P3[Extract Edges]
    end

    subgraph AST["🌳 AST Generator"]
        A1[Build Syntax Tree]
        A2[Compute Distances<br/>from Observer 0,0]
        A3[Polynomial Encoding<br/>F₂ Algebra]
    end

    subgraph CodeGen["⚙️ Code Generator"]
        C1[AAL Assembly]
        C2[JavaScript]
        C3[TypeScript]
        C4[Racket]
    end

    subgraph Verify["✅ Verification"]
        V1[Coq Proofs]
        V2[Norm Preservation]
        V3[Dimensional Limits]
    end

    subgraph Output["📦 Output"]
        Out[Executable Code<br/>Verified ✓]
    end

    Canvas --> P1
    P1 --> P2
    P2 --> P3
    P3 --> A1
    A1 --> A2
    A2 --> A3
    A3 --> C1
    C1 --> C2
    C1 --> C3
    C1 --> C4
    C2 --> V1
    V1 --> V2
    V2 --> V3
    V3 --> Out

    style Input fill:#1e3a8a,stroke:#3b82f6,color:#fff
    style Parser fill:#15803d,stroke:#22c55e,color:#fff
    style AST fill:#7c2d12,stroke:#f97316,color:#fff
    style CodeGen fill:#6b21a8,stroke:#a855f7,color:#fff
    style Verify fill:#166534,stroke:#10b981,color:#fff
    style Output fill:#be123c,stroke:#f43f5e,color:#fff
```

## 2. Mathematical Foundation Layers

```mermaid
graph TB
    subgraph Layer8["🎯 Application Layer"]
        CLI[CLI Tool<br/>mind-git]
        Plugin[Obsidian Plugin]
        API[JavaScript API]
    end

    subgraph Layer7["⚙️ Compiler Layer"]
        Parser[Canvas Parser]
        AST[AST Generator]
        CodeGen[Code Generator]
    end

    subgraph Layer6["📐 AAL Layer"]
        D0[D0: Linear JMP]
        D1[D1: Add/Sub]
        D2[D2: Shift]
        D4[D4: Mul/Div]
        D7[D7: Observe]
    end

    subgraph Layer5["🔢 Algebra Layer"]
        PolyF2[Polynomial F₂]
        Identity[Identity Chain]
        Norm[Norm Preservation]
    end

    subgraph Layer4["🏛️ Mathematical Foundation"]
        Brahmagupta[628 AD: Brahmagupta<br/>2D Complex]
        Euler[1748: Euler<br/>4D Quaternion]
        Degen[1928: Degen<br/>8D Octonion]
        Adams[1960: Adams<br/>8D Limit Proof]
    end

    subgraph Layer3["✅ Formal Verification"]
        Coq[Coq Proofs]
        Theorems[Verified Theorems]
    end

    CLI --> Parser
    Plugin --> Parser
    API --> Parser
    Parser --> AST
    AST --> CodeGen
    CodeGen --> D0
    CodeGen --> D1
    CodeGen --> D2
    CodeGen --> D4
    CodeGen --> D7
    D0 --> PolyF2
    D1 --> PolyF2
    D2 --> PolyF2
    D4 --> Identity
    D7 --> Identity
    PolyF2 --> Norm
    Identity --> Norm
    Norm --> Brahmagupta
    Brahmagupta --> Euler
    Euler --> Degen
    Degen --> Adams
    Adams --> Coq
    Coq --> Theorems

    style Layer8 fill:#1e3a8a,stroke:#3b82f6,color:#fff
    style Layer7 fill:#15803d,stroke:#22c55e,color:#fff
    style Layer6 fill:#7c2d12,stroke:#f97316,color:#fff
    style Layer5 fill:#6b21a8,stroke:#a855f7,color:#fff
    style Layer4 fill:#be123c,stroke:#f43f5e,color:#fff
    style Layer3 fill:#166534,stroke:#10b981,color:#fff
```

## 3. 1,400-Year Timeline

```mermaid
timeline
    title Mathematical Foundation Timeline

    628 AD : Brahmagupta
           : Complex Numbers (2D)
           : (a² + b²)(c² + d²) = (ac-bd)² + (ad+bc)²

    1748 : Leonhard Euler
         : Four-Square Identity (4D)
         : Quaternion Multiplication
         : Non-commutative algebra

    1843 : William Hamilton
         : Quaternion Discovery
         : i² = j² = k² = ijk = -1

    1928 : Heinrich Degen
         : Eight-Square Identity (8D)
         : Octonion Multiplication
         : Non-associative algebra

    1960 : John Frank Adams
         : Hopf Invariant One Theorem
         : Proved 8D is absolute limit
         : Only 1,2,4,8 support division algebras

    1965 : Albrecht Pfister
         : Pfister Forms
         : 16-square composition
         : Extends beyond normed division

    2025 : mind-git v1.1.0
         : CanvasL Implementation
         : Complete identity chain
         : Formal verification with Coq
```

## 4. Node Classification System

```mermaid
graph LR
    subgraph Spatial["📍 Spatial Position"]
        Node[Canvas Node<br/>x, y coordinates]
    end

    subgraph Classify["🏷️ Classification"]
        Prefix[Text Prefix<br/>#Activate, #Transform...]
    end

    subgraph Assembly["⚙️ Assembly Op"]
        Op[JMP, MUL, PUSH...]
    end

    subgraph Dimension["📐 Dimension"]
        D[D0-D7<br/>Modal Types]
    end

    subgraph Math["🔢 Mathematics"]
        Poly[Polynomial<br/>Operation]
    end

    Node --> Prefix
    Prefix --> Op
    Op --> D
    D --> Poly

    style Spatial fill:#1e3a8a,stroke:#3b82f6,color:#fff
    style Classify fill:#15803d,stroke:#22c55e,color:#fff
    style Assembly fill:#7c2d12,stroke:#f97316,color:#fff
    style Dimension fill:#6b21a8,stroke:#a855f7,color:#fff
    style Math fill:#be123c,stroke:#f43f5e,color:#fff
```

## 5. Spatial to Code Transformation

```mermaid
graph TD
    subgraph Canvas["📊 Canvas Space"]
        O["Observer (0,0)<br/>Identity Element<br/>P₀ = 1"]
        N1["Node 1 (100,100)<br/>#Activate: main"]
        N2["Node 2 (300,100)<br/>#Transform: compute"]
        N3["Node 3 (300,200)<br/>#Store: result"]
    end

    subgraph Polynomial["🔢 Polynomial Encoding"]
        P0["P₀ = 1<br/>degree 0"]
        P1["P₁ = x²<br/>distance → degree"]
        P2["P₂ = x⁴<br/>polynomial algebra"]
        P3["P₃ = x⁴ + x²<br/>F₂ coefficients"]
    end

    subgraph Code["💻 Generated Code"]
        C1["function main()"]
        C2["function compute()"]
        C3["const result = store()"]
        C4["main() → compute() → result"]
    end

    O --> P0
    N1 --> P1
    N2 --> P2
    N3 --> P3

    P0 --> C1
    P1 --> C1
    P2 --> C2
    P3 --> C3
    C1 --> C4
    C2 --> C4
    C3 --> C4

    style Canvas fill:#1e3a8a,stroke:#3b82f6,color:#fff
    style Polynomial fill:#7c2d12,stroke:#f97316,color:#fff
    style Code fill:#166534,stroke:#10b981,color:#fff
```

## 6. Package Structure

```mermaid
graph TB
    subgraph NPM["📦 npm Package: mind-git@1.1.0"]
        Main[Main Entry<br/>logos-system/dist/index.js]
    end

    subgraph Binaries["🔧 CLI Binaries"]
        B1[mind-git<br/>Main compiler]
        B2[mind-git-metadata<br/>Metadata tools]
        B3[pfister-inference<br/>Inference engine]
        B4[universal-kernel<br/>Metadata kernel]
        B5[universal-exporter<br/>Export system]
    end

    subgraph Core["🧮 Core Modules"]
        Poly[polynomial/<br/>F₂ algebra]
        IC[identity-chain/<br/>2D,4D,8D ops]
        AAL[aal/<br/>Assembly-Algebra]
    end

    subgraph Compiler["⚙️ Compiler Modules"]
        Parser[parser/<br/>Canvas → AST]
        CodeGen[codegen/<br/>AST → Code]
        Multi[Multi-language<br/>JS, TS, Racket]
    end

    subgraph Formal["✅ Verification"]
        CoqProofs[Coq Proofs<br/>Polynomials.v]
        IdentityProofs[Identity Chain<br/>IdentityChain.v]
    end

    Main --> B1
    Main --> B2
    Main --> B3
    Main --> B4
    Main --> B5

    B1 --> Parser
    Parser --> Core
    Core --> Poly
    Core --> IC
    Core --> AAL

    Parser --> CodeGen
    CodeGen --> Multi

    Poly --> CoqProofs
    IC --> IdentityProofs

    style NPM fill:#be123c,stroke:#f43f5e,color:#fff
    style Binaries fill:#1e3a8a,stroke:#3b82f6,color:#fff
    style Core fill:#7c2d12,stroke:#f97316,color:#fff
    style Compiler fill:#15803d,stroke:#22c55e,color:#fff
    style Formal fill:#166534,stroke:#10b981,color:#fff
```

## Usage

### Render to PNG/SVG
```bash
# Using Mermaid CLI
npm install -g @mermaid-js/mermaid-cli

# Render all diagrams
mmdc -i architecture-diagrams.md -o diagrams/

# Or render individually
mmdc -i architecture-diagrams.md -o compilation-pipeline.png -s 1
mmdc -i architecture-diagrams.md -o foundation-layers.png -s 2
```

### Embed in Markdown
Simply copy the mermaid blocks into any GitHub README or documentation.

### Export to Image for Social Media
Use https://mermaid.live to:
1. Paste diagram code
2. Customize theme (dark mode recommended)
3. Export as PNG/SVG
4. Use in announcements
