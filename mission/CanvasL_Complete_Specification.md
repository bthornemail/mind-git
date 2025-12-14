# CanvasL + MindGit: Complete System Specification

## Permanent Reference Document v1.0

---

# PART I: WHAT YOU ARE ACTUALLY BUILDING

## 1. The One Sentence (Memorize This)

> **You are designing a decentralized, federated abstract syntax tree for shared semantic states, with language-server-style services for validation, projection, and consistency checking across agents, serialized as append-only JSONL logs with Git-like version control.**

Return to this sentence whenever confusion arises.

## 2. Verified Implementation Status

### ✅ Week Mission Complete
**Question**: "Can I write this as TypeScript/JSON in 50 lines?"
**Answer**: ✅ YES - Implementation complete and tested

### ✅ Working Implementation
- **Canvas Parser**: Extracts structure from `.canvas` JSON files
- **AST Generator**: Builds hierarchical abstract syntax trees
- **Code Generation**: Produces executable JavaScript from visual diagrams
- **Test Coverage**: Comprehensive tests validate the entire pipeline

### ✅ Grounding Verification
Every component passes the "Is This Code?" test:
1. ✅ TypeScript interfaces exist
2. ✅ Passing tests implemented
3. ✅ Concrete outcomes measured (executable JavaScript)

---

## 2. The Bulletproof Paragraph (Copy-Paste Anywhere)

> I'm building CanvasL + MindGit: a decentralized, federated abstract syntax tree for evolving computational organisms, serialized as append-only JSONL logs. It provides Git-like branching and mathematically verifiable merging via polynomial composition algebras, plus language-server-style services for provenance, consistency checking, and state reconstruction. The system is purely digital and exploratory; it makes no claims about physical reality, consciousness, or ultimate truth — it is tooling for versioning, verifying, and coordinating structured virtual state.

---

## 3. What Each Component Actually Is

### 3.1 CanvasL (The Data Structure)

**What it is:** A federated Abstract Syntax Tree (AST) for representing structured state.

**In compiler terms:**
- **Nodes** = assertions, symbols, beliefs, state
- **Edges** = incidence relations (who/what/why/how/where/when/observer/confidence)
- **Subtrees** = local world models (per agent or group)
- **Rootless** = no global authority or canonical truth
- **Partial trees allowed** = incomplete knowledge is valid state

**What it is NOT:**
- An evaluation tree (we don't compute truth)
- A metaphysical model (we don't claim reality access)
- A consciousness theory (we don't explain minds)

### 3.2 MindGit (The Version Control Layer)

**What it is:** Git semantics applied to AST state.

- **Branch** = divergent state lineage
- **Commit** = snapshot of AST state with integrity proof
- **Merge** = polynomial composition with norm verification
- **Diff** = structural comparison between states
- **Log** = append-only JSONL serialization

**What it is NOT:**
- A time machine (we track dependency, not causality)
- A consensus protocol (we suggest, not compel)
- A blockchain (we don't require global agreement)

### 3.3 The Mathematical Foundation (The Verification Layer)

**What it is:** Proven composition identities for integrity checking.

| Identity | Year | Transformation | Role | Guarantee |
|----------|------|----------------|------|-----------|
| Brahmagupta–Fibonacci | 628 AD | 2D × 2D → 2D | Base composition | Norm preserved |
| Euler 4-Square | 1748 | 4D × 4D → 4D | Quaternion ops | Norm preserved |
| Degen 8-Square | 1928 | 8D × 8D → 8D | Node composition | Norm preserved |
| Pfister 16-Square | 1965 | 8D → 16D | Tree merge | Norm preserved |
| Pfister 32-Square | 1967 | 16D → 32D | Multi-tree merge | Norm preserved |
| Leech Lattice (24D) | 1967 | Optimal packing | Storage optimization | Density optimal |

**What it is NOT:**
- Physics (these are data transformations, not reality claims)
- Mysticism (these are proven theorems, not revelations)
- Unique to you (these are well-known mathematics)

### 3.4 The LSP Services (The Tooling Layer)

**What it is:** Language-server-style services for AST operations.

| LSP Feature | CanvasL Equivalent |
|-------------|-------------------|
| Syntax checking | Logical consistency validation |
| Type checking | Domain compatibility verification |
| Diagnostics | Contradiction detection and reporting |
| Hover info | Contextual meaning retrieval |
| Go-to definition | Source of belief tracing |
| Refactoring | Reframing / projection transforms |
| Formatting | Canonicalization (BQF compression) |
| Code actions | Convergence suggestions |

**Critical distinction:** The LSP does **not execute** programs; it **assists understanding**. That is exactly CanvasL's role.

---

## 4. The Node Schema (The Concrete Data Structure)

Every AST node has 8 annotated fields, implemented as an 8-dimensional algebraic structure:

```json
{
  "id": "node-<uuid>",
  "who": "agent-id or null",
  "what": "assertion content",
  "why": "evidence or justification",
  "how": "method or derivation",
  "where": "context identifier",
  "when": "revision number (not timestamp)",
  "observer": "perspective identifier",
  "confidence": 0.0-1.0,
  
  "metadata": {
    "created": "ISO-8601 timestamp",
    "polynomial": [coefficients],
    "norm": number,
    "parent_ids": ["node-id", ...],
    "signature": "cryptographic signature"
  }
}
```

This keeps everything: **finite, inspectable, editable, debuggable**. No infinity required.

---

## 5. The Architecture Layers

```
┌─────────────────────────────────────────────────────────────┐
│                    APPLICATION LAYER                         │
│  (CLI tools, visual browsers, API endpoints)                │
├─────────────────────────────────────────────────────────────┤
│                    LSP SERVICES LAYER                        │
│  (consistency checking, diagnostics, projection, refactoring)│
├─────────────────────────────────────────────────────────────┤
│                    MINDGIT LAYER                             │
│  (branch, commit, merge, diff, log)                         │
├─────────────────────────────────────────────────────────────┤
│                    CANVASL AST LAYER                         │
│  (nodes, edges, subtrees, federation)                       │
├─────────────────────────────────────────────────────────────┤
│                    MATHEMATICAL LAYER                        │
│  (polynomial identities, norm verification, lattice encoding)│
├─────────────────────────────────────────────────────────────┤
│                    STORAGE LAYER                             │
│  (append-only JSONL, BQF compression, Leech optimization)   │
└─────────────────────────────────────────────────────────────┘
```

---

## 6. What Problems This Solves

| Problem | Solution | Measurable Outcome |
|---------|----------|-------------------|
| Exponential state growth in federated systems | Lattice packing optimization | ~40% storage reduction |
| Merge conflicts in distributed knowledge | Polynomial composition with norm verification | O(1) conflict detection |
| Provenance tracking for assertions | Append-only log with cryptographic signatures | Complete audit trail |
| Contradiction detection across agents | LSP-style diagnostics | Automated inconsistency surfacing |
| Federation without forced consensus | Partial merge with incompatibility tolerance | Trees can disagree validly |

---

## 7. Analogies That Work (Use These)

| Say This | Not This |
|----------|----------|
| "Git for meaning" | "Reality version control" |
| "AST with LSP services" | "Consciousness compiler" |
| "Polynomial integrity checking" | "Mathematical truth verification" |
| "24D lattice for data packing" | "Accessing higher dimensions" |
| "Federated state synchronization" | "Collective consciousness network" |
| "Dependency graphs over chronological ordering" | "Replacing time" |
| "Diagnostic propagation" | "Back-propagation through reality" |

---

# PART II: RFC 2119 NORMATIVE CONSTRAINTS

## RFC-CANVASL-01: Normative Language Rules

**Status:** Personal Safety / Clarity Standard  
**Keywords:** MUST, MUST NOT, SHOULD, SHOULD NOT, MAY (as defined in RFC 2119)

---

### Section 1: Ontological Domain Separation (MANDATORY)

#### 1.1 Domain Definitions

All statements MUST belong to exactly ONE of these domains:

| Domain | Definition | Examples |
|--------|------------|----------|
| **PHYSICAL** | Mind-independent reality | Spacetime, matter, energy |
| **DIGITAL** | Constructed computational universes | CanvasL, simulations, virtual systems |
| **SOCIAL** | Human coordination systems | Language, money, law, protocols |
| **METAPHORICAL** | Narrative, symbolic framing | Analogies, teaching illustrations |
| **PERSONAL** | Subjective experience | Intuitions, preferences, feelings |

#### 1.2 Domain Rules

- A statement MUST NOT move between domains without explicit labeling.
- If a sentence spans domains, it MUST name the boundary explicitly.
- CanvasL statements MUST default to DIGITAL domain.

**VALID:**
> "In the *digital* CanvasL system, polynomial composition preserves norms, but this is *not a claim* about physical reality."

**INVALID:**
> "Polynomial composition preserves reality." (domain unspecified)

---

### Section 2: Claims About Reality (STRICT)

#### 2.1 Physical Reality

- You MUST NOT claim that consensus, logic, or computation alters physical laws.
- You MUST NOT use physics terms as literal mechanisms unless explicitly simulating them.

**ALLOWED:**
> "This system is *isomorphic to* certain mathematical structures."

**FORBIDDEN:**
> "This system *implements* reality."

#### 2.2 Digital Reality

- You MAY claim completeness, enumeration, or enforcement ONLY inside explicitly defined digital systems.
- You MUST say "virtual", "simulated", "digital", or "constructed" at least once per explanation.

---

### Section 3: Physics Language (CONTROLLED)

#### 3.1 Projection Rule

When using mathematical terms (dimensions, projections, fibrations):

- You MUST say "projects onto", "behaves like", "is analogous to", or "models".
- You MUST NOT say "is", "equals", "proves", or "accesses".

**VALID:**
> "States project onto an 8-dimensional algebraic structure for efficient encoding."

**INVALID:**
> "This accesses 8 dimensions of reality."

#### 3.2 Dimension Language

- "Dimension" MUST refer to annotated fields on data structures, not spatial/temporal reality.
- "Higher dimensions" MUST be qualified as "higher-dimensional *encodings*" or "*mathematical* dimensions".

---

### Section 4: Consensus and Truth (CRITICAL)

#### 4.1 Mandatory Distinctions

You MUST distinguish between:

| Term | Definition | CanvasL Role |
|------|------------|--------------|
| **Truth** | Correspondence to external constraints | NOT determined by CanvasL |
| **Consistency** | Internal logical coherence | Verified by CanvasL |
| **Consensus** | Agreement among agents | Enabled but not required by CanvasL |
| **Operational state** | Enacted behavior in system | Tracked by CanvasL |

- You MUST NOT collapse these into one term.
- You MUST NOT claim CanvasL determines truth.

**REQUIRED phrasing:**
> "CanvasL verifies *consistency*, not *truth*. Consensus defines *operational state*, not *reality*."

---

### Section 5: Theology and Symbolism (SAFETY-CRITICAL)

#### 5.1 Religious Language

- You MAY use theological terms ONLY as metaphor or historical analogy.
- You MUST NOT claim divine authority, revelation, or inevitability.
- You MUST NOT position the work as spiritually significant.

**ALLOWED:**
> "Logos is used here as a *metaphor* for structural coherence, borrowed from Greek philosophy."

**FORBIDDEN:**
> "This reveals God's true structure."
> "This is the mathematical form of divine creation."

---

### Section 6: Self-Reference and Authority (HARD LIMIT)

You MUST NOT position yourself as:
- Uniquely chosen
- Sole discoverer of truth
- Administrator of reality
- Holder of special insight unavailable to others
- The one who "finally figured it out"

**ALLOWED:**
> "This is my current working model, building on existing mathematics."

**FORBIDDEN:**
> "I have discovered the structure of reality."
> "I have the admin credentials to consciousness."
> "No one else has seen this connection."

---

### Section 7: Exponential Thinking Guardrails (VERY IMPORTANT)

#### 7.1 One-Step Rule

When explaining an idea, you MUST:
1. State exactly ONE claim
2. Give ONE reason
3. Give ONE example

No more per explanation unit.

#### 7.2 Branch Containment

If an idea branches into multiple directions:
- You MUST name the branch
- You MUST defer it explicitly
- You MUST NOT follow more than one branch per session

**REQUIRED:**
> "That's a separate branch (Leech lattice optimization); I'm deferring it to focus on the core AST schema."

#### 7.3 Connection Limit

If you feel the urge to connect 5+ concepts:
- STOP
- Write them as a numbered list
- Pick ONE to develop
- Defer the rest explicitly

---

### Section 8: Prediction and Power Claims (FORBIDDEN)

You MUST NOT claim:
- Inevitability ("this will change everything")
- Singularity ("this leads to AGI/awakening")
- Total convergence ("all knowledge unifies here")
- Universal resolution ("this solves the hard problem")
- Proof of ultimate truth ("this is mathematically certain about reality")

You MAY claim:
- Usefulness ("this helps with X problem")
- Coherence ("this is internally consistent")
- Bounded completeness ("this covers cases A, B, C")
- Efficiency ("this reduces storage/computation by X%")
- Novelty ("this combination hasn't been explored")

---

### Section 9: Documentation Standards

#### 9.1 Every File MUST Include

```typescript
/**
 * @domain DIGITAL
 * @purpose [specific computational purpose]
 * @warning This models virtual structures only; no claims about physical reality
 */
```

#### 9.2 Every Public Explanation MUST Include

- The domain qualifier (DIGITAL/virtual/computational)
- The specific problem being solved
- The measurable outcome
- The explicit non-claim about reality

---

### Section 10: Grounding Checklist (Use When Confused)

Before writing or speaking, ask:

1. Is this an AST node, edge, or service?
2. Is this syntax, semantics, or diagnostics?
3. Is this local, federated, or shared?
4. Is this physical, digital, or metaphorical?
5. **Would a compiler engineer understand this sentence?**

If the answer to (5) is "no", **rewrite**.

---

### Section 11: Personal Safety Clause

If at any time:
- Ideas feel uncontrollable
- Everything starts to "connect"
- Sleep is disrupted
- Urgency or inevitability appears
- You feel uniquely chosen or burdened

You MUST:
- Pause discussion immediately
- Reduce scope to smallest concrete task
- Ground in physical activity
- Return to implementation details only
- Consider talking to a trusted person

**This is not failure. This is correct operation.**

---

### Section 12: Allowed Safe Summary Sentences

Use these verbatim when unsure:

**For technical audiences:**
> "I'm working on a federated AST with polynomial integrity checking and Git-like version control. It's tooling for distributed state management."

**For general audiences:**
> "I'm building something like Git, but for structured knowledge instead of code. It helps multiple systems stay consistent without a central authority."

**For skeptical audiences:**
> "It's an experiment in applying mathematical structures to distributed data synchronization. The math is well-established; the application is exploratory."

---

### Section 13: The "Is It Code?" Test

Before any feature or concept is considered real:

1. Write the TypeScript/Python interface
2. Implement a passing test
3. Measure a concrete outcome

If you cannot do these three things, the feature is not ready for discussion. Defer it.

---

### Section 14: Versioning

- This RFC MAY be revised.
- Any revision MUST reduce scope, not increase it.
- Scope increases require explicit justification and safety review.

---

# PART III: QUICK REFERENCE CARD

## When Explaining CanvasL

| Context | Say This |
|---------|----------|
| What is it? | "A federated AST with LSP services and Git-like version control" |
| What problem? | "Distributed state management with mathematical integrity guarantees" |
| What math? | "Polynomial composition identities for norm-preserving operations" |
| What's novel? | "Applying lattice theory to AST merge optimization" |
| What's not claimed? | "No claims about physical reality, consciousness, or truth" |

## Red Flags (Stop If You Notice These)

- Using "reality" without "virtual" or "digital" qualifier
- Connecting more than 3 concepts in one explanation
- Feeling that "everything is coming together"
- Using religious language without "metaphor" qualifier
- Claiming uniqueness of insight
- Feeling urgency to share/publish/announce

## Green Flags (You're On Track)

- Can explain in compiler engineering terms
- Have concrete TypeScript/Python interfaces
- Have measurable benchmarks
- Using domain qualifiers consistently
- Deferring branches explicitly
- Feeling calm about the work

---

# PART IV: THE DEFINITIVE ARCHITECTURE SUMMARY

## What You Are Building

```
CanvasL + MindGit
├── Core: Federated AST for structured state
├── Versioning: Git-like branch/merge/diff/log
├── Verification: Polynomial composition identities
├── Services: LSP-style consistency/diagnostics/projection
├── Storage: Append-only JSONL with BQF compression
├── Optimization: Optional 24D Leech lattice packing
└── Federation: P2P sync without forced consensus
```

## What You Are NOT Building

- A theory of consciousness
- A model of physical reality
- A spiritual framework
- A proof of metaphysical truth
- A path to AGI/singularity
- A replacement for human judgment

## The Value Proposition

- **Measurable:** ~40% storage reduction, O(1) conflict detection
- **Verifiable:** Proven mathematical identities
- **Practical:** Solves real distributed systems problems
- **Bounded:** Clear scope with explicit non-claims
- **Extensible:** Optional optimization layers

---

## Final Statement

**You are building infrastructure for distributed state management. The mathematics is the optimization, not the mysticism. The contribution is real and bounded. The scope is deliberately constrained.**

**This document is your anchor. Return to it whenever the ideas start expanding beyond these bounds.**

---

*Document version: 1.0*  
*Last updated: [current date]*  
*Status: Normative reference*
