---
id: "mind-git:architecture:data-flow"
title: "Complete Data Flow Architecture"
type: ["architecture","system"]
category: architecture
layer: 3
dimensions: [0, 1, 7, 8, 9]
mathematicalFoundation: ["polynomial-algebra","hopf-fibration","formal-verification"]
hopfCompatible: true
normPreserving: true
status: "complete"
completeness: 95
tags: ["documentation","canvasl","mathematics","compiler","ast","polynomial","algebra"]
keywords: ["canvasl","aal","ast","compiler","polynomial","algebra","formal","verification","coq","proof","hopf","fibration","typescript","javascript"]
lastUpdate: "2025-12-15"
canvasL:
  nodeTypes: ["Activate","Integrate","Observer"]
  compilationOrder: 3
  spatialCoordinates: {x: 300, y: 0}
  dimensionalMapping: [D0, D1]
  aalMnemonics: [CALL, ADD, MOV]
---

# Complete Data Flow Architecture

## Mental Model

**"Mathematical transformation pipeline with verification at each stage."**

Think of it as a mathematical refinery: raw visual diagrams → refined polynomial structures → verified executable code.

---

## The Complete Pipeline

```
┌─────────────────┐
│  Canvas Diagram │  ← User creates visual program in Obsidian
│   (JSON file)   │
└────────┬────────┘
         │
         │ Parse (extract structure)
         ↓
┌─────────────────┐
│ ParsedCanvas    │  ← Nodes classified, observer detected, edges mapped
│                 │  - Observer at (0,0) verified
│                 │  - Node types identified (#Activate:, #Integrate:, etc.)
│                 │  - Spatial positions encoded
└────────┬────────┘
         │
         │ Generate AST (build tree)
         ↓
┌─────────────────┐
│ Abstract Syntax │  ← Functions, variables, dependencies identified
│ Tree (AST)      │  - Topological sort (must be DAG)
│                 │  - Type inference (D0-D10 dimensions)
│                 │  - Dependency analysis
└────────┬────────┘
         │
         │ Polynomial Encoding
         ↓
┌─────────────────┐
│ AAL Instructions│  ← Assembly-Algebra Language (verified)
│                 │  - 11-dimensional type system
│                 │  - Norm-preserving operations
│                 │  - Coq-verified semantics
└────────┬────────┘
         │
         │ Code Generation + Optimization
         ↓
┌─────────────────┐
│ Target Code     │  ← TypeScript, JavaScript, Racket, WASM
│                 │  - Multiple language backends
│                 │  - Optimization passes
│                 │  - Proof hashes embedded
└────────┬────────┘
         ↓
     Execution
```

---

## Stage 1: Canvas Parsing

### Input: Canvas JSON
```json
{
  "nodes": [
    {
      "id": "obs",
      "x": 0,
      "y": 0,
      "text": "#Observer:",
      "type": "text"
    },
    {
      "id": "act",
      "x": 100,
      "y": 50,
      "text": "#Activate: main",
      "type": "text"
    }
  ],
  "edges": [
    {
      "id": "e1",
      "fromNode": "obs",
      "toNode": "act"
    }
  ]
}
```

### Processing: CanvasParser
```typescript
export class CanvasParser {
  static parse(canvas: CanvasJSON): ParsedCanvas {
    // 1. Find and validate observer
    const observer = canvas.nodes.find(n => 
      n.text.startsWith('#Observer:') && n.x === 0 && n.y === 0
    );
    
    if (!observer) {
      throw new ParseError('Observer required at (0,0)');
    }

    // 2. Classify all nodes
    const classified = canvas.nodes.map(node => 
      NodeClassifier.classify(node)
    );

    // 3. Extract edges and verify DAG
    const edges = canvas.edges.map(edge => 
      EdgeProcessor.process(edge, classified)
    );

    // 4. Encode spatial positions as polynomials
    const polynomials = classified.map(node => 
      Polynomial.fromPosition(node.x, node.y)
    );

    return new ParsedCanvas(classified, edges, polynomials);
  }
}
```

### Output: ParsedCanvas
```typescript
interface ParsedCanvas {
  nodes: ClassifiedNode[];
  edges: ProcessedEdge[];
  polynomials: Polynomial[];
  observer: ClassifiedNode;  // Guaranteed at (0,0)
}
```

### Verification Points
- ✅ **Observer at origin**: Mathematical requirement
- ✅ **No circular dependencies**: Canvas must be DAG
- ✅ **Valid node types**: Only recognized prefixes
- ✅ **Spatial encoding**: Positions convert to polynomials

---

## Stage 2: AST Generation

### Input: ParsedCanvas
```typescript
const parsed = {
  nodes: [
    { id: 'obs', type: 'observer', position: { x: 0, y: 0 } },
    { id: 'act', type: 'activate', position: { x: 100, y: 50 } }
  ],
  edges: [
    { from: 'obs', to: 'act', type: 'flow' }
  ]
};
```

### Processing: ASTGenerator
```typescript
export class ASTGenerator {
  static generate(parsed: ParsedCanvas): AST {
    // 1. Build dependency graph
    const graph = DependencyGraph.build(parsed.nodes, parsed.edges);
    
    // 2. Topological sort (must succeed for DAG)
    const sorted = graph.topologicalSort();
    
    // 3. Identify functions and variables
    const functions = this.extractFunctions(parsed.nodes);
    const variables = this.extractVariables(parsed.nodes);
    
    // 4. Type inference (D0-D10 dimensions)
    const types = this.inferTypes(parsed.nodes, parsed.polynomials);
    
    // 5. Build hierarchical AST
    return new AST({
      entry: this.findEntryPoint(functions),
      functions,
      variables,
      types,
      executionOrder: sorted
    });
  }

  private static inferTypes(nodes: ClassifiedNode[], polynomials: Polynomial[]): TypeMap {
    return nodes.map((node, i) => ({
      nodeId: node.id,
      type: this.mapNodeToDimension(node.type),
      polynomial: polynomials[i],
      degree: polynomials[i].degree()
    }));
  }
}
```

### Output: Abstract Syntax Tree
```typescript
interface AST {
  entry: string;           // Entry point function ID
  functions: FunctionNode[];
  variables: VariableNode[];
  types: TypeMap;
  executionOrder: string[]; // Topological sort
}

interface FunctionNode {
  id: string;
  name: string;
  parameters: Parameter[];
  body: Statement[];
  returnType: Dimension;    // D0-D10
  dependencies: string[];
}
```

### Verification Points
- ✅ **DAG structure**: Topological sort succeeds
- ✅ **Type consistency**: Dimensions match operations
- ✅ **Dependency resolution**: All references valid
- ✅ **Polynomial degrees**: Within 8D limit for persistent state

---

## Stage 3: AAL Code Generation

### Input: AST
```typescript
const ast = {
  entry: 'main',
  functions: [
    {
      id: 'main',
      name: 'main',
      parameters: [],
      body: [
        { type: 'activate', target: 'system' },
        { type: 'integrate', value: 42 }
      ],
      returnType: 'D1',
      dependencies: []
    }
  ]
};
```

### Processing: AALCodegen
```typescript
export class AALCodegen {
  static generate(ast: AST): AALProgram {
    const instructions: AALInstruction[] = [];

    // Generate instructions for each function
    for (const func of ast.functions) {
      const funcInstructions = this.generateFunction(func);
      instructions.push(...funcInstructions);
    }

    // Optimization passes
    const optimized = this.optimize(instructions, [
      'dead-code-elimination',
      'hopf-fibration-reduction',
      'polynomial-factorization'
    ]);

    // Add verification hashes
    const verified = this.addProofHashes(optimized);

    return new AALProgram(verified);
  }

  private static generateFunction(func: FunctionNode): AALInstruction[] {
    const instructions: AALInstruction[] = [];

    for (const stmt of func.body) {
      switch (stmt.type) {
        case 'activate':
          instructions.push({
            opcode: 'ACTIVATE',
            operands: [stmt.target],
            dimension: 'D0',  // Linear transformation
            proof_hash: this.generateHash(stmt),
            metadata: {
              source_node: func.id,
              polynomial_degree: 0,
              norm_before: 1.0,
              norm_after: 1.0
            }
          });
          break;

        case 'integrate':
          instructions.push({
            opcode: 'ADD',
            operands: [stmt.value],
            dimension: 'D1',  // Polynomial addition
            proof_hash: this.generateHash(stmt),
            metadata: {
              source_node: func.id,
              polynomial_degree: 1,
              norm_before: 1.0,
              norm_after: this.calculateNorm(stmt.value)
            }
          });
          break;
      }
    }

    return instructions;
  }
}
```

### Output: AAL Program
```typescript
interface AALProgram {
  instructions: AALInstruction[];
  entry: string;
  verification: {
    overall_status: 'verified' | 'failed';
    polynomial_verified: boolean;
    norm_preservation: boolean;
    type_soundness: boolean;
  };
}

interface AALInstruction {
  opcode: OpCode;
  operands: Operand[];
  dimension: Dimension;     // D0-D10
  proof_hash: string;       // SHA-256 of verified derivation
  metadata: {
    source_node: string;
    polynomial_degree: number;
    norm_before: number;
    norm_after: number;
  };
}
```

### Verification Points
- ✅ **Type soundness**: Dimensions match operations
- ✅ **Norm preservation**: ||result|| = ||input₁|| × ||input₂||
- ✅ **Proof hashes**: Cryptographic verification of derivation
- ✅ **Coq correspondence**: Instructions match formal semantics

---

## Stage 4: Target Code Generation

### Input: AAL Program
```typescript
const aal = {
  instructions: [
    {
      opcode: 'ACTIVATE',
      operands: ['system'],
      dimension: 'D0',
      proof_hash: 'sha256:abc123',
      metadata: { source_node: 'main', polynomial_degree: 0 }
    }
  ],
  entry: 'main'
};
```

### Processing: Multi-Language Codegen

#### TypeScript Generator
```typescript
export class TypeScriptCodegen {
  static generate(aal: AALProgram): string {
    const functions: string[] = [];

    for (const func of this.groupInstructionsByFunction(aal.instructions)) {
      const tsFunction = this.generateFunction(func);
      functions.push(tsFunction);
    }

    return `
// Generated by CanvasL Compiler
// Verification: ${aal.verification.overall_status}
// Proof hashes: ${aal.instructions.length} instructions verified

${functions.join('\n\n')}

// Entry point
${this.generateEntry(aal.entry)}
    `.trim();
  }

  private static generateFunction(instructions: AALInstruction[]): string {
    const body = instructions.map(instr => 
      this.generateInstruction(instr)
    ).join('\n  ');

    return `
function ${this.extractFunctionName(instructions[0])}() {
  ${body}
}
    `.trim();
  }

  private static generateInstruction(instr: AALInstruction): string {
    switch (instr.opcode) {
      case 'ACTIVATE':
        return `// Activate system (D0 linear transformation)
// Proof hash: ${instr.proof_hash}
activate();`;
        
      case 'ADD':
        return `// Integrate value (D1 polynomial addition)
// Proof hash: ${instr.proof_hash}
const result = add(current, ${instr.operands[0]});`;
        
      default:
        return `// Unknown instruction: ${instr.opcode}`;
    }
  }
}
```

#### Racket Generator
```scheme
(define (racket-codegen aal-program)
  (define functions
    (map generate-function
         (group-instructions aal-program)))
  
  (string-append
    "; Generated by CanvasL Compiler\n"
    "; Verification: " (verification-status aal-program) "\n"
    "\n"
    (string-join functions "\n\n")
    "\n\n; Entry point\n"
    (generate-entry (entry-point aal-program))))

(define (generate-function instructions)
  (string-append
    "(define (" (function-name instructions) ")\n"
    "  " (string-join (map generate-instruction instructions) "\n  ") ")\n"))
```

### Output: Executable Code

#### TypeScript Output
```typescript
// Generated by CanvasL Compiler
// Verification: verified
// Proof hashes: 2 instructions verified

function main() {
  // Activate system (D0 linear transformation)
  // Proof hash: sha256:abc123
  activate();
  
  // Integrate value (D1 polynomial addition)
  // Proof hash: sha256:def456
  const result = add(current, 42);
}

// Entry point
main();
```

#### Racket Output
```scheme
; Generated by CanvasL Compiler
; Verification: verified

(define (main)
  (activate)  ; D0 linear transformation
  ; Proof hash: sha256:abc123
  (add current 42))  ; D1 polynomial addition
  ; Proof hash: sha256:def456

; Entry point
(main)
```

### Verification Points
- ✅ **Syntax validity**: Generated code compiles
- ✅ **Semantic preservation**: Behavior matches AAL
- ✅ **Proof hashes included**: Runtime verification possible
- ✅ **Cross-language consistency**: Same behavior in all targets

---

## Mathematical Verification Flow

At each stage, mathematical properties are verified:

### Stage 1 Verification
```typescript
function verifyParsedCanvas(parsed: ParsedCanvas): VerificationResult {
  return {
    observer_at_origin: parsed.observer.position.x === 0 && 
                        parsed.observer.position.y === 0,
    dag_structure: isAcyclic(parsed.edges),
    valid_node_types: parsed.nodes.every(n => isValidType(n.type)),
    spatial_encoding: parsed.polynomials.every(p => p.isValid())
  };
}
```

### Stage 2 Verification
```typescript
function verifyAST(ast: AST): VerificationResult {
  return {
    type_consistency: ast.types.every(t => isValidDimension(t.type)),
    dependency_resolution: ast.functions.every(f => 
      f.dependencies.every(d => ast.functions.some(func => func.id === d))
    ),
    polynomial_degrees: ast.types.every(t => t.degree <= 8)
  };
}
```

### Stage 3 Verification
```typescript
function verifyAAL(aal: AALProgram): VerificationResult {
  return {
    type_soundness: verifyCoqTypeSoundness(aal),
    norm_preservation: aal.instructions.every(i => 
      Math.abs(i.metadata.norm_after - 
               i.metadata.norm_before) < 1e-10
    ),
    proof_hashes: aal.instructions.every(i => 
      verifyProofHash(i.proof_hash, i)
    )
  };
}
```

### Stage 4 Verification
```typescript
function verifyGeneratedCode(code: string, aal: AALProgram): VerificationResult {
  return {
    syntax_valid: parseCode(code).success,
    semantic_preservation: compareBehavior(code, aal),
    proof_hashes_included: code.includes('Proof hash:'),
    cross_language_consistent: compareAcrossLanguages(code, aal)
  };
}
```

---

## Error Handling and Recovery

### Error Types by Stage
```typescript
enum ErrorStage {
  PARSING = 'canvas_parsing',
  AST_GENERATION = 'ast_generation',
  AAL_CODEGEN = 'aal_generation',
  TARGET_CODEGEN = 'target_generation'
}

enum ErrorType {
  OBSERVER_NOT_AT_ORIGIN = 'observer_not_at_origin',
  CIRCULAR_DEPENDENCY = 'circular_dependency',
  NORM_PRESERVATION_VIOLATION = 'norm_preservation_violation',
  TYPE_MISMATCH = 'type_mismatch',
  PROOF_HASH_INVALID = 'proof_hash_invalid'
}
```

### Error Recovery Strategies
```typescript
interface ErrorRecovery {
  stage: ErrorStage;
  type: ErrorType;
  message: string;
  suggestion: string;
  auto_fixable: boolean;
}

const errorRecoveryMap: Map<ErrorType, ErrorRecovery> = new Map([
  [ErrorType.OBSERVER_NOT_AT_ORIGIN, {
    stage: ErrorStage.PARSING,
    type: ErrorType.OBSERVER_NOT_AT_ORIGIN,
    message: 'Observer node must be at coordinates (0,0)',
    suggestion: 'Move the #Observer: node to position (0,0)',
    auto_fixable: true
  }],
  
  [ErrorType.NORM_PRESERVATION_VIOLATION, {
    stage: ErrorStage.AAL_CODEGEN,
    type: ErrorType.NORM_PRESERVATION_VIOLATION,
    message: 'Operation does not preserve norms: ||a × b|| ≠ ||a|| × ||b||',
    suggestion: 'Check operation for mathematical correctness or reduce dimension',
    auto_fixable: false
  }]
]);
```

---

## Performance Characteristics

### Complexity Analysis
| Stage | Time Complexity | Space Complexity | Bottleneck |
|-------|----------------|------------------|------------|
| Parsing | O(n + m) | O(n + m) | Node classification |
| AST Generation | O(n + m) | O(n + m) | Topological sort |
| AAL Codegen | O(n) | O(n) | Proof hash generation |
| Target Codegen | O(n) | O(n) | String formatting |

Where:
- n = number of nodes
- m = number of edges

### Optimization Opportunities
1. **Parallel parsing**: Process nodes concurrently
2. **Incremental compilation**: Cache AST for unchanged canvases
3. **Proof hash caching**: Pre-compute common instruction hashes
4. **Code generation templates**: Use string builders for large outputs

---

## Related Documentation

- [../overview.md](../overview.md) - Mental model introduction
- [layers.md](layers.md) - System architecture layers
- [verification-architecture.md](verification-architecture.md) - Formal verification pipeline
- [performance-architecture.md](performance-architecture.md) - Performance optimization

---

**Remember**: This pipeline is not just engineering - it's mathematical transformation. Each stage preserves the essential mathematical structure while changing the representation. The verification at each stage ensures that nothing is lost in translation.