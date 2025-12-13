// ============================================================================
// CANVAS POLYNOMIAL ALGEBRA SYSTEM
// A multivariate polynomial encoding of Obsidian Canvas structure
// ============================================================================

// ============================================================================
// 1. CORE ALGEBRAIC STRUCTURES
// ============================================================================

/**
 * A polynomial term in the canvas space: ℝ[x,y,w,h,c,t,id]
 * Each canvas node IS a polynomial in 7-dimensional space
 */
interface PolynomialTerm {
  // Geometric variables (continuous)
  x: number;        // Position X ∈ ℝ
  y: number;        // Position Y ∈ ℝ  
  w: number;        // Width ∈ ℝ⁺
  h: number;        // Height ∈ ℝ⁺
  
  // Discrete variables
  c: number;        // Color ∈ ℤ₈ (modulo 8)
  t: NodeType;      // Type ∈ {text, file, link, group, control}
  id: string;       // Unique identifier
  
  // Polynomial properties
  degree: number;   // Polynomial degree (0-7, maps to dimensions)
  coefficients: number[];  // [a₀, a₁x, a₂y, a₃w, a₄h, a₅c, a₆t, a₇id]
  
  // Metadata
  content: string;
  metadata?: Record<string, any>;
}

type NodeType = 'text' | 'file' | 'link' | 'group' | 'control';

/**
 * A differential operator represented by canvas edges
 * Edges become partial derivative operators: ∂/∂x, ∂/∂compile, etc.
 */
interface DifferentialOperator {
  symbol: string;           // e.g., "∂/∂compile", "∇", "Δ"
  order: number;            // 1 = first derivative, 2 = second derivative
  variables: string[];      // Which variables to differentiate
  direction?: [number, number]; // Direction vector for directional derivatives
}

/**
 * An edge connecting two polynomial nodes
 */
interface PolynomialEdge {
  id: string;
  from: string;
  to: string;
  operator: DifferentialOperator;
  label: string;
  metadata?: Record<string, any>;
}

/**
 * The complete canvas as a polynomial expression
 */
interface CanvasPolynomial {
  terms: Map<string, PolynomialTerm>;
  edges: Map<string, PolynomialEdge>;
  degree: number;  // Maximum degree of any term
  dimension: number; // Dimensional level (0D-7D)
}

// ============================================================================
// 2. NODE-TO-POLYNOMIAL ENCODING
// ============================================================================

class PolynomialEncoder {
  /**
   * Convert a canvas node to a polynomial term
   * The node's geometric properties become polynomial coefficients
   */
  encodeNode(node: any): PolynomialTerm {
    const contentHash = this.hashString(node.content || "");
    const typeValue = this.encodeType(node.type);
    
    // Compute polynomial degree based on content complexity
    const degree = this.computeDegree(node);
    
    // Coefficients encode the polynomial: a₀ + a₁x + a₂y + a₃w + a₄h + ...
    const coefficients = [
      contentHash % 1000,           // a₀: constant (content hash)
      node.x / 1000,                // a₁: x coefficient (normalized)
      node.y / 1000,                // a₂: y coefficient  
      node.width / 500,             // a₃: w coefficient
      node.height / 500,            // a₄: h coefficient
      parseInt(node.color || "1"),  // a₅: c coefficient (color 1-8)
      typeValue,                    // a₆: t coefficient (type encoding)
      contentHash % 100             // a₇: id coefficient
    ];
    
    return {
      x: node.x,
      y: node.y,
      w: node.width,
      h: node.height,
      c: parseInt(node.color || "1") % 8,
      t: node.type as NodeType,
      id: node.id,
      degree,
      coefficients,
      content: node.content || "",
      metadata: node.metadata
    };
  }
  
  /**
   * Compute polynomial degree based on node properties
   * Degree 0-7 maps to dimensional levels 0D-7D
   */
  private computeDegree(node: any): number {
    const content = node.content || "";
    
    // Control nodes (zero polynomial)
    if (content.includes("#Zero") || content.includes("#Control")) {
      return 0;
    }
    
    // Check for dimensional markers
    if (content.includes("0D") || content.includes("Quantum Vacuum")) return 0;
    if (content.includes("1D") || content.includes("Temporal")) return 1;
    if (content.includes("2D") || content.includes("Bipartite")) return 2;
    if (content.includes("3D") || content.includes("Algebraic")) return 3;
    if (content.includes("4D") || content.includes("Network")) return 4;
    if (content.includes("5D") || content.includes("Consensus")) return 5;
    if (content.includes("6D") || content.includes("Intelligence")) return 6;
    if (content.includes("7D") || content.includes("Quantum")) return 7;
    
    // Otherwise compute from content complexity
    const lines = content.split('\n').length;
    const complexity = Math.min(7, Math.floor(Math.log2(lines + 1)));
    
    return complexity;
  }
  
  private encodeType(type: string): number {
    // Prime encoding for node types
    const primes = { text: 2, file: 3, link: 5, group: 7, control: 11 };
    return primes[type as keyof typeof primes] || 2;
  }
  
  private hashString(str: string): number {
    let hash = 0;
    for (let i = 0; i < str.length; i++) {
      hash = ((hash << 5) - hash) + str.charCodeAt(i);
      hash |= 0;
    }
    return Math.abs(hash);
  }
}

// ============================================================================
// 3. EDGE-TO-OPERATOR ENCODING
// ============================================================================

class OperatorEncoder {
  /**
   * Convert a canvas edge to a differential operator
   */
  encodeEdge(edge: any): PolynomialEdge {
    const operator = this.labelToOperator(edge.label || "");
    
    return {
      id: edge.id,
      from: edge.fromNode,
      to: edge.toNode,
      operator,
      label: edge.label || "",
      metadata: edge.metadata
    };
  }
  
  /**
   * Map edge labels to mathematical operators
   */
  private labelToOperator(label: string): DifferentialOperator {
    const lowerLabel = label.toLowerCase();
    
    // Compilation/transformation operators
    if (lowerLabel.includes('compile') || lowerLabel.includes('→')) {
      return {
        symbol: '∂/∂compile',
        order: 1,
        variables: ['x', 'y', 'w', 'h']
      };
    }
    
    // Integration operators (ADD/accumulation)
    if (lowerLabel.includes('integrate') || lowerLabel.includes('+')) {
      return {
        symbol: '∫',
        order: -1,  // Negative order = integration
        variables: ['x', 'y']
      };
    }
    
    // Dependency operators
    if (lowerLabel.includes('depends') || lowerLabel.includes('uses')) {
      return {
        symbol: '∂/∂dependency',
        order: 1,
        variables: ['id']
      };
    }
    
    // Testing/verification operators (Laplacian)
    if (lowerLabel.includes('test') || lowerLabel.includes('verify')) {
      return {
        symbol: 'Δ',
        order: 2,
        variables: ['x', 'y']
      };
    }
    
    // Flow/propagation operators (gradient)
    if (lowerLabel.includes('flow') || lowerLabel.includes('propagate')) {
      return {
        symbol: '∇',
        order: 1,
        variables: ['x', 'y']
      };
    }
    
    // Default: directional derivative
    return {
      symbol: '∂/∂connection',
      order: 1,
      variables: ['x', 'y'],
      direction: [1, 0]  // Default: rightward
    };
  }
}

// ============================================================================
// 4. POLYNOMIAL ALGEBRA OPERATIONS
// ============================================================================

class PolynomialAlgebra {
  /**
   * Add two polynomial terms (node combination/grouping)
   * N₁ ⊕ N₂ = Combined node
   */
  add(p1: PolynomialTerm, p2: PolynomialTerm): PolynomialTerm {
    const newCoeffs = p1.coefficients.map((c, i) => c + p2.coefficients[i]);
    
    return {
      x: (p1.x + p2.x) / 2,  // Centroid
      y: (p1.y + p2.y) / 2,
      w: Math.max(p1.w, p2.w),
      h: Math.max(p1.h, p2.h),
      c: (p1.c + p2.c) % 8,
      t: 'group',
      id: `${p1.id}+${p2.id}`,
      degree: Math.max(p1.degree, p2.degree),
      coefficients: newCoeffs,
      content: `Group: ${p1.content} + ${p2.content}`,
      metadata: { operation: 'addition', sources: [p1.id, p2.id] }
    };
  }
  
  /**
   * Multiply two polynomial terms (composition/connection)
   * N₁ ⊗ N₂ = Connected nodes
   */
  multiply(p1: PolynomialTerm, p2: PolynomialTerm): PolynomialTerm {
    // Polynomial multiplication: convolve coefficients
    const newCoeffs = this.convolveCoefficients(p1.coefficients, p2.coefficients);
    
    return {
      x: p2.x,  // Result at target position
      y: p2.y,
      w: (p1.w + p2.w) / 2,
      h: (p1.h + p2.h) / 2,
      c: (p1.c * p2.c) % 8,
      t: p2.t,
      id: `${p1.id}×${p2.id}`,
      degree: p1.degree + p2.degree,  // Degree of product = sum of degrees
      coefficients: newCoeffs,
      content: `Composition: ${p1.content} → ${p2.content}`,
      metadata: { operation: 'multiplication', sources: [p1.id, p2.id] }
    };
  }
  
  /**
   * Apply differential operator (edge transformation)
   * ∂P/∂x = Transformed polynomial
   */
  differentiate(p: PolynomialTerm, operator: DifferentialOperator): PolynomialTerm {
    const newCoeffs = [...p.coefficients];
    
    // Apply differentiation rules based on operator
    if (operator.order === 1) {
      // First derivative: shift coefficients
      for (let i = 0; i < operator.variables.length; i++) {
        const varIdx = this.getVariableIndex(operator.variables[i]);
        if (varIdx >= 0 && varIdx < newCoeffs.length) {
          newCoeffs[varIdx] = newCoeffs[varIdx] * (varIdx + 1);
        }
      }
    }
    
    return {
      ...p,
      coefficients: newCoeffs,
      degree: Math.max(0, p.degree - 1),
      metadata: { 
        ...p.metadata, 
        operation: 'differentiation',
        operator: operator.symbol 
      }
    };
  }
  
  /**
   * Evaluate polynomial at a specific point
   * P(x₀, y₀, ...) = value
   */
  evaluate(p: PolynomialTerm, point: Partial<PolynomialTerm>): number {
    const [a0, a1, a2, a3, a4, a5, a6, a7] = p.coefficients;
    const x = point.x ?? p.x;
    const y = point.y ?? p.y;
    const w = point.w ?? p.w;
    const h = point.h ?? p.h;
    const c = point.c ?? p.c;
    const t = this.encodeTypeValue(point.t ?? p.t);
    
    return a0 + a1*x + a2*y + a3*w + a4*h + a5*c + a6*t + a7;
  }
  
  private convolveCoefficients(c1: number[], c2: number[]): number[] {
    const result = new Array(Math.min(c1.length, c2.length)).fill(0);
    for (let i = 0; i < result.length; i++) {
      result[i] = c1[i] * c2[i];
    }
    return result;
  }
  
  private getVariableIndex(variable: string): number {
    const indices: Record<string, number> = {
      'constant': 0, 'x': 1, 'y': 2, 'w': 3, 'h': 4, 'c': 5, 't': 6, 'id': 7
    };
    return indices[variable] ?? -1;
  }
  
  private encodeTypeValue(type: NodeType): number {
    return { text: 2, file: 3, link: 5, group: 7, control: 11 }[type] || 2;
  }
}

// ============================================================================
// 5. CANVAS POLYNOMIAL COMPILER
// ============================================================================

class CanvasPolynomialCompiler {
  private encoder = new PolynomialEncoder();
  private opEncoder = new OperatorEncoder();
  private algebra = new PolynomialAlgebra();
  
  /**
   * Parse canvas JSON into polynomial representation
   */
  parseCanvas(canvasJSON: any): CanvasPolynomial {
    const terms = new Map<string, PolynomialTerm>();
    const edges = new Map<string, PolynomialEdge>();
    let maxDegree = 0;
    
    // Encode all nodes as polynomial terms
    for (const [id, node] of Object.entries(canvasJSON.nodes || {})) {
      const term = this.encoder.encodeNode({ ...node as any, id });
      terms.set(id, term);
      maxDegree = Math.max(maxDegree, term.degree);
    }
    
    // Encode all edges as differential operators
    for (const [id, edge] of Object.entries(canvasJSON.edges || {})) {
      const polyEdge = this.opEncoder.encodeEdge({ ...edge as any, id });
      edges.set(id, polyEdge);
    }
    
    return {
      terms,
      edges,
      degree: maxDegree,
      dimension: maxDegree  // Degree maps to dimensional level
    };
  }
  
  /**
   * Compile canvas to executable expression tree
   */
  compile(canvasPoly: CanvasPolynomial): ExpressionTree {
    // Find root nodes (no incoming edges)
    const roots = this.findRootNodes(canvasPoly);
    
    // Build expression tree from each root
    const trees = roots.map(rootId => 
      this.buildExpressionTree(rootId, canvasPoly, new Set())
    );
    
    return {
      roots: trees,
      polynomial: canvasPoly
    };
  }
  
  /**
   * Build expression tree recursively following edges
   */
  private buildExpressionTree(
    nodeId: string, 
    canvas: CanvasPolynomial,
    visited: Set<string>
  ): ExpressionNode {
    if (visited.has(nodeId)) {
      return { type: 'reference', nodeId };
    }
    
    visited.add(nodeId);
    const term = canvas.terms.get(nodeId)!;
    const outgoingEdges = Array.from(canvas.edges.values())
      .filter(e => e.from === nodeId);
    
    if (outgoingEdges.length === 0) {
      return { type: 'leaf', term, nodeId };
    }
    
    const children = outgoingEdges.map(edge => ({
      operator: edge.operator,
      child: this.buildExpressionTree(edge.to, canvas, visited)
    }));
    
    return {
      type: 'operator',
      term,
      nodeId,
      children
    };
  }
  
  private findRootNodes(canvas: CanvasPolynomial): string[] {
    const hasIncoming = new Set<string>();
    for (const edge of canvas.edges.values()) {
      hasIncoming.add(edge.to);
    }
    
    return Array.from(canvas.terms.keys())
      .filter(id => !hasIncoming.has(id));
  }
}

// ============================================================================
// 6. SUPPORTING TYPES
// ============================================================================

interface ExpressionTree {
  roots: ExpressionNode[];
  polynomial: CanvasPolynomial;
}

type ExpressionNode = 
  | { type: 'leaf'; term: PolynomialTerm; nodeId: string }
  | { type: 'operator'; term: PolynomialTerm; nodeId: string; 
      children: Array<{ operator: DifferentialOperator; child: ExpressionNode }> }
  | { type: 'reference'; nodeId: string };

// ============================================================================
// 7. EXAMPLE USAGE
// ============================================================================

// Example: Compile a canvas
const compiler = new CanvasPolynomialCompiler();
const algebra = new PolynomialAlgebra();

// Parse canvas from JSON
const canvasPoly = compiler.parseCanvas({
  nodes: {
    "n1": { x: 100, y: 100, width: 300, height: 150, type: "text", 
            content: "#Activate: main", color: "1" },
    "n2": { x: 500, y: 100, width: 300, height: 150, type: "text",
            content: "#Integrate: x y", color: "2" },
    "n3": { x: 900, y: 100, width: 300, height: 150, type: "text",
            content: "#Store: result", color: "3" }
  },
  edges: {
    "e1": { fromNode: "n1", toNode: "n2", label: "compiles to" },
    "e2": { fromNode: "n2", toNode: "n3", label: "stores to" }
  }
});

console.log("Canvas Polynomial:", {
  termCount: canvasPoly.terms.size,
  edgeCount: canvasPoly.edges.size,
  degree: canvasPoly.degree,
  dimension: canvasPoly.dimension
});

// Compile to expression tree
const expression = compiler.compile(canvasPoly);
console.log("Expression tree compiled with", expression.roots.length, "root(s)");

export {
  PolynomialEncoder,
  OperatorEncoder,
  PolynomialAlgebra,
  CanvasPolynomialCompiler,
  type PolynomialTerm,
  type PolynomialEdge,
  type CanvasPolynomial
};