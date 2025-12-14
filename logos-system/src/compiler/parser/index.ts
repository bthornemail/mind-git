/**
 * Canvas JSON Parser for CanvasL Visual Compiler
 * 
 * This parser extracts mathematical structure from canvas diagrams
 * and converts them into AAL (Assembly-Algebra Language) programs.
 * 
 * Key principles:
 * - Spatial arrangement encodes mathematical relationships
 * - Observer node at (0,0) is the identity element
 * - Node positions determine polynomial degrees
 * - Edges represent data flow and dependencies
 */

import type { CanvasJSON, Node, Edge } from '../../json.canvas';
import { AssemblyOp, Dimension } from '../../core/aal';
import { Polynomial } from '../../core/polynomial';

/**
 * Parsed Canvas Structure
 */
export interface ParsedCanvas {
  nodes: CanvasNode[];
  edges: CanvasEdge[];
  observer: CanvasNode | null;
  metadata: CanvasMetadata;
}

export interface CanvasNode {
  id: string;
  type: string;
  position: { x: number; y: number };
  size: { width: number; height: number };
  content: string;
  classification: NodeClassification;
  polynomial: Polynomial;
  dimension: Dimension;
  degree: number;
  operands: string[];
  dependencies: string[];
  dependents: string[];
}

export interface CanvasEdge {
  id: string;
  from: string;
  to: string;
  type: EdgeType;
  weight: number;
  polynomial: Polynomial;
}

export interface CanvasMetadata {
  total_nodes: number;
  total_edges: number;
  max_degree: number;
  observer_present: boolean;
  canvas_bounds: { min_x: number; min_y: number; max_x: number; max_y: number };
  node_types: { [key: string]: number };
  dimensional_analysis: DimensionalAnalysis;
}

export interface DimensionalAnalysis {
  max_dimension: Dimension;
  dimension_distribution: { [key in Dimension]: number };
  complexity_score: number;
  hopf_compatibility: boolean;
}

export enum NodeClassification {
  ACTIVATE = 'activate',
  INTEGRATE = 'integrate',
  PROPAGATE = 'propagate',
  BACKPROPAGATE = 'backpropagate',
  TRANSFORM = 'transform',
  VERIFY = 'verify',
  STORE = 'store',
  OBSERVE = 'observe',
  DATA = 'data',
  LOOP = 'loop',
  CONDITION = 'condition',
  FUNCTION = 'function',
  CALL = 'call',
  RETURN = 'return',
  PARAMETER = 'parameter',
  VARIABLE = 'variable',
  CONSTANT = 'constant',
  UNKNOWN = 'unknown'
}

export enum EdgeType {
  DATA_FLOW = 'data_flow',
  CONTROL_FLOW = 'control_flow',
  DEPENDENCY = 'dependency',
  FEEDBACK = 'feedback',
  ENTANGLEMENT = 'entanglement'
}

/**
 * Canvas Parser - Extracts mathematical structure from visual diagrams
 */
export class CanvasParser {
  
  /**
   * Parse complete canvas JSON
   */
  parseCanvas(canvas: CanvasJSON): ParsedCanvas {
    const nodes = this.extractNodes(canvas);
    const edges = this.extractEdges(canvas);
    const observer = this.findObserverNode(nodes);
    const metadata = this.analyzeCanvas(nodes, edges, observer);
    
    return {
      nodes,
      edges,
      observer,
      metadata
    };
  }
  
  /**
   * Extract nodes from canvas JSON
   */
  private extractNodes(canvas: CanvasJSON): CanvasNode[] {
    return canvas.nodes.map((node: any, index: number) => {
      const position = this.extractPosition(node);
      const size = this.extractSize(node);
      const content = this.extractContent(node);
      const classification = this.classifyNode(node, content, position);
      const polynomial = this.encodeNode(node, position, content, classification);
      const dimension = this.calculateNodeDimension(classification, position, polynomial);
      
      const operands = this.extractOperands(content, classification);
      
      return {
        id: node.id || `node_${index}`,
        type: node.type || 'unknown',
        position,
        size,
        content,
        classification,
        polynomial,
        dimension,
        degree: this.calculateDegree(polynomial),
        operands,
        dependencies: [],
        dependents: []
      };
    });
  }
  
  /**
   * Extract edges from canvas JSON
   */
  private extractEdges(canvas: CanvasJSON): CanvasEdge[] {
    const edges: CanvasEdge[] = [];
    
    if (canvas.edges) {
      canvas.edges.forEach((edge: any, index: number) => {
        const edge_type = this.classifyEdge(edge);
        const weight = this.calculateEdgeWeight(edge);
        const polynomial = this.encodeEdge(edge, edge_type, weight);
        
        edges.push({
          id: edge.id || `edge_${index}`,
          from: edge.fromNode || edge.from || '',
          to: edge.toNode || edge.to || '',
          type: edge_type,
          weight,
          polynomial
        });
      });
    }
    
    return edges;
  }
  
  /**
   * Find observer node (identity element at origin)
   */
  private findObserverNode(nodes: CanvasNode[]): CanvasNode | null {
    // Observer is at or closest to (0,0) origin
    const origin_distance = (node: CanvasNode) => 
      Math.sqrt(node.position.x * node.position.x + node.position.y * node.position.y);
    
    if (nodes.length === 0) return null;
    
    // Find node closest to origin
    let observer = nodes[0] || null;
    let min_distance = observer ? origin_distance(observer) : Infinity;
    
    for (const node of nodes) {
      const distance = origin_distance(node);
      if (distance < min_distance) {
        observer = node;
        min_distance = distance;
      }
    }
    
    // Check if it's close enough to be considered observer (within 10 pixels)
    if (min_distance < 10 && observer) {
      return observer;
    }
    
    return null;
  }
  
  /**
   * Extract node position
   */
  private extractPosition(node: any): { x: number; y: number } {
    return {
      x: node.x || 0,
      y: node.y || 0
    };
  }
  
  /**
   * Extract node size
   */
  private extractSize(node: any): { width: number; height: number } {
    return {
      width: node.width || 100,
      height: node.height || 50
    };
  }
  
  /**
   * Extract node content
   */
  private extractContent(node: any): string {
    if (node.text) return node.text;
    if (node.file) return node.file;
    if (node.url) return node.url;
    if (node.label) return node.label;
    return '';
  }
  
  /**
   * Classify node type based on content and position with dynamic parsing
   */
  private classifyNode(_node: any, content: string, position: { x: number; y: number }): NodeClassification {
    // Classification based on explicit content prefixes
    if (content.startsWith('#Activate:') || content.startsWith('#activate:')) {
      return NodeClassification.ACTIVATE;
    }
    if (content.startsWith('#Integrate:') || content.startsWith('#integrate:')) {
      return NodeClassification.INTEGRATE;
    }
    if (content.startsWith('#Propagate:') || content.startsWith('#propagate:')) {
      return NodeClassification.PROPAGATE;
    }
    if (content.startsWith('#BackPropagate:') || content.startsWith('#backpropagate:')) {
      return NodeClassification.BACKPROPAGATE;
    }
    if (content.startsWith('#Transform:') || content.startsWith('#transform:')) {
      return NodeClassification.TRANSFORM;
    }
    if (content.startsWith('#Verify:') || content.startsWith('#verify:')) {
      return NodeClassification.VERIFY;
    }
    if (content.startsWith('#Store:') || content.startsWith('#store:')) {
      return NodeClassification.STORE;
    }
    if (content.startsWith('#Observe:') || content.startsWith('#observe:')) {
      return NodeClassification.OBSERVE;
    }
    
    // Dynamic classification based on content patterns
    const lowerContent = content.toLowerCase();
    
    // Loop detection
    if (this.isLoopNode(content, lowerContent)) {
      return NodeClassification.LOOP;
    }
    
    // Condition detection
    if (this.isConditionNode(content, lowerContent)) {
      return NodeClassification.CONDITION;
    }
    
    // Function detection
    if (this.isFunctionNode(content, lowerContent)) {
      return NodeClassification.FUNCTION;
    }
    
    // Function call detection
    if (this.isFunctionCallNode(content, lowerContent)) {
      return NodeClassification.CALL;
    }
    
    // Return statement detection
    if (this.isReturnNode(content, lowerContent)) {
      return NodeClassification.RETURN;
    }
    
    // Parameter detection
    if (this.isParameterNode(content, lowerContent)) {
      return NodeClassification.PARAMETER;
    }
    
    // Variable detection
    if (this.isVariableNode(content, lowerContent)) {
      return NodeClassification.VARIABLE;
    }
    
    // Constant detection
    if (this.isConstantNode(content, lowerContent)) {
      return NodeClassification.CONSTANT;
    }
    
    // Classification based on node type
    switch (_node.type) {
      case 'text':
        return NodeClassification.DATA;
      case 'file':
        return NodeClassification.INTEGRATE;
      case 'link':
        return NodeClassification.PROPAGATE;
      case 'group':
        return NodeClassification.TRANSFORM;
      default:
        return NodeClassification.UNKNOWN;
    }
  }
  
  /**
   * Extract operands from node content based on classification
   */
  private extractOperands(content: string, classification: NodeClassification): string[] {
    const operands: string[] = [];
    
    switch (classification) {
      case NodeClassification.FUNCTION:
        // Extract function name and parameters
        const funcMatch = content.match(/(?:function|const|let|var)\s+(\w+)\s*\(([^)]*)\)/);
        if (funcMatch) {
          operands.push(funcMatch[1]); // Function name
          const params = funcMatch[2].split(',').map(p => p.trim()).filter(p => p);
          operands.push(...params);
        }
        break;
        
      case NodeClassification.CALL:
        // Extract function name and arguments
        const callMatch = content.match(/(\w+(?:\.\w+)*)\s*\(([^)]*)\)/);
        if (callMatch) {
          operands.push(callMatch[1]); // Function name
          const args = callMatch[2].split(',').map(a => a.trim()).filter(a => a);
          operands.push(...args);
        }
        break;
        
      case NodeClassification.CONDITION:
        // Extract variables in condition
        const conditionVars = content.match(/\b[a-zA-Z_$][a-zA-Z0-9_$]*\b/g);
        if (conditionVars) {
          operands.push(...conditionVars.filter(v => !['if', 'else', 'switch', 'case', 'when'].includes(v)));
        }
        break;
        
      case NodeClassification.VARIABLE:
      case NodeClassification.CONSTANT:
        // Extract variable name and value
        const varMatch = content.match(/(?:let|const|var)\s+([a-zA-Z_$][a-zA-Z0-9_$]*)\s*=\s*([^;]+)/);
        if (varMatch) {
          operands.push(varMatch[1]); // Variable name
          // Extract variables from the right side
          const rightSideVars = varMatch[2].match(/\b[a-zA-Z_$][a-zA-Z0-9_$]*\b/g);
          if (rightSideVars) {
            operands.push(...rightSideVars);
          }
        }
        break;
        
      case NodeClassification.LOOP:
        // Extract loop variable and condition
        const loopMatch = content.match(/(?:for|while)\s*\(([^)]+)\)/);
        if (loopMatch) {
          const loopVars = loopMatch[1].match(/\b[a-zA-Z_$][a-zA-Z0-9_$]*\b/g);
          if (loopVars) {
            operands.push(...loopVars.filter(v => !['for', 'while', 'in', 'of'].includes(v)));
          }
        }
        break;
        
      case NodeClassification.RETURN:
        // Extract return value variables
        const returnMatch = content.match(/return\s+([^;]+)/);
        if (returnMatch) {
          const returnVars = returnMatch[1].match(/\b[a-zA-Z_$][a-zA-Z0-9_$]*\b/g);
          if (returnVars) {
            operands.push(...returnVars);
          }
        }
        break;
        
      default:
        // For other types, extract any identifiers
        const identifiers = content.match(/\b[a-zA-Z_$][a-zA-Z0-9_$]*\b/g);
        if (identifiers) {
          operands.push(...identifiers);
        }
        break;
    }
    
    // Remove duplicates and filter out common keywords
    const keywords = new Set([
      'function', 'const', 'let', 'var', 'if', 'else', 'switch', 'case', 'when',
      'for', 'while', 'do', 'break', 'continue', 'return', 'yield', 'true', 'false',
      'null', 'undefined', 'this', 'new', 'typeof', 'instanceof', 'in', 'of'
    ]);
    
    return [...new Set(operands)].filter(operand => !keywords.has(operand));
  }

  /**
   * Dynamic node type detection methods
   */
  private isLoopNode(content: string, lowerContent: string): boolean {
    const loopPatterns = [
      /for\s*\(/,
      /while\s*\(/,
      /do\s*{/,
      /loop/i,
      /iteration/i,
      /repeat/i
    ];
    
    return loopPatterns.some(pattern => pattern.test(content)) ||
           lowerContent.includes('for loop') ||
           lowerContent.includes('while loop') ||
           lowerContent.includes('iteration');
  }
  
  private isConditionNode(content: string, lowerContent: string): boolean {
    const conditionPatterns = [
      /if\s*\(/,
      /else\s*if\s*\(/,
      /else\s*{/,
      /switch\s*\(/,
      /case\s+/,
      /condition/i,
      /when\s+/i
    ];
    
    return conditionPatterns.some(pattern => pattern.test(content)) ||
           lowerContent.includes('if condition') ||
           lowerContent.includes('conditional') ||
           (lowerContent.includes('<') || lowerContent.includes('>') || 
            lowerContent.includes('==') || lowerContent.includes('!=') ||
            lowerContent.includes('<=') || lowerContent.includes('>='));
  }
  
  private isFunctionNode(content: string, lowerContent: string): boolean {
    const functionPatterns = [
      /function\s+\w+\s*\(/,
      /const\s+\w+\s*=\s*\(/,
      /let\s+\w+\s*=\s*\(/,
      /var\s+\w+\s*=\s*\(/,
      /\w+\s*:\s*\(/,
      /def\s+\w+/,
      /func\s+\w+/
    ];
    
    return functionPatterns.some(pattern => pattern.test(content)) ||
           lowerContent.includes('function definition') ||
           lowerContent.includes('method definition') ||
           lowerContent.startsWith('function ');
  }
  
  private isFunctionCallNode(content: string, lowerContent: string): boolean {
    const callPatterns = [
      /\w+\s*\([^)]*\)\s*;/,
      /\w+\.\w+\s*\([^)]*\)/,
      /\w+\s*\([^)]*\)\s*$/,
      /console\.\w+/,
      /print\s*\(/,
      /log\s*\(/
    ];
    
    return callPatterns.some(pattern => pattern.test(content)) ||
           lowerContent.includes('call ') ||
           lowerContent.includes('invoke ') ||
           (lowerContent.includes('(') && lowerContent.includes(')') && 
            !this.isFunctionNode(content, lowerContent));
  }
  
  private isReturnNode(content: string, lowerContent: string): boolean {
    const returnPatterns = [
      /return\s+/,
      /yield\s+/,
      /break\s*;/,
      /continue\s*;/
    ];
    
    return returnPatterns.some(pattern => pattern.test(content)) ||
           lowerContent.startsWith('return ') ||
           lowerContent.startsWith('yield ');
  }
  
  private isParameterNode(content: string, lowerContent: string): boolean {
    const parameterPatterns = [
      /parameter\s+/i,
      /param\s+/i,
      /arg\s+/i,
      /argument\s+/i
    ];
    
    return parameterPatterns.some(pattern => pattern.test(content)) ||
           lowerContent.includes('parameter') ||
           lowerContent.includes('param ') ||
           lowerContent.includes('argument ');
  }
  
  private isVariableNode(content: string, lowerContent: string): boolean {
    const variablePatterns = [
      /[a-zA-Z_$][a-zA-Z0-9_$]*\s*=\s*[^=]/,
      /let\s+[a-zA-Z_$]/,
      /const\s+[a-zA-Z_$]/,
      /var\s+[a-zA-Z_$]/,
      /[a-zA-Z_$][a-zA-Z0-9_$]*\s*:\s*string/,
      /[a-zA-Z_$][a-zA-Z0-9_$]*\s*:\s*number/
    ];
    
    return variablePatterns.some(pattern => pattern.test(content)) ||
           lowerContent.includes('variable ') ||
           lowerContent.includes('var ') ||
           (lowerContent.includes('=') && !this.isConstantNode(content, lowerContent));
  }
  
  private isConstantNode(content: string, lowerContent: string): boolean {
    const constantPatterns = [
      /const\s+[a-zA-Z_$][a-zA-Z0-9_$]*\s*=\s*["'`\d]/,
      /#define\s+/,
      /final\s+/,
      /readonly\s+/
    ];
    
    return constantPatterns.some(pattern => pattern.test(content)) ||
           lowerContent.includes('constant ') ||
           (lowerContent.includes('const ') && 
            (lowerContent.includes('"') || lowerContent.includes("'") || 
             /\d/.test(lowerContent)));
  }
  
  /**
   * Calculate node dimension based on classification and properties with dynamic mapping
   */
  private calculateNodeDimension(
    classification: NodeClassification, 
    position: { x: number; y: number },
    polynomial: Polynomial
  ): Dimension {
    // Base dimension based on classification with extended mapping
    const dimension_map = {
      [NodeClassification.ACTIVATE]: Dimension.D0_PureAlgebra,
      [NodeClassification.INTEGRATE]: Dimension.D1_Functional,
      [NodeClassification.PROPAGATE]: Dimension.D2_Environment,
      [NodeClassification.BACKPROPAGATE]: Dimension.D3_MemoryModel,
      [NodeClassification.TRANSFORM]: Dimension.D4_ControlStack,
      [NodeClassification.VERIFY]: Dimension.D5_Concurrency,
      [NodeClassification.STORE]: Dimension.D6_Privileged,
      [NodeClassification.OBSERVE]: Dimension.D7_Timing,
      [NodeClassification.LOOP]: Dimension.D5_Concurrency, // Loops involve concurrency
      [NodeClassification.CONDITION]: Dimension.D3_MemoryModel, // Conditions affect memory flow
      [NodeClassification.FUNCTION]: Dimension.D4_ControlStack, // Functions use call stack
      [NodeClassification.CALL]: Dimension.D4_ControlStack, // Function calls use stack
      [NodeClassification.RETURN]: Dimension.D3_MemoryModel, // Returns affect memory
      [NodeClassification.PARAMETER]: Dimension.D1_Functional, // Parameters are functional
      [NodeClassification.VARIABLE]: Dimension.D1_Functional, // Variables are functional
      [NodeClassification.CONSTANT]: Dimension.D0_PureAlgebra, // Constants are pure
      [NodeClassification.DATA]: Dimension.D0_PureAlgebra,
      [NodeClassification.UNKNOWN]: Dimension.D0_PureAlgebra
    };
    
    let base_dimension = dimension_map[classification] || Dimension.D0_PureAlgebra;
    
    // Dynamic dimension elevation based on node complexity
    const degree = this.calculateDegree(polynomial);
    
    // Elevate based on polynomial degree (self-reference depth)
    if (degree > 15) {
      base_dimension = Dimension.D10_Physical; // Maximum complexity
    } else if (degree > 10) {
      base_dimension = Dimension.D9_ProjectiveGeometry; // High complexity
    } else if (degree > 7) {
      base_dimension = Dimension.D8_Probabilistic; // Medium-high complexity
    } else if (degree > 5) {
      base_dimension = Math.max(base_dimension, Dimension.D6_Privileged); // Medium complexity
    } else if (degree > 3) {
      base_dimension = Math.max(base_dimension, Dimension.D4_ControlStack); // Low-medium complexity
    }
    
    // Special handling for complex control structures
    if (classification === NodeClassification.LOOP || classification === NodeClassification.CONDITION) {
      base_dimension = Math.max(base_dimension, Dimension.D5_Concurrency);
    }
    
    // Special handling for functions
    if (classification === NodeClassification.FUNCTION || classification === NodeClassification.CALL) {
      base_dimension = Math.max(base_dimension, Dimension.D4_ControlStack);
    }
    
    // Elevate based on distance from origin (higher dimensions at edges)
    const distance_from_origin = Math.sqrt(position.x * position.x + position.y * position.y);
    if (distance_from_origin > 1000) {
      base_dimension = Math.max(base_dimension, Dimension.D9_ProjectiveGeometry);
    } else if (distance_from_origin > 500) {
      base_dimension = Math.max(base_dimension, Dimension.D8_Probabilistic);
    }
    
    return Math.min(base_dimension, Dimension.D10_Physical);
  }
  
  /**
   * Encode node as polynomial over F₂
   */
  private encodeNode(
    node: any, 
    position: { x: number; y: number },
    content: string,
    classification: NodeClassification
  ): Polynomial {
    // Encode position (x, y) as polynomial coefficients
    const x_bits = this.numberToBits(Math.abs(position.x), 16);
    const y_bits = this.numberToBits(Math.abs(position.y), 16);
    
    // Encode content as polynomial coefficients
    const content_bits = this.stringToBits(content.substring(0, 32));
    
    // Encode classification as polynomial coefficients
    const classification_bits = this.numberToBits(Object.values(NodeClassification).indexOf(classification), 4);
    
    // Encode node type as polynomial coefficients
    const type_bits = this.stringToBits((node.type || 'unknown').substring(0, 8));
    
    // Combine all encodings
    return [...x_bits, ...y_bits, ...content_bits, ...classification_bits, ...type_bits];
  }
  
  /**
   * Classify edge type
   */
  private classifyEdge(edge: any): EdgeType {
    const label = (edge.label || '').toLowerCase();
    
    if (label.includes('data') || label.includes('flow')) {
      return EdgeType.DATA_FLOW;
    }
    if (label.includes('control') || label.includes('jump')) {
      return EdgeType.CONTROL_FLOW;
    }
    if (label.includes('dependency') || label.includes('depends')) {
      return EdgeType.DEPENDENCY;
    }
    if (label.includes('feedback') || label.includes('loop')) {
      return EdgeType.FEEDBACK;
    }
    if (label.includes('entangle') || label.includes('quantum')) {
      return EdgeType.ENTANGLEMENT;
    }
    
    // Default to data flow
    return EdgeType.DATA_FLOW;
  }
  
  /**
   * Calculate edge weight
   */
  private calculateEdgeWeight(edge: any): number {
    // Weight based on edge properties
    let weight = 1.0;
    
    // Heavier weight for edges with labels
    if (edge.label) weight += 0.5;
    
    // Heavier weight for edges with colors
    if (edge.color) weight += 0.3;
    
    // Weight based on edge arrow type
    if (edge.arrow) {
      switch (edge.arrow) {
        case 'arrow': weight += 0.2; break;
        case 'circle': weight += 0.3; break;
        case 'diamond': weight += 0.4; break;
        case 'none': weight -= 0.1; break;
      }
    }
    
    return Math.max(0.1, Math.min(2.0, weight));
  }
  
  /**
   * Encode edge as polynomial
   */
  private encodeEdge(edge: any, edge_type: EdgeType, weight: number): Polynomial {
    // Encode edge type
    const type_bits = this.numberToBits(Object.values(EdgeType).indexOf(edge_type), 4);
    
    // Encode weight as fixed-point representation
    const weight_bits = this.numberToBits(Math.floor(weight * 100), 8);
    
    // Encode edge IDs
    const from_bits = this.stringToBits((edge.fromNode || edge.from || '').substring(0, 16));
    const to_bits = this.stringToBits((edge.toNode || edge.to || '').substring(0, 16));
    
    // Encode label
    const label_bits = this.stringToBits((edge.label || '').substring(0, 32));
    
    return [...type_bits, ...weight_bits, ...from_bits, ...to_bits, ...label_bits];
  }
  
  /**
   * Analyze canvas metadata and structure
   */
  private analyzeCanvas(
    nodes: CanvasNode[], 
    edges: CanvasEdge[], 
    observer: CanvasNode | null
  ): CanvasMetadata {
    // Basic statistics
    const total_nodes = nodes.length;
    const total_edges = edges.length;
    const max_degree = Math.max(...nodes.map(n => n.degree));
    const observer_present = observer !== null;
    
    // Canvas bounds
    const positions = nodes.map(n => n.position);
    const min_x = Math.min(...positions.map(p => p.x));
    const min_y = Math.min(...positions.map(p => p.y));
    const max_x = Math.max(...positions.map(p => p.x));
    const max_y = Math.max(...positions.map(p => p.y));
    
    // Node type distribution
    const node_types: { [key: string]: number } = {};
    nodes.forEach(node => {
      node_types[node.classification] = (node_types[node.classification] || 0) + 1;
    });
    
    // Dimensional analysis
    const dimensional_distribution = nodes.reduce((dist, node) => {
      dist[node.dimension] = (dist[node.dimension] || 0) + 1;
      return dist;
    }, {} as { [key in Dimension]: number });
    
    const max_dimension = Math.max(...Object.keys(dimensional_distribution).map(Number)) as Dimension;
    const complexity_score = this.calculateComplexityScore(nodes, edges);
    const hopf_compatibility = this.checkHopfCompatibility(nodes, edges);
    
    return {
      total_nodes,
      total_edges,
      max_degree,
      observer_present,
      canvas_bounds: { min_x, min_y, max_x, max_y },
      node_types,
      dimensional_analysis: {
        max_dimension,
        dimension_distribution: dimensional_distribution,
        complexity_score,
        hopf_compatibility
      }
    };
  }
  
  /**
   * Calculate canvas complexity score
   */
  private calculateComplexityScore(nodes: CanvasNode[], edges: CanvasEdge[]): number {
    // Complexity based on node count, edge count, and dimensional distribution
    const node_complexity = nodes.length * 10;
    const edge_complexity = edges.length * 15;
    const dimensional_complexity = nodes.reduce((sum, node) => sum + node.dimension * 5, 0);
    const degree_complexity = nodes.reduce((sum, node) => sum + node.degree * 2, 0);
    
    return node_complexity + edge_complexity + dimensional_complexity + degree_complexity;
  }
  
  /**
   * Check compatibility with Hopf fibrations
   */
  private checkHopfCompatibility(nodes: CanvasNode[], _edges: CanvasEdge[]): boolean {
    // Check if the canvas structure is compatible with Hopf fibrations
    // This is a simplified check - full verification would require topological analysis
    
    // Count nodes in valid Hopf dimensions (1, 2, 4, 8)
    const hopf_dimension_nodes = nodes.filter(node => 
      node.degree === 0 || node.degree === 1 || node.degree === 3 || node.degree === 7
    ).length;
    
    // At least 50% of nodes should be in Hopf-compatible dimensions
    return (hopf_dimension_nodes / nodes.length) >= 0.5;
  }
  
  /**
   * Helper functions for encoding/decoding
   */
  private calculateDegree(polynomial: Polynomial): number {
    // Find highest set bit
    for (let i = polynomial.length - 1; i >= 0; i--) {
      if (polynomial[i]) return i;
    }
    return 0;
  }
  
  private numberToBits(n: number, bits: number): Polynomial {
    const result: Polynomial = [];
    for (let i = 0; i < bits; i++) {
      result.push((n & (1 << i)) !== 0);
    }
    return result;
  }
  
  private stringToBits(s: string): Polynomial {
    const result: Polynomial = [];
    for (let i = 0; i < s.length; i++) {
      const char_code = s.charCodeAt(i);
      for (let j = 0; j < 8; j++) {
        result.push((char_code & (1 << j)) !== 0);
      }
    }
    return result;
  }
  
  /**
   * Build dependency graph from edges
   */
  buildDependencyGraph(canvas: ParsedCanvas): void {
    // Clear existing dependencies
    canvas.nodes.forEach(node => {
      node.dependencies = [];
      node.dependents = [];
    });
    
    // Build dependencies from edges
    canvas.edges.forEach(edge => {
      const from_node = canvas.nodes.find(n => n.id === edge.from);
      const to_node = canvas.nodes.find(n => n.id === edge.to);
      
      if (from_node && to_node) {
        from_node.dependents.push(to_node.id);
        to_node.dependencies.push(from_node.id);
      }
    });
  }
  
  /**
   * Detect cycles in dependency graph
   */
  detectCycles(canvas: ParsedCanvas): string[][] {
    const cycles: string[][] = [];
    const visited = new Set<string>();
    const recursion_stack = new Set<string>();
    
    const has_cycle = (node_id: string, path: string[]): boolean => {
      if (recursion_stack.has(node_id)) {
        // Found cycle
        const cycle_start = path.indexOf(node_id);
        if (cycle_start !== -1) {
          cycles.push([...path.slice(cycle_start), node_id]);
        }
        return true;
      }
      
      if (visited.has(node_id)) return false;
      
      visited.add(node_id);
      recursion_stack.add(node_id);
      
      const node = canvas.nodes.find(n => n.id === node_id);
      if (node) {
        for (const dependent_id of node.dependents) {
          if (has_cycle(dependent_id, [...path, node_id])) {
            return true;
          }
        }
      }
      
      recursion_stack.delete(node_id);
      return false;
    };
    
    canvas.nodes.forEach(node => {
      if (!visited.has(node.id)) {
        has_cycle(node.id, []);
      }
    });
    
    return cycles;
  }
  
  /**
   * Get topological order of nodes
   */
  getTopologicalOrder(canvas: ParsedCanvas): CanvasNode[] {
    const in_degree = new Map<string, number>();
    const queue: string[] = [];
    const result: CanvasNode[] = [];
    
    // Calculate in-degrees
    canvas.nodes.forEach(node => {
      in_degree.set(node.id, node.dependencies.length);
      if (node.dependencies.length === 0) {
        queue.push(node.id);
      }
    });
    
    // Topological sort
    while (queue.length > 0) {
      const current_id = queue.shift()!;
      const current_node = canvas.nodes.find(n => n.id === current_id);
      
      if (current_node) {
        result.push(current_node);
        
        // Update in-degrees of dependents
        current_node.dependents.forEach(dependent_id => {
          const current_in_degree = in_degree.get(dependent_id) || 0;
          const new_in_degree = current_in_degree - 1;
          in_degree.set(dependent_id, new_in_degree);
          
          if (new_in_degree === 0) {
            queue.push(dependent_id);
          }
        });
      }
    }
    
    return result;
  }
}