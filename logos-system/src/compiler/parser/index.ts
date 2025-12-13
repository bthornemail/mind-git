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

import { CanvasJSON, Node, Edge } from '../../json.canvas';
import { AALInstruction, AALProgram, AssemblyOp, Dimension } from '../core/aal';
import { Polynomial } from '../core/polynomial';

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
    return canvas.nodes.map((node, index) => {
      const position = this.extractPosition(node);
      const size = this.extractSize(node);
      const content = this.extractContent(node);
      const classification = this.classifyNode(node, content, position);
      const polynomial = this.encodeNode(node, position, content, classification);
      const dimension = this.calculateNodeDimension(classification, position, polynomial);
      
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
        operands: [],
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
      canvas.edges.forEach((edge, index) => {
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
    let observer = nodes[0];
    let min_distance = origin_distance(observer);
    
    for (const node of nodes) {
      const distance = origin_distance(node);
      if (distance < min_distance) {
        observer = node;
        min_distance = distance;
      }
    }
    
    // Check if it's close enough to be considered observer (within 10 pixels)
    if (min_distance < 10) {
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
   * Classify node type based on content and position
   */
  private classifyNode(node: any, content: string, position: { x: number; y: number }): NodeClassification {
    // Classification based on content prefixes
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
    
    // Classification based on node type
    switch (node.type) {
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
   * Calculate node dimension based on classification and properties
   */
  private calculateNodeDimension(
    classification: NodeClassification, 
    position: { x: number; y: number },
    polynomial: Polynomial
  ): Dimension {
    // Base dimension based on classification
    const dimension_map = {
      [NodeClassification.ACTIVATE]: Dimension.D0_PureAlgebra,
      [NodeClassification.INTEGRATE]: Dimension.D1_Functional,
      [NodeClassification.PROPAGATE]: Dimension.D2_Environment,
      [NodeClassification.BACKPROPAGATE]: Dimension.D3_MemoryModel,
      [NodeClassification.TRANSFORM]: Dimension.D4_ControlStack,
      [NodeClassification.VERIFY]: Dimension.D5_Concurrency,
      [NodeClassification.STORE]: Dimension.D6_Privileged,
      [NodeClassification.OBSERVE]: Dimension.D7_Timing,
      [NodeClassification.DATA]: Dimension.D0_PureAlgebra,
      [NodeClassification.UNKNOWN]: Dimension.D0_PureAlgebra
    };
    
    let base_dimension = dimension_map[classification] || Dimension.D0_PureAlgebra;
    
    // Elevate dimension based on polynomial degree (self-reference depth)
    const degree = this.calculateDegree(polynomial);
    if (degree > 7) {
      base_dimension = Dimension.D8_Probabilistic;
    } else if (degree > 3) {
      base_dimension = Math.max(base_dimension, Dimension.D4_ControlStack);
    }
    
    // Elevate based on distance from origin (higher dimensions at edges)
    const distance_from_origin = Math.sqrt(position.x * position.x + position.y * position.y);
    if (distance_from_origin > 500) {
      base_dimension = Math.max(base_dimension, Dimension.D9_ProjectiveGeometry);
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
  private checkHopfCompatibility(nodes: CanvasNode[], edges: CanvasEdge[]): boolean {
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