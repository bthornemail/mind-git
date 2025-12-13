/**
 * Abstract Syntax Tree Generator for CanvasL
 * 
 * This module transforms parsed canvas nodes into an Abstract Syntax Tree (AST)
 * that represents the mathematical structure and computational flow of the canvas.
 * 
 * The AST captures:
 * - Hierarchical structure of computations
 * - Data flow and dependencies
 * - Mathematical operations at each node
 * - Dimensional relationships
 * - Control flow patterns
 */

import { ParsedCanvas, CanvasNode, CanvasEdge, NodeClassification, EdgeType } from '../parser';
import { AALInstruction, AssemblyOp, Dimension } from '../../core/aal';
import { Polynomial } from '../../core/polynomial';

/**
 * AST Node Types
 */
export enum ASTNodeType {
  PROGRAM = 'program',
  FUNCTION = 'function',
  BLOCK = 'block',
  ASSIGNMENT = 'assignment',
  OPERATION = 'operation',
  CONDITIONAL = 'conditional',
  LOOP = 'loop',
  CALL = 'call',
  RETURN = 'return',
  JUMP = 'jump',
  DATA = 'data',
  OBSERVER = 'observer'
}

/**
 * AST Node Structure
 */
export interface ASTNode {
  id: string;
  type: ASTNodeType;
  children: ASTNode[];
  parent?: ASTNode;
  metadata: ASTNodeMetadata;
  aal_instruction?: AALInstruction;
  polynomial?: Polynomial;
}

export interface ASTNodeMetadata {
  source_node?: string;
  line_number?: number;
  dimension: Dimension;
  degree: number;
  position: { x: number; y: number };
  label?: string;
  comment?: string;
  execution_order?: number;
  complexity_score?: number;
  hopf_compatible?: boolean;
}

/**
 * Function Definition
 */
export interface FunctionDefinition {
  name: string;
  parameters: string[];
  return_type?: string;
  body: ASTNode[];
  local_variables: VariableDefinition[];
  assembly_template?: string;
  metadata: {
    entry_point?: boolean;
    exit_point?: boolean;
    observer_function?: boolean;
  };
}

/**
 * Variable Definition
 */
export interface VariableDefinition {
  name: string;
  type: string;
  scope: string;
  dimension: Dimension;
  polynomial?: Polynomial;
  initial_value?: any;
}

/**
 * Control Flow Structures
 */
export interface ConditionalNode {
  condition: ASTNode;
  then_branch: ASTNode;
  else_branch?: ASTNode;
}

export interface LoopNode {
  loop_type: 'while' | 'for' | 'do-while';
  condition?: ASTNode;
  initialization?: ASTNode;
  update?: ASTNode;
  body: ASTNode;
}

/**
 * Complete AST Structure
 */
export interface AST {
  nodes: ASTNode[];
  edges: ASTEdge[];
  functions: FunctionDefinition[];
  variables: VariableDefinition[];
  entry_points: string[];
  exit_points: string[];
  metadata: ASTMetadata;
}

export interface ASTEdge {
  from: string;
  to: string;
  type: EdgeType;
  weight: number;
  label?: string;
}

export interface ASTMetadata {
  total_nodes: number;
  total_edges: number;
  max_depth: number;
  complexity: number;
  contains_cycles: boolean;
  hopf_compatible: boolean;
  entry_points: string[];
  exit_points: string[];
  dimensions_used: Dimension[];
}

/**
 * AST Generator - Transforms canvas to Abstract Syntax Tree
 */
export class ASTGenerator {
  private variable_counter: number = 0;
  
  constructor(private canvas: ParsedCanvas) {}
  
  /**
   * Generate complete AST from parsed canvas
   */
  async generateAST(): Promise<AST> {
    // Build dependency graph
    const { CanvasParser } = await import('../parser');
    const parser = new CanvasParser();
    parser.buildDependencyGraph(this.canvas);
    
    // Check for cycles
    const cycles = parser.detectCycles(this.canvas);
    
    // Get topological order for execution
    const ordered_nodes = parser.getTopologicalOrder(this.canvas);
    
    // Generate functions from canvas structure
    const functions = this.extractFunctions(ordered_nodes);
    
    // Generate variables from data nodes
    const variables = this.extractVariables(ordered_nodes);
    
    // Generate AST nodes
    const ast_nodes = this.generateASTNodes(ordered_nodes, functions);
    
    // Generate AST edges
    const ast_edges = this.generateASTEdges(this.canvas.edges, ast_nodes);
    
    // Identify entry and exit points
    const entry_points = this.identifyEntryPoints(ast_nodes, functions);
    const exit_points = this.identifyExitPoints(ast_nodes, functions);
    
    // Calculate metadata
    const metadata = this.calculateASTMetadata(ast_nodes, ast_edges, cycles);
    
    return {
      nodes: ast_nodes,
      edges: ast_edges,
      functions,
      variables,
      entry_points,
      exit_points,
      metadata
    };
  }
  
  /**
   * Extract functions from canvas structure
   */
  private extractFunctions(ordered_nodes: CanvasNode[]): FunctionDefinition[] {
    const functions: FunctionDefinition[] = [];
    
    // Group nodes by spatial proximity and logical grouping
    const function_groups = this.groupNodesIntoFunctions(ordered_nodes);
    
    function_groups.forEach((group, index) => {
      const entry_node = group[0]!; // First node in group is entry point
      const exit_node = group[group.length - 1]!; // Last node is exit point
      
      const func: FunctionDefinition = {
        name: this.generateFunctionName(entry_node, index),
        parameters: this.extractParameters(group),
        return_type: this.inferReturnType(group),
        body: [], // Will be filled by generateASTNodes
        local_variables: this.extractLocalVariables(group),
        assembly_template: this.generateAssemblyTemplate(entry_node),
        metadata: {
          entry_point: this.isEntryPoint(entry_node),
          exit_point: this.isExitPoint(exit_node),
          observer_function: this.isObserverFunction(group)
        }
      };
      
      functions.push(func);
    });
    
    return functions;
  }
  
  /**
   * Extract variables from data nodes
   */
  private extractVariables(ordered_nodes: CanvasNode[]): VariableDefinition[] {
    const variables: VariableDefinition[] = [];
    
    ordered_nodes.forEach(node => {
      if (node.classification === NodeClassification.DATA || node.content) {
        const variable: VariableDefinition = {
          name: this.generateVariableName(node),
          type: this.inferVariableType(node),
          scope: 'global',
          dimension: node.dimension,
          polynomial: node.polynomial,
          initial_value: this.parseNodeContent(node.content)
        };
        
        variables.push(variable);
      }
    });
    
    return variables;
  }
  
  /**
   * Generate AST nodes from canvas nodes
   */
  private generateASTNodes(
    ordered_nodes: CanvasNode[], 
    functions: FunctionDefinition[]
  ): ASTNode[] {
    const ast_nodes: ASTNode[] = [];
    
    ordered_nodes.forEach((node, index) => {
      const ast_node = this.createASTNode(node, index, functions);
      ast_nodes.push(ast_node);
    });
    
    return ast_nodes;
  }
  
  /**
   * Create AST node from canvas node
   */
  private createASTNode(
    canvas_node: CanvasNode, 
    index: number, 
    _functions: FunctionDefinition[]
  ): ASTNode {
    const node_type = this.mapCanvasNodeToASTType(canvas_node);
    const children = this.createChildNodes(canvas_node);
    const aal_instruction = this.createAALInstruction(canvas_node);
    
    const ast_node: ASTNode = {
      id: this.generateNodeId(canvas_node),
      type: node_type,
      children,
      metadata: {
        source_node: canvas_node.id,
        line_number: index,
        dimension: canvas_node.dimension,
        degree: canvas_node.degree,
        position: canvas_node.position,
        label: canvas_node.content,
        comment: this.generateNodeComment(canvas_node),
        execution_order: index,
        complexity_score: this.calculateNodeComplexity(canvas_node),
        hopf_compatible: this.isHopfCompatible(canvas_node)
      },
      aal_instruction,
      polynomial: canvas_node.polynomial
    };
    
    // Set parent relationships
    children.forEach(child => {
      child.parent = ast_node;
    });
    
    return ast_node;
  }
  
  /**
   * Map canvas node classification to AST node type
   */
  private mapCanvasNodeToASTType(canvas_node: CanvasNode): ASTNodeType {
    switch (canvas_node.classification) {
      case NodeClassification.ACTIVATE:
        return ASTNodeType.JUMP;
      case NodeClassification.INTEGRATE:
        return ASTNodeType.ASSIGNMENT;
      case NodeClassification.PROPAGATE:
        return ASTNodeType.OPERATION;
      case NodeClassification.BACKPROPAGATE:
        return ASTNodeType.CONDITIONAL;
      case NodeClassification.TRANSFORM:
        return ASTNodeType.OPERATION;
      case NodeClassification.VERIFY:
        return ASTNodeType.CONDITIONAL;
      case NodeClassification.STORE:
        return ASTNodeType.ASSIGNMENT;
      case NodeClassification.OBSERVE:
        return ASTNodeType.OBSERVER;
      case NodeClassification.DATA:
        return ASTNodeType.DATA;
      default:
        return ASTNodeType.OPERATION;
    }
  }
  
  /**
   * Create child nodes for complex canvas nodes
   */
  private createChildNodes(canvas_node: CanvasNode): ASTNode[] {
    const children: ASTNode[] = [];
    
    // Create parameter nodes for function-like structures
    if (canvas_node.dependents.length > 1) {
      canvas_node.dependents.forEach(dependent_id => {
        const dependent = this.canvas.nodes.find(n => n.id === dependent_id);
        if (dependent) {
          const child = this.createASTNode(dependent, -1, []);
          children.push(child);
        }
      });
    }
    
    return children;
  }
  
  /**
   * Create AAL instruction from canvas node
   */
  private createAALInstruction(canvas_node: CanvasNode): AALInstruction {
    return {
      id: this.generateInstructionId(canvas_node),
      opcode: this.mapClassificationToOpcode(canvas_node.classification),
      dimension: canvas_node.dimension,
      operands: this.generateOperands(canvas_node),
      polynomial: canvas_node.polynomial,
      verification: {
        algorithm: 'sha256',
        hash: this.generateInstructionHash(canvas_node),
        timestamp: Date.now(),
        theorem_reference: this.getTheoremReference(canvas_node.classification)
      },
      metadata: {
        source_node: canvas_node.id,
        comment: this.generateNodeComment(canvas_node)
      }
    };
  }
  
  /**
   * Generate AST edges from canvas edges
   */
  private generateASTEdges(canvas_edges: CanvasEdge[], _ast_nodes: ASTNode[]): ASTEdge[] {
    return canvas_edges.map(edge => ({
      from: edge.from,
      to: edge.to,
      type: edge.type,
      weight: edge.weight,
      label: (edge as any).label
    }));
  }
  
  /**
   * Group nodes into functions based on spatial and logical relationships
   */
  private groupNodesIntoFunctions(ordered_nodes: CanvasNode[]): CanvasNode[][] {
    const groups: CanvasNode[][] = [];
    const processed = new Set<string>();
    
    // Start with observer node as main function if present
    if (this.canvas.observer) {
      const main_function = this.extractFunctionNodes(this.canvas.observer, processed);
      if (main_function.length > 0) {
        groups.push(main_function);
      }
    }
    
    // Group remaining nodes
    ordered_nodes.forEach(node => {
      if (!processed.has(node.id)) {
        const group = this.extractFunctionNodes(node, processed);
        if (group.length > 0) {
          groups.push(group);
        }
      }
    });
    
    return groups;
  }
  
  /**
   * Extract function nodes starting from entry point
   */
  private extractFunctionNodes(entry_node: CanvasNode, processed: Set<string>): CanvasNode[] {
    const function_nodes: CanvasNode[] = [];
    const queue = [entry_node];
    
    while (queue.length > 0) {
      const current = queue.shift()!;
      
      if (processed.has(current.id)) continue;
      
      function_nodes.push(current);
      processed.add(current.id);
      
      // Add dependents to queue
      current.dependents.forEach(dependent_id => {
        const dependent = this.canvas.nodes.find(n => n.id === dependent_id);
        if (dependent && !processed.has(dependent_id)) {
          queue.push(dependent);
        }
      });
    }
    
    return function_nodes;
  }
  
  /**
   * Identify entry points in AST
   */
  private identifyEntryPoints(ast_nodes: ASTNode[], functions: FunctionDefinition[]): string[] {
    const entry_points: string[] = [];
    
    // Functions marked as entry points
    functions.filter(f => f.metadata.entry_point).forEach(f => {
      entry_points.push(f.name);
    });
    
    // Nodes with no dependencies
    ast_nodes.filter(node => 
      !this.canvas.nodes.find(n => n.id === node.metadata.source_node)?.dependencies.length
    ).forEach(node => {
      entry_points.push(node.id);
    });
    
    // Observer node
    if (this.canvas.observer) {
      entry_points.push(this.canvas.observer.id);
    }
    
    return entry_points;
  }
  
  /**
   * Identify exit points in AST
   */
  private identifyExitPoints(ast_nodes: ASTNode[], functions: FunctionDefinition[]): string[] {
    const exit_points: string[] = [];
    
    // Functions marked as exit points
    functions.filter(f => f.metadata.exit_point).forEach(f => {
      exit_points.push(f.name);
    });
    
    // Nodes with no dependents
    ast_nodes.filter(node => 
      !this.canvas.nodes.find(n => n.id === node.metadata.source_node)?.dependents.length
    ).forEach(node => {
      exit_points.push(node.id);
    });
    
    return exit_points;
  }
  
  /**
   * Calculate AST metadata
   */
  private calculateASTMetadata(
    ast_nodes: ASTNode[], 
    ast_edges: ASTEdge[], 
    cycles: string[][]
  ): ASTMetadata {
    const max_depth = this.calculateMaxDepth(ast_nodes);
    const complexity = this.calculateOverallComplexity(ast_nodes, ast_edges);
    const dimensions_used = this.extractDimensionsUsed(ast_nodes);
    
    return {
      total_nodes: ast_nodes.length,
      total_edges: ast_edges.length,
      max_depth,
      complexity,
      contains_cycles: cycles.length > 0,
      hopf_compatible: this.canvas.metadata.dimensional_analysis.hopf_compatibility,
      entry_points: [],
      exit_points: [],
      dimensions_used
    };
  }
  
  /**
   * Helper methods
   */
  private generateNodeId(canvas_node: CanvasNode): string {
    return `ast_node_${canvas_node.id}`;
  }
  
  private generateInstructionId(canvas_node: CanvasNode): string {
    return `instr_${canvas_node.id}_${Date.now()}`;
  }
  
  private generateFunctionName(entry_node: CanvasNode, index: number): string {
    const base_name = entry_node.content || `function_${index}`;
    return base_name.replace(/[^a-zA-Z0-9_]/g, '_');
  }
  
  private generateVariableName(canvas_node: CanvasNode): string {
    const base_name = canvas_node.content || canvas_node.id;
    return `var_${base_name.replace(/[^a-zA-Z0-9_]/g, '_')}_${this.variable_counter++}`;
  }
  
  private mapClassificationToOpcode(classification: NodeClassification): AssemblyOp {
    const mapping = {
      [NodeClassification.ACTIVATE]: AssemblyOp.JMP,
      [NodeClassification.INTEGRATE]: AssemblyOp.ADD,
      [NodeClassification.PROPAGATE]: AssemblyOp.SHL,
      [NodeClassification.BACKPROPAGATE]: AssemblyOp.CMP,
      [NodeClassification.TRANSFORM]: AssemblyOp.MUL,
      [NodeClassification.VERIFY]: AssemblyOp.VOTE,
      [NodeClassification.STORE]: AssemblyOp.PUSH,
      [NodeClassification.OBSERVE]: AssemblyOp.SYNC,
      [NodeClassification.DATA]: AssemblyOp.NOP,
      [NodeClassification.UNKNOWN]: AssemblyOp.NOP
    };
    
    return mapping[classification] || AssemblyOp.NOP;
  }
  
  private generateOperands(canvas_node: CanvasNode): number[] {
    // Generate memory addresses based on position
    return [
      Math.floor(canvas_node.position.x / 10),
      Math.floor(canvas_node.position.y / 10),
      Math.floor(Math.sqrt(canvas_node.position.x ** 2 + canvas_node.position.y ** 2))
    ];
  }
  
  private generateInstructionHash(canvas_node: CanvasNode): string {
    // Simple hash for demonstration
    const data = `${canvas_node.id}_${canvas_node.classification}_${canvas_node.polynomial}`;
    let hash = 0;
    for (let i = 0; i < data.length; i++) {
      hash = ((hash << 5) - hash) + data.charCodeAt(i);
      hash = hash & hash;
    }
    return Math.abs(hash).toString(16);
  }
  
  private getTheoremReference(classification: NodeClassification): string {
    const theorem_map: Record<string, string> = {
      [NodeClassification.ACTIVATE]: 'LinearTransformationTheorem',
      [NodeClassification.INTEGRATE]: 'PolynomialAdditionCommutativity',
      [NodeClassification.PROPAGATE]: 'PolynomialShiftProperties',
      [NodeClassification.BACKPROPAGATE]: 'PolynomialEqualityProperties',
      [NodeClassification.VERIFY]: 'MajorityVoteConsensus',
      [NodeClassification.STORE]: 'MemoryPreservationTheorem',
      [NodeClassification.OBSERVE]: 'QuantumObservationTheorem'
    };
    
    return theorem_map[classification as string] || 'GenericTheorem';
  }
  
  private generateNodeComment(canvas_node: CanvasNode): string {
    return `${canvas_node.classification} at (${canvas_node.position.x}, ${canvas_node.position.y})`;
  }
  
  private calculateNodeComplexity(canvas_node: CanvasNode): number {
    // Complexity based on degree, dimension, and dependencies
    return canvas_node.degree * 10 + canvas_node.dimension * 5 + canvas_node.dependencies.length * 2;
  }
  
  private isHopfCompatible(canvas_node: CanvasNode): boolean {
    // Check if node degree is compatible with Hopf fibrations (0, 1, 3, 7)
    return [0, 1, 3, 7].includes(canvas_node.degree);
  }
  
  private calculateMaxDepth(ast_nodes: ASTNode[]): number {
    let max_depth = 0;
    
    const calculateDepth = (node: ASTNode, depth: number): void => {
      max_depth = Math.max(max_depth, depth);
      node.children.forEach(child => calculateDepth(child, depth + 1));
    };
    
    ast_nodes.forEach(node => calculateDepth(node, 0));
    return max_depth;
  }
  
  private calculateOverallComplexity(ast_nodes: ASTNode[], ast_edges: ASTEdge[]): number {
    const node_complexity = ast_nodes.reduce((sum, node) => sum + (node.metadata.complexity_score || 0), 0);
    const edge_complexity = ast_edges.reduce((sum, edge) => sum + edge.weight * 10, 0);
    return node_complexity + edge_complexity;
  }
  
  private extractDimensionsUsed(ast_nodes: ASTNode[]): Dimension[] {
    const dimensions = new Set<Dimension>();
    ast_nodes.forEach(node => dimensions.add(node.metadata.dimension));
    return Array.from(dimensions);
  }
  
  // Placeholder implementations for methods that would be fully implemented
  private extractParameters(_group: CanvasNode[]): string[] { return []; }
  private inferReturnType(_group: CanvasNode[]): string { return 'any'; }
  private extractLocalVariables(_group: CanvasNode[]): VariableDefinition[] { return []; }
  private generateAssemblyTemplate(_entry_node: CanvasNode): string { return ''; }
  private isEntryPoint(_entry_node: CanvasNode): boolean { return false; }
  private isExitPoint(_exit_node: CanvasNode): boolean { return false; }
  private isObserverFunction(_group: CanvasNode[]): boolean { return false; }
  private inferVariableType(_node: CanvasNode): string { return 'any'; }
  private parseNodeContent(content: string): any { return content; }
}