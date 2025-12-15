/**
 * Type definitions for mind-git Canvas spatial programming
 * Based on Obsidian Canvas JSON format with mathematical node classification
 */

export interface CanvasNode {
  id: string;
  type: 'text' | 'file' | 'link' | 'group';
  x: number;
  y: number;
  width: number;
  height: number;
  text: string;
  color?: string;
}

export interface CanvasEdge {
  id: string;
  fromNode: string;
  toNode: string;
  label?: string;
}

export interface Canvas {
  nodes: CanvasNode[];
  edges: CanvasEdge[];
}

/**
 * Mathematical node classification by prefix
 * Maps to AAL assembly operations and dimensions (D0-D7)
 */
export enum NodeType {
  Activate = 'Activate',      // D0: JMP/CALL - Linear transformation
  Integrate = 'Integrate',    // D1: ADD/SUB - Polynomial addition
  Propagate = 'Propagate',    // D2: SHL/SHR - Polynomial shift
  BackPropagate = 'BackPropagate', // D3: CMP - Polynomial comparison
  Transform = 'Transform',    // D4: MUL/DIV - Polynomial multiplication
  Verify = 'Verify',          // D5: VOTE - Consensus voting
  Store = 'Store',            // D6: PUSH/POP - Memory stack
  Observe = 'Observe',        // D7: SYNC - Quantum observation
}

/**
 * Parse node prefix to determine mathematical classification
 */
export function parseNodeType(text: string): NodeType | null {
  const prefixes = {
    '#Activate:': NodeType.Activate,
    '#Integrate:': NodeType.Integrate,
    '#Propagate:': NodeType.Propagate,
    '#BackPropagate:': NodeType.BackPropagate,
    '#Transform:': NodeType.Transform,
    '#Verify:': NodeType.Verify,
    '#Store:': NodeType.Store,
    '#Observe:': NodeType.Observe,
  };

  for (const [prefix, type] of Object.entries(prefixes)) {
    if (text.startsWith(prefix)) {
      return type;
    }
  }
  return null;
}

/**
 * Get color for node based on mathematical type
 */
export function getNodeColor(nodeType: NodeType | null): string {
  const colors = {
    [NodeType.Activate]: '#FF6B6B',      // Red - Entry point
    [NodeType.Integrate]: '#4ECDC4',     // Teal - Addition
    [NodeType.Propagate]: '#95E1D3',     // Light teal - Shift
    [NodeType.BackPropagate]: '#F38181', // Pink - Comparison
    [NodeType.Transform]: '#AA96DA',     // Purple - Multiplication
    [NodeType.Verify]: '#FCBAD3',        // Light pink - Voting
    [NodeType.Store]: '#FFFFD2',         // Yellow - Memory
    [NodeType.Observe]: '#A8D8EA',       // Blue - Observation
  };
  return nodeType ? colors[nodeType] : '#CCCCCC';
}
