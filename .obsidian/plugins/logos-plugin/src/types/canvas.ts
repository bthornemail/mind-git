export interface CanvasNode {
	id: string;
	type: 'text' | 'file' | 'link' | 'group';
	x: number;
	y: number;
	width: number;
	height: number;
	color?: string;
	text?: string;
	file?: string;
	url?: string;
	label?: string;
}

export interface CanvasEdge {
	id: string;
	fromNode: string;
	toNode: string;
	fromSide?: 'top' | 'right' | 'bottom' | 'left';
	toSide?: 'top' | 'right' | 'bottom' | 'left';
	fromEnd?: 'none' | 'arrow';
	toEnd?: 'none' | 'arrow';
	color?: string;
	label?: string;
}

export interface CanvasData {
	nodes: CanvasNode[];
	edges: CanvasEdge[];
}

export type NodeClassification = 
	| 'activate'
	| 'integrate'
	| 'transform'
	| 'propagate'
	| 'verify'
	| 'store'
	| 'observe'
	| 'data'
	| 'unknown';

export interface ClassifiedNode extends CanvasNode {
	classification: NodeClassification;
	operation?: string;
	operands?: string[];
	dimension?: string;
	degree?: number;
}

export interface ParsedCanvas {
	raw: CanvasData;
	nodes: ClassifiedNode[];
	edges: CanvasEdge[];
	metadata: {
		totalNodes: number;
		totalEdges: number;
		nodeTypes: Record<NodeClassification, number>;
		maxDegree: number;
	};
}
