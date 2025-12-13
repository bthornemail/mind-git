export interface ASTNode {
	id: string;
	type: 'activate' | 'integrate' | 'transform' | 'propagate' | 'verify' | 'store' | 'observe' | 'data';
	operation: string;
	operands: string[];
	metadata: {
		canvasNodeId: string;
		position: { x: number; y: number };
		dimension: string;
		degree: number;
		originalContent?: string;
		nodeType: 'function' | 'data' | 'control';
	};
	dependencies: string[];
	dependents: string[];
	children: string[];
	parents: string[];
}

export interface ASTEdge {
	id: string;
	from: string;
	to: string;
	type: 'dataflow' | 'dependency' | 'control' | 'composition';
	label?: string;
	weight: number; // 1-5 for visual importance
}

export interface ASTFunction {
	id: string;
	name: string;
	parameters: string[];
	returnType?: string;
	body: string[];
	assemblyTemplate: string;
}

export interface ASTVariable {
	id: string;
	name: string;
	type: string;
	value?: string;
	scope: string;
}

export interface AST {
	nodes: ASTNode[];
	edges: ASTEdge[];
	functions: ASTFunction[];
	variables: ASTVariable[];
	entryPoints: string[];
	exitPoints: string[];
	metadata: {
		sourceCanvas: string;
		generatedAt: number;
		totalNodes: number;
		totalEdges: number;
		maxDepth: number;
		complexity: 'simple' | 'moderate' | 'complex';
		containsCycles: boolean;
	};
}
