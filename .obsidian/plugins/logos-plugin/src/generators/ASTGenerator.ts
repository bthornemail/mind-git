import { ParsedCanvas, ClassifiedNode } from '../types/canvas';
import { AST, ASTNode, ASTEdge, ASTFunction, ASTVariable } from '../types/ast';

export class ASTGenerator {
	private canvas: ParsedCanvas;
	private ast: AST;

	constructor(canvas: ParsedCanvas) {
		this.canvas = canvas;
		this.ast = this.initializeAST();
	}

	generateAST(): AST {
		this.generateNodes();
		this.generateEdges();
		this.identifyEntryPoints();
		this.identifyExitPoints();
		this.extractFunctions();
		this.extractVariables();
		this.calculateMetadata();
		
		return this.ast;
	}

	private initializeAST(): AST {
		return {
			nodes: [],
			edges: [],
			functions: [],
			variables: [],
			entryPoints: [],
			exitPoints: [],
			metadata: {
				sourceCanvas: 'unknown',
				generatedAt: Date.now(),
				totalNodes: 0,
				totalEdges: 0,
				maxDepth: 0,
				complexity: 'simple',
				containsCycles: false
			}
		};
	}

	private generateNodes(): void {
		this.canvas.nodes.forEach(canvasNode => {
			const astNode: ASTNode = {
				id: this.generateASTNodeId(canvasNode.id),
				type: canvasNode.classification,
				operation: canvasNode.operation || 'NOOP',
				operands: canvasNode.operands || [],
				metadata: {
					canvasNodeId: canvasNode.id,
					position: { x: canvasNode.x, y: canvasNode.y },
					dimension: canvasNode.dimension || '0D',
					degree: canvasNode.degree || 0,
					originalContent: canvasNode.text || canvasNode.label || canvasNode.file,
					nodeType: this.determineNodeType(canvasNode)
				},
				dependencies: [],
				dependents: [],
				children: [],
				parents: []
			};

			this.ast.nodes.push(astNode);
		});
	}

	private generateEdges(): void {
		let edgeId = 0;

		this.canvas.edges.forEach(canvasEdge => {
			const fromASTNodeId = this.findASTNodeId(canvasEdge.fromNode);
			const toASTNodeId = this.findASTNodeId(canvasEdge.toNode);

			if (fromASTNodeId && toASTNodeId) {
				const astEdge: ASTEdge = {
					id: `edge_${edgeId++}`,
					from: fromASTNodeId,
					to: toASTNodeId,
					type: this.determineEdgeType(canvasEdge),
					label: canvasEdge.label,
					weight: this.calculateEdgeWeight(canvasEdge)
				};

				this.ast.edges.push(astEdge);

				// Update node relationships
				const fromNode = this.findASTNode(fromASTNodeId);
				const toNode = this.findASTNode(toASTNodeId);
				
				if (fromNode && toNode) {
					fromNode.dependents.push(toASTNodeId);
					toNode.dependencies.push(fromASTNodeId);
					toNode.parents.push(fromASTNodeId);
					fromNode.children.push(toASTNodeId);
				}
			}
		});
	}

	private identifyEntryPoints(): void {
		// Nodes with no dependencies are entry points
		this.ast.entryPoints = this.ast.nodes
			.filter(node => node.dependencies.length === 0)
			.map(node => node.id);
	}

	private identifyExitPoints(): void {
		// Nodes with no dependents are exit points
		this.ast.exitPoints = this.ast.nodes
			.filter(node => node.dependents.length === 0)
			.map(node => node.id);
	}

	private extractFunctions(): void {
		// Extract functions from activate and integrate nodes
		this.canvas.nodes.forEach(canvasNode => {
			if (canvasNode.classification === 'activate' || canvasNode.classification === 'integrate') {
				const func = this.createFunctionFromNode(canvasNode);
				if (func) {
					this.ast.functions.push(func);
				}
			}
		});
	}

	private extractVariables(): void {
		// Extract variables from operands and data nodes
		const variableNames = new Set<string>();

		this.ast.nodes.forEach(node => {
			// Extract from operands
			node.operands.forEach(operand => {
				if (this.isVariableName(operand)) {
					variableNames.add(operand);
				}
			});

			// Extract from data nodes
			if (node.type === 'data' && node.metadata.originalContent) {
				const vars = this.extractVariablesFromContent(node.metadata.originalContent);
				vars.forEach(v => variableNames.add(v));
			}
		});

		// Create ASTVariable objects
		variableNames.forEach(name => {
			const astVar: ASTVariable = {
				id: `var_${name}`,
				name,
				type: this.inferVariableType(name),
				scope: 'global',
				value: undefined
			};
			this.ast.variables.push(astVar);
		});
	}

	private calculateMetadata(): void {
		this.ast.metadata.totalNodes = this.ast.nodes.length;
		this.ast.metadata.totalEdges = this.ast.edges.length;
		this.ast.metadata.sourceCanvas = this.detectCanvasName();
		this.ast.metadata.maxDepth = this.calculateMaxDepth();
		this.ast.metadata.complexity = this.assessComplexity();
		this.ast.metadata.containsCycles = this.detectCycles();
	}

	// Helper methods

	private generateASTNodeId(canvasNodeId: string): string {
		return `ast_${canvasNodeId}`;
	}

	private findASTNodeId(canvasNodeId: string): string | undefined {
		return this.ast.nodes.find(node => node.metadata.canvasNodeId === canvasNodeId)?.id;
	}

	private findASTNode(astNodeId: string): ASTNode | undefined {
		return this.ast.nodes.find(node => node.id === astNodeId);
	}

	private determineNodeType(canvasNode: ClassifiedNode): 'function' | 'data' | 'control' {
		if (['activate', 'integrate', 'transform', 'propagate'].includes(canvasNode.classification)) {
			return 'function';
		} else if (['verify', 'store'].includes(canvasNode.classification)) {
			return 'control';
		} else {
			return 'data';
		}
	}

	private determineEdgeType(canvasEdge: any): 'dataflow' | 'dependency' | 'control' | 'composition' {
		// Simple heuristic based on edge label or direction
		if (canvasEdge.label) {
			if (canvasEdge.label.toLowerCase().includes('data') || canvasEdge.label.toLowerCase().includes('flow')) {
				return 'dataflow';
			} else if (canvasEdge.label.toLowerCase().includes('control') || canvasEdge.label.toLowerCase().includes('if') || canvasEdge.label.toLowerCase().includes('branch')) {
				return 'control';
			} else if (canvasEdge.label.toLowerCase().includes('compose') || canvasEdge.label.toLowerCase().includes('merge')) {
				return 'composition';
			}
		}
		return 'dependency';
	}

	private calculateEdgeWeight(canvasEdge: any): number {
		// Weight based on edge properties (1-5 scale)
		let weight = 3; // default
		
		if (canvasEdge.color) {
			weight = 4; // colored edges are more important
		}
		
		if (canvasEdge.label) {
			weight = 5; // labeled edges are most important
		}
		
		return weight;
	}

	private createFunctionFromNode(canvasNode: ClassifiedNode): ASTFunction | null {
		const content = canvasNode.text || canvasNode.label || '';
		const operands = canvasNode.operands || [];
		
		const functionName = this.extractFunctionName(content);
		if (!functionName) return null;

		return {
			id: `func_${canvasNode.id}`,
			name: functionName,
			parameters: operands,
			returnType: this.inferReturnType(canvasNode.classification),
			body: [content],
			assemblyTemplate: this.getAssemblyTemplate(canvasNode.classification)
		};
	}

	private extractFunctionName(content: string): string | null {
		const lines = content.split('\n');
		const firstLine = lines[0];
		
		// Extract from #Activate: functionName
		const activateMatch = firstLine.match(/^#Activate:\s*(\w+)/);
		if (activateMatch) return activateMatch[1];
		
		// Extract from #Integrate: var1 var2 -> integrate_var1_var2
		const integrateMatch = firstLine.match(/^#Integrate:\s*(.+)/);
		if (integrateMatch) {
			const vars = integrateMatch[1].trim().split(/\s+/);
			return `integrate_${vars.join('_')}`;
		}
		
		return null;
	}

	private inferReturnType(classification: string): string {
		const typeMap: Record<string, string> = {
			'activate': 'void',
			'integrate': 'number',
			'transform': 'number',
			'propagate': 'any[]',
			'verify': 'boolean',
			'store': 'void',
			'observe': 'any'
		};
		return typeMap[classification] || 'any';
	}

	private getAssemblyTemplate(classification: string): string {
		const templateMap: Record<string, string> = {
			'activate': 'JMP {target}',
			'integrate': 'ADD {dest}, {src1}, {src2}',
			'transform': 'MUL {dest}, {src1}, {src2}',
			'propagate': 'SHL {dest}, {src}, {count}',
			'verify': 'CMP {left}, {right}',
			'store': 'MOV [{addr}], {value}',
			'observe': 'LD {dest}, [{addr}]'
		};
		return templateMap[classification] || 'NOOP';
	}

	private isVariableName(name: string): boolean {
		// Simple heuristic: starts with letter or underscore, contains only letters, numbers, underscore
		return /^[a-zA-Z_][a-zA-Z0-9_]*$/.test(name) && !['if', 'else', 'for', 'while', 'return'].includes(name);
	}

	private extractVariablesFromContent(content: string): string[] {
		const variables: string[] = [];
		const words = content.split(/\s+/);
		
		words.forEach(word => {
			const cleanWord = word.replace(/[^\w]/g, '');
			if (this.isVariableName(cleanWord)) {
				variables.push(cleanWord);
			}
		});
		
		return [...new Set(variables)];
	}

	private inferVariableType(name: string): string {
		// Simple type inference based on naming patterns
		if (name.toLowerCase().includes('result') || name.toLowerCase().includes('sum') || name.toLowerCase().includes('count')) {
			return 'number';
		} else if (name.toLowerCase().includes('is') || name.toLowerCase().includes('has') || name.toLowerCase().includes('can')) {
			return 'boolean';
		} else if (name.toLowerCase().includes('data') || name.toLowerCase().includes('list') || name.toLowerCase().includes('array')) {
			return 'any[]';
		}
		return 'any';
	}

	private detectCanvasName(): string {
		// Try to extract canvas name from file path or content
		const canvasNodes = this.canvas.nodes.filter(node => node.type === 'file' && node.file);
		if (canvasNodes.length > 0) {
			return canvasNodes[0].file?.replace(/\.(md|txt)$/, '') || 'unknown';
		}
		return 'untitled-canvas';
	}

	private calculateMaxDepth(): number {
		// Calculate maximum depth of the dependency graph
		const visited = new Set<string>();
		let maxDepth = 0;

		const calculateDepth = (nodeId: string, currentDepth: number): void => {
			if (visited.has(nodeId)) return;
			visited.add(nodeId);
			
			maxDepth = Math.max(maxDepth, currentDepth);
			
			const node = this.findASTNode(nodeId);
			if (node) {
				node.children.forEach(childId => {
					calculateDepth(childId, currentDepth + 1);
				});
			}
		};

		this.ast.entryPoints.forEach(entryId => {
			calculateDepth(entryId, 1);
		});

		return maxDepth;
	}

	private assessComplexity(): 'simple' | 'moderate' | 'complex' {
		const nodeCount = this.ast.nodes.length;
		const edgeCount = this.ast.edges.length;
		const functionCount = this.ast.functions.length;
		const variableCount = this.ast.variables.length;
		const hasCycles = this.detectCycles();

		// Complexity scoring
		let score = 0;
		score += nodeCount > 20 ? 2 : nodeCount > 10 ? 1 : 0;
		score += edgeCount > 30 ? 2 : edgeCount > 15 ? 1 : 0;
		score += functionCount > 10 ? 2 : functionCount > 5 ? 1 : 0;
		score += variableCount > 20 ? 2 : variableCount > 10 ? 1 : 0;
		if (hasCycles) score += 3;

		if (score >= 6) return 'complex';
		if (score >= 3) return 'moderate';
		return 'simple';
	}

	private detectCycles(): boolean {
		const visited = new Set<string>();
		const recursionStack = new Set<string>();

		const hasCycle = (nodeId: string): boolean => {
			visited.add(nodeId);
			recursionStack.add(nodeId);

			const node = this.findASTNode(nodeId);
			if (node) {
				for (const childId of node.children) {
					if (!visited.has(childId)) {
						if (hasCycle(childId)) return true;
					} else if (recursionStack.has(childId)) {
						return true;
					}
				}
			}

			recursionStack.delete(nodeId);
			return false;
		};

		for (const node of this.ast.nodes) {
			if (!visited.has(node.id)) {
				if (hasCycle(node.id)) return true;
			}
		}

		return false;
	}
}
