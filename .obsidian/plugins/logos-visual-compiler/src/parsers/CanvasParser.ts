import { TFile } from 'obsidian';
import { CanvasData, CanvasNode, CanvasEdge, ParsedCanvas, ClassifiedNode } from '../types/canvas';
import { NodeClassifier } from './NodeClassifier';

export class CanvasParser {
	private classifier: NodeClassifier;

	constructor() {
		this.classifier = new NodeClassifier();
	}

	async parseCanvasFile(file: TFile): Promise<ParsedCanvas> {
		const content = await file.vault.read(file);
		return this.parseCanvasContent(content);
	}

	parseCanvasContent(content: string): ParsedCanvas {
		try {
			const raw: CanvasData = JSON.parse(content);
			
			if (!raw.nodes || !Array.isArray(raw.nodes)) {
				throw new Error('Invalid canvas format: missing nodes array');
			}

			const classifiedNodes = raw.nodes.map(node => 
				this.classifier.classifyNode(node)
			);

			const edges = raw.edges || [];

			const metadata = this.generateMetadata(classifiedNodes, edges);

			return {
				raw,
				nodes: classifiedNodes,
				edges,
				metadata
			};
		} catch (error) {
			throw new Error(`Failed to parse canvas: ${error.message}`);
		}
	}

	private generateMetadata(nodes: ClassifiedNode[], edges: CanvasEdge[]) {
		const nodeTypes: Record<string, number> = {};
		let maxDegree = 0;

		nodes.forEach(node => {
			const classification = node.classification;
			nodeTypes[classification] = (nodeTypes[classification] || 0) + 1;
			
			if (node.degree !== undefined && node.degree > maxDegree) {
				maxDegree = node.degree;
			}
		});

		return {
			totalNodes: nodes.length,
			totalEdges: edges.length,
			nodeTypes,
			maxDegree
		};
	}

	findCanvasFiles(files: TFile[]): TFile[] {
		return files.filter(file => file.extension === 'canvas');
	}

	getNodeById(parsed: ParsedCanvas, nodeId: string): ClassifiedNode | undefined {
		return parsed.nodes.find(node => node.id === nodeId);
	}

	getNodeDependencies(parsed: ParsedCanvas, nodeId: string): ClassifiedNode[] {
		const dependencyIds = parsed.edges
			.filter(edge => edge.toNode === nodeId)
			.map(edge => edge.fromNode);

		return dependencyIds
			.map(id => this.getNodeById(parsed, id))
			.filter((node): node is ClassifiedNode => node !== undefined);
	}

	getNodeDependents(parsed: ParsedCanvas, nodeId: string): ClassifiedNode[] {
		const dependentIds = parsed.edges
			.filter(edge => edge.fromNode === nodeId)
			.map(edge => edge.toNode);

		return dependentIds
			.map(id => this.getNodeById(parsed, id))
			.filter((node): node is ClassifiedNode => node !== undefined);
	}

	detectCircularDependencies(parsed: ParsedCanvas): string[][] {
		const cycles: string[][] = [];
		const visited = new Set<string>();
		const recursionStack = new Set<string>();

		const dfs = (nodeId: string, path: string[]): void => {
			visited.add(nodeId);
			recursionStack.add(nodeId);
			path.push(nodeId);

			const dependents = this.getNodeDependents(parsed, nodeId);
			
			for (const dependent of dependents) {
				if (!visited.has(dependent.id)) {
					dfs(dependent.id, [...path]);
				} else if (recursionStack.has(dependent.id)) {
					const cycleStart = path.indexOf(dependent.id);
					cycles.push([...path.slice(cycleStart), dependent.id]);
				}
			}

			recursionStack.delete(nodeId);
		};

		for (const node of parsed.nodes) {
			if (!visited.has(node.id)) {
				dfs(node.id, []);
			}
		}

		return cycles;
	}

	getTopologicalOrder(parsed: ParsedCanvas): ClassifiedNode[] {
		const inDegree = new Map<string, number>();
		const adjList = new Map<string, string[]>();

		parsed.nodes.forEach(node => {
			inDegree.set(node.id, 0);
			adjList.set(node.id, []);
		});

		parsed.edges.forEach(edge => {
			inDegree.set(edge.toNode, (inDegree.get(edge.toNode) || 0) + 1);
			const neighbors = adjList.get(edge.fromNode) || [];
			neighbors.push(edge.toNode);
			adjList.set(edge.fromNode, neighbors);
		});

		const queue: string[] = [];
		inDegree.forEach((degree, nodeId) => {
			if (degree === 0) {
				queue.push(nodeId);
			}
		});

		const result: ClassifiedNode[] = [];

		while (queue.length > 0) {
			const nodeId = queue.shift()!;
			const node = this.getNodeById(parsed, nodeId);
			if (node) {
				result.push(node);
			}

			const neighbors = adjList.get(nodeId) || [];
			neighbors.forEach(neighborId => {
				const degree = inDegree.get(neighborId)! - 1;
				inDegree.set(neighborId, degree);
				if (degree === 0) {
					queue.push(neighborId);
				}
			});
		}

		if (result.length !== parsed.nodes.length) {
			throw new Error('Circular dependency detected - cannot create topological order');
		}

		return result;
	}
}
