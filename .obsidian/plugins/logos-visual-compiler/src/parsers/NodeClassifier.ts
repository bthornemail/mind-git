import { CanvasNode, ClassifiedNode, NodeClassification } from '../types/canvas';

interface NodePattern {
	prefix: string;
	classification: NodeClassification;
	operation: string;
	dimension: string;
	degree: number;
}

export class NodeClassifier {
	private patterns: NodePattern[] = [
		{ prefix: '#Activate:', classification: 'activate', operation: 'JMP/CALL', dimension: '0D→1D', degree: 0 },
		{ prefix: '#Integrate:', classification: 'integrate', operation: 'ADD/SUB', dimension: '1D→2D', degree: 1 },
		{ prefix: '#Transform:', classification: 'transform', operation: 'MUL/DIV', dimension: '2D→3D', degree: 2 },
		{ prefix: '#Propagate:', classification: 'propagate', operation: 'SHL/ROL', dimension: '3D→4D', degree: 3 },
		{ prefix: '#Verify:', classification: 'verify', operation: 'CMP/TEST', dimension: '4D→5D', degree: 4 },
		{ prefix: '#Store:', classification: 'store', operation: 'MOV/ST', dimension: '5D→6D', degree: 5 },
		{ prefix: '#Observe:', classification: 'observe', operation: 'LD/GET', dimension: '6D→7D', degree: 6 },
	];

	classifyNode(node: CanvasNode): ClassifiedNode {
		const content = this.getNodeContent(node);
		
		if (!content) {
			return {
				...node,
				classification: 'data',
				degree: 0
			};
		}

		for (const pattern of this.patterns) {
			if (content.startsWith(pattern.prefix)) {
				const operands = this.extractOperands(content, pattern.prefix);
				return {
					...node,
					classification: pattern.classification,
					operation: pattern.operation,
					operands,
					dimension: pattern.dimension,
					degree: pattern.degree
				};
			}
		}

		if (this.isObserverNode(node)) {
			return {
				...node,
				classification: 'observe',
				operation: 'IDENTITY',
				dimension: '0D',
				degree: 0,
				operands: []
			};
		}

		return {
			...node,
			classification: 'data',
			degree: 0
		};
	}

	private getNodeContent(node: CanvasNode): string {
		if (node.text) {
			return node.text.trim();
		}
		if (node.label) {
			return node.label.trim();
		}
		if (node.file) {
			return node.file;
		}
		return '';
	}

	private extractOperands(content: string, prefix: string): string[] {
		const afterPrefix = content.substring(prefix.length).trim();
		const firstLine = afterPrefix.split('\n')[0].trim();
		
		if (!firstLine) {
			return [];
		}

		return firstLine.split(/\s+/).filter(op => op.length > 0);
	}

	private isObserverNode(node: CanvasNode): boolean {
		return node.x === 0 && node.y === 0;
	}

	getClassificationInfo(classification: NodeClassification): string {
		const pattern = this.patterns.find(p => p.classification === classification);
		if (pattern) {
			return `${pattern.classification} (${pattern.operation}) - ${pattern.dimension}`;
		}
		return classification;
	}

	getAllClassifications(): NodeClassification[] {
		return [
			...this.patterns.map(p => p.classification),
			'data',
			'unknown'
		];
	}

	getDegreeForClassification(classification: NodeClassification): number {
		const pattern = this.patterns.find(p => p.classification === classification);
		return pattern?.degree ?? 0;
	}

	getOperationForClassification(classification: NodeClassification): string {
		const pattern = this.patterns.find(p => p.classification === classification);
		return pattern?.operation ?? 'UNKNOWN';
	}
}
