import { App, Modal, TFile } from 'obsidian';
import { ParsedCanvas, ClassifiedNode } from '../types/canvas';
import { AST } from '../types/ast';
import { CanvasParser } from '../parsers/CanvasParser';
import { ASTGenerator } from '../generators/ASTGenerator';

export class CompilerModal extends Modal {
	private parser: CanvasParser;
	private canvasFile: TFile | null = null;
	private parsed: ParsedCanvas | null = null;
	private ast: AST | null = null;

	constructor(app: App) {
		super(app);
		this.parser = new CanvasParser();
	}

async openWithFile(file: TFile) {
		this.canvasFile = file;
		try {
			this.parsed = await this.parser.parseCanvasFile(file);
			
			// Generate AST
			const generator = new ASTGenerator(this.parsed);
			this.ast = generator.generateAST();
			
			this.open();
} catch (error) {
			console.error('Failed to parse canvas:', error);
			this.showError(error.message);
		}
	}

	onOpen() {
		const { contentEl } = this;
		contentEl.empty();
		contentEl.addClass('logos-compiler-modal');

		if (!this.parsed || !this.canvasFile) {
			this.showError('No canvas data available');
			return;
		}

	this.renderHeader(contentEl);
		this.renderMetadata(contentEl);
		this.renderAST(contentEl);
		this.renderNodes(contentEl);
		this.renderEdges(contentEl);
		this.renderDependencyAnalysis(contentEl);
	}

	private renderHeader(container: HTMLElement) {
		const header = container.createDiv({ cls: 'logos-modal-header' });
		header.createEl('h2', { text: '🎨 Logos Visual Compiler' });
		
		if (this.canvasFile) {
			header.createEl('p', { 
				text: `Canvas: ${this.canvasFile.basename}`,
				cls: 'logos-canvas-name'
			});
		}
	}

	private renderMetadata(container: HTMLElement) {
		if (!this.parsed) return;

		const section = container.createDiv({ cls: 'logos-section' });
		section.createEl('h3', { text: '📊 Canvas Metadata' });

		const metadata = this.parsed.metadata;
		const metaList = section.createEl('ul', { cls: 'logos-metadata-list' });

		metaList.createEl('li', { text: `Total Nodes: ${metadata.totalNodes}` });
		metaList.createEl('li', { text: `Total Edges: ${metadata.totalEdges}` });
		metaList.createEl('li', { text: `Max Degree: ${metadata.maxDegree}` });

		const typesSection = section.createDiv({ cls: 'logos-node-types' });
		typesSection.createEl('h4', { text: 'Node Types:' });
		const typesList = typesSection.createEl('ul');

		Object.entries(metadata.nodeTypes).forEach(([type, count]) => {
			const emoji = this.getEmojiForType(type);
			typesList.createEl('li', { text: `${emoji} ${type}: ${count}` });
		});
	}

	private renderAST(container: HTMLElement) {
		if (!this.ast) return;

		const section = container.createDiv({ cls: 'logos-section' });
		section.createEl('h3', { text: '🌳 Abstract Syntax Tree (AST)' });

		// AST metadata
		const metadata = this.ast.metadata;
		const metadataList = section.createEl('ul', { cls: 'logos-ast-metadata' });
		metadataList.createEl('li', { text: `Functions: ${this.ast.functions.length}` });
		metadataList.createEl('li', { text: `Variables: ${this.ast.variables.length}` });
		metadataList.createEl('li', { text: `Entry Points: ${this.ast.entryPoints.length}` });
		metadataList.createEl('li', { text: `Max Depth: ${metadata.maxDepth}` });
		metadataList.createEl('li', { text: `Complexity: ${metadata.complexity}` });
		metadataList.createEl('li', { 
			text: `Cycles: ${metadata.containsCycles ? '⚠️ Yes' : '✅ No'}`,
			cls: metadata.containsCycles ? 'logos-warning' : 'logos-success'
		});

		// Functions section
		if (this.ast.functions.length > 0) {
			const functionsSection = section.createDiv({ cls: 'logos-ast-functions' });
			functionsSection.createEl('h4', { text: '🔧 Extracted Functions' });
			
			const functionsContainer = functionsSection.createDiv({ cls: 'logos-functions-container' });
			this.ast.functions.forEach(func => {
				this.renderFunction(functionsContainer, func);
			});
		}

		// Variables section
		if (this.ast.variables.length > 0) {
			const variablesSection = section.createDiv({ cls: 'logos-ast-variables' });
			variablesSection.createEl('h4', { text: '📝 Identified Variables' });
			
			const variablesContainer = variablesSection.createDiv({ cls: 'logos-variables-container' });
			const variablesList = variablesContainer.createEl('ul');
			this.ast.variables.forEach(variable => {
				const varEl = variablesList.createEl('li', { cls: 'logos-variable-item' });
				varEl.createEl('span', { 
					text: `${variable.name}: ${variable.type}`,
					cls: 'logos-variable-name'
				});
				varEl.createEl('span', { 
					text: `(${variable.scope})`,
					cls: 'logos-variable-scope'
				});
			});
		}

		// AST structure visualization
		const structureSection = section.createDiv({ cls: 'logos-ast-structure' });
		structureSection.createEl('h4', { text: '🏗️ AST Structure' });
		
		const structureContainer = structureSection.createDiv({ cls: 'logos-structure-container' });
		this.renderASTStructure(structureContainer);
	}

	private renderFunction(container: HTMLElement, func: any) {
		const funcEl = container.createDiv({ cls: 'logos-function' });
		
		const header = funcEl.createDiv({ cls: 'logos-function-header' });
		header.createEl('span', { 
			text: `${func.name}(${func.parameters.join(', ')})`,
			cls: 'logos-function-signature'
		});
		
		if (func.returnType) {
			header.createEl('span', { 
				text: `: ${func.returnType}`,
				cls: 'logos-function-return'
			});
		}

		const body = funcEl.createDiv({ cls: 'logos-function-body' });
		if (func.assemblyTemplate) {
			body.createEl('div', { 
				text: `Assembly: ${func.assemblyTemplate}`,
				cls: 'logos-function-assembly'
			});
		}

		if (func.body && func.body.length > 0) {
			body.createEl('div', { cls: 'logos-function-content' });
			func.body.forEach(line => {
				body.createEl('div', { 
					text: line,
					cls: 'logos-function-line'
				});
			});
		}
	}

	private renderASTStructure(container: HTMLElement) {
		if (!this.ast) return;

		const canvas = container.createEl('canvas', { 
			cls: 'logos-ast-canvas'
		});
		canvas.width = 600;
		canvas.height = 400;
		
		const ctx = canvas.getContext('2d');
		if (!ctx) return;

		// Simple tree visualization
		const nodeMap = new Map();
		this.ast.nodes.forEach((node, index) => {
			const x = 50 + (index * 120) % 550;
			const y = 50 + Math.floor(index * 120 / 550) * 100;
			
			// Store node position
			nodeMap.set(node.id, { x, y, node });
			
			// Draw node
			ctx.fillStyle = this.getNodeColor(node.type);
			ctx.fillRect(x - 30, y - 20, 60, 40);
			ctx.strokeStyle = '#000';
			ctx.strokeRect(x - 30, y - 20, 60, 40);
			
			// Draw label
			ctx.fillStyle = '#fff';
			ctx.font = '12px monospace';
			ctx.textAlign = 'center';
			ctx.fillText(node.type.substring(0, 3), x, y + 5);
		});

		// Draw edges
		ctx.strokeStyle = '#666';
		ctx.lineWidth = 1;
		this.ast.edges.forEach(edge => {
			const fromPos = nodeMap.get(edge.from);
			const toPos = nodeMap.get(edge.to);
			
			if (fromPos && toPos) {
				ctx.beginPath();
				ctx.moveTo(fromPos.x, fromPos.y);
				ctx.lineTo(toPos.x, toPos.y);
				ctx.stroke();
				
				// Arrow
				const angle = Math.atan2(toPos.y - fromPos.y, toPos.x - fromPos.x);
				ctx.save();
				ctx.translate(toPos.x, toPos.y);
				ctx.rotate(angle);
				ctx.beginPath();
				ctx.moveTo(-10, -5);
				ctx.lineTo(0, 0);
				ctx.lineTo(-10, 5);
				ctx.stroke();
				ctx.restore();
			}
		});
	}

	private getNodeColor(type: string): string {
		const colorMap: Record<string, string> = {
			'activate': '#3498db',
			'integrate': '#2ecc71',
			'transform': '#f39c12',
			'propagate': '#9b59b6',
			'verify': '#e74c3c',
			'store': '#95a5a6',
			'observe': '#e67e22',
			'data': '#34495e'
		};
		return colorMap[type] || '#666';
	}

	private renderNodes(container: HTMLElement) {
		if (!this.parsed) return;

		const section = container.createDiv({ cls: 'logos-section' });
		section.createEl('h3', { text: '🔷 Classified Nodes' });

		const nodesContainer = section.createDiv({ cls: 'logos-nodes-container' });

		this.parsed.nodes.forEach(node => {
			this.renderNode(nodesContainer, node);
		});
	}

	private renderNode(container: HTMLElement, node: ClassifiedNode) {
		const nodeEl = container.createDiv({ cls: 'logos-node' });
		nodeEl.addClass(`logos-node-${node.classification}`);

		const header = nodeEl.createDiv({ cls: 'logos-node-header' });
		const emoji = this.getEmojiForType(node.classification);
		header.createEl('span', { 
			text: `${emoji} ${node.classification.toUpperCase()}`,
			cls: 'logos-node-type'
		});

		if (node.operation) {
			header.createEl('span', { 
				text: node.operation,
				cls: 'logos-node-operation'
			});
		}

		const body = nodeEl.createDiv({ cls: 'logos-node-body' });
		
		body.createEl('div', { 
			text: `ID: ${node.id}`,
			cls: 'logos-node-id'
		});

		body.createEl('div', { 
			text: `Position: (${node.x}, ${node.y})`,
			cls: 'logos-node-position'
		});

		if (node.dimension) {
			body.createEl('div', { 
				text: `Dimension: ${node.dimension}`,
				cls: 'logos-node-dimension'
			});
		}

		if (node.degree !== undefined) {
			body.createEl('div', { 
				text: `Degree: ${node.degree}`,
				cls: 'logos-node-degree'
			});
		}

		if (node.operands && node.operands.length > 0) {
			body.createEl('div', { 
				text: `Operands: ${node.operands.join(', ')}`,
				cls: 'logos-node-operands'
			});
		}

		const content = node.text || node.label || node.file || '';
		if (content) {
			const contentEl = body.createDiv({ cls: 'logos-node-content' });
			contentEl.createEl('strong', { text: 'Content:' });
			contentEl.createEl('pre', { text: content.substring(0, 100) + (content.length > 100 ? '...' : '') });
		}
	}

	private renderEdges(container: HTMLElement) {
		if (!this.parsed || this.parsed.edges.length === 0) return;

		const section = container.createDiv({ cls: 'logos-section' });
		section.createEl('h3', { text: '🔗 Edges (Dependencies)' });

		const edgesList = section.createEl('ul', { cls: 'logos-edges-list' });

		this.parsed.edges.forEach(edge => {
			const fromNode = this.parser.getNodeById(this.parsed!, edge.fromNode);
			const toNode = this.parser.getNodeById(this.parsed!, edge.toNode);

			const fromLabel = fromNode?.classification || edge.fromNode.substring(0, 8);
			const toLabel = toNode?.classification || edge.toNode.substring(0, 8);

			edgesList.createEl('li', { 
				text: `${fromLabel} → ${toLabel}${edge.label ? ` (${edge.label})` : ''}`
			});
		});
	}

	private renderDependencyAnalysis(container: HTMLElement) {
		if (!this.parsed) return;

		const section = container.createDiv({ cls: 'logos-section' });
		section.createEl('h3', { text: '🔍 Dependency Analysis' });

		try {
			const cycles = this.parser.detectCircularDependencies(this.parsed);
			
			if (cycles.length > 0) {
				const warning = section.createDiv({ cls: 'logos-warning' });
				warning.createEl('strong', { text: '⚠️ Circular Dependencies Detected:' });
				const cyclesList = warning.createEl('ul');
				cycles.forEach(cycle => {
					cyclesList.createEl('li', { text: cycle.join(' → ') });
				});
			} else {
				section.createEl('p', { 
					text: '✅ No circular dependencies detected',
					cls: 'logos-success'
				});

				try {
					const order = this.parser.getTopologicalOrder(this.parsed);
					const orderSection = section.createDiv({ cls: 'logos-topological-order' });
					orderSection.createEl('h4', { text: 'Execution Order:' });
					const orderList = orderSection.createEl('ol');
					order.forEach(node => {
						const emoji = this.getEmojiForType(node.classification);
						orderList.createEl('li', { 
							text: `${emoji} ${node.classification} (${node.id.substring(0, 8)})`
						});
					});
				} catch (error) {
					section.createEl('p', { 
						text: `⚠️ Could not determine execution order: ${error.message}`,
						cls: 'logos-warning'
					});
				}
			}
		} catch (error) {
			section.createEl('p', { 
				text: `Error analyzing dependencies: ${error.message}`,
				cls: 'logos-error'
			});
		}
	}

	private getEmojiForType(type: string): string {
		const emojiMap: Record<string, string> = {
			'activate': '🚀',
			'integrate': '➕',
			'transform': '🔄',
			'propagate': '📡',
			'verify': '✅',
			'store': '💾',
			'observe': '👁️',
			'data': '📄',
			'unknown': '❓'
		};
		return emojiMap[type] || '⚪';
	}

	private showError(message: string) {
		const { contentEl } = this;
		contentEl.empty();
		contentEl.createEl('h2', { text: '❌ Error' });
		contentEl.createEl('p', { text: message, cls: 'logos-error' });
	}

	onClose() {
		const { contentEl } = this;
		contentEl.empty();
	}
}
