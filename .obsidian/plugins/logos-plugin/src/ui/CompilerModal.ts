import { App, Modal, TFile } from 'obsidian';
import { ParsedCanvas, ClassifiedNode } from '../types/canvas';
import { CanvasParser } from '../parsers/CanvasParser';

export class CompilerModal extends Modal {
	private parser: CanvasParser;
	private canvasFile: TFile | null = null;
	private parsed: ParsedCanvas | null = null;

	constructor(app: App) {
		super(app);
		this.parser = new CanvasParser();
	}

	async openWithFile(file: TFile) {
		this.canvasFile = file;
		try {
			this.parsed = await this.parser.parseCanvasFile(file);
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
