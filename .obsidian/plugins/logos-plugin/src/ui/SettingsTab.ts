import { App, PluginSettingTab, Setting } from 'obsidian';
import LogosPlugin from '../main';

export class LogosSettingTab extends PluginSettingTab {
	plugin: LogosPlugin;

	constructor(app: App, plugin: LogosPlugin) {
		super(app, plugin);
		this.plugin = plugin;
	}

	display(): void {
		const { containerEl } = this;

		containerEl.empty();
		containerEl.createEl('h2', { text: '🎨 Logos Visual Compiler Settings' });

		new Setting(containerEl)
			.setName('Racket Server URL')
			.setDesc('URL for the Racket backend server (future feature)')
			.addText(text => text
				.setPlaceholder('http://localhost:8080')
				.setValue(this.plugin.settings.racketServerUrl)
				.onChange(async (value) => {
					this.plugin.settings.racketServerUrl = value;
					await this.plugin.saveSettings();
				}));

		new Setting(containerEl)
			.setName('Enable Racket Backend')
			.setDesc('Enable communication with Racket server (not yet implemented)')
			.addToggle(toggle => toggle
				.setValue(this.plugin.settings.racketServerEnabled)
				.onChange(async (value) => {
					this.plugin.settings.racketServerEnabled = value;
					await this.plugin.saveSettings();
				}));

		new Setting(containerEl)
			.setName('Default Output Language')
			.setDesc('Select the default language for code generation')
			.addDropdown(dropdown => dropdown
				.addOption('typescript', 'TypeScript')
				.addOption('javascript', 'JavaScript')
				.addOption('racket', 'Racket')
				.setValue(this.plugin.settings.defaultOutputLanguage)
				.onChange(async (value) => {
					this.plugin.settings.defaultOutputLanguage = value as any;
					await this.plugin.saveSettings();
				}));

		new Setting(containerEl)
			.setName('Auto-compile on Save')
			.setDesc('Automatically compile canvas files when they are saved')
			.addToggle(toggle => toggle
				.setValue(this.plugin.settings.autoCompileOnSave)
				.onChange(async (value) => {
					this.plugin.settings.autoCompileOnSave = value;
					await this.plugin.saveSettings();
				}));

		new Setting(containerEl)
			.setName('Show Debug Info')
			.setDesc('Show detailed debug information in console')
			.addToggle(toggle => toggle
				.setValue(this.plugin.settings.showDebugInfo)
				.onChange(async (value) => {
					this.plugin.settings.showDebugInfo = value;
					await this.plugin.saveSettings();
				}));

		new Setting(containerEl)
			.setName('Output Directory')
			.setDesc('Directory where generated code will be saved')
			.addText(text => text
				.setPlaceholder('generated')
				.setValue(this.plugin.settings.outputDirectory)
				.onChange(async (value) => {
					this.plugin.settings.outputDirectory = value;
					await this.plugin.saveSettings();
				}));

		containerEl.createEl('h3', { text: 'About' });
		
		const aboutDiv = containerEl.createDiv({ cls: 'about-section' });
		aboutDiv.createEl('p', { 
			text: 'Logos Visual Compiler transforms Obsidian Canvas files into executable code through mathematical structures based on division algebras, Hopf fibrations, and E₈ lattice geometry.'
		});

		const featuresList = aboutDiv.createEl('ul');
		featuresList.createEl('li', { text: '🎨 Parse canvas files and classify nodes' });
		featuresList.createEl('li', { text: '🔗 Analyze dependencies and detect circular references' });
		featuresList.createEl('li', { text: '📊 Generate Abstract Syntax Trees (AST)' });
		featuresList.createEl('li', { text: '💻 Generate code in multiple languages' });
		featuresList.createEl('li', { text: '🚀 Connect to Racket backend for advanced compilation' });

		containerEl.createEl('h3', { text: 'Node Classification' });
		
		const classificationDiv = containerEl.createDiv({ cls: 'classification-section' });
		const classificationTable = classificationDiv.createEl('table', { cls: 'node-classification-table' });
		
		const headers = ['Prefix', 'Type', 'Assembly', 'Dimension'];
		const headerRow = classificationTable.createEl('tr');
		headers.forEach(header => {
			headerRow.createEl('th', { text: header });
		});

		const nodeTypes = [
			['#Activate:', 'activate', 'JMP/CALL', '0D→1D'],
			['#Integrate:', 'integrate', 'ADD/SUB', '1D→2D'],
			['#Transform:', 'transform', 'MUL/DIV', '2D→3D'],
			['#Propagate:', 'propagate', 'SHL/ROL', '3D→4D'],
			['#Verify:', 'verify', 'CMP/TEST', '4D→5D'],
			['#Store:', 'store', 'MOV/ST', '5D→6D'],
			['#Observe:', 'observe', 'LD/GET', '6D→7D']
		];

		nodeTypes.forEach(([prefix, type, assembly, dimension]) => {
			const row = classificationTable.createEl('tr');
			row.createEl('td', { text: prefix, cls: 'code' });
			row.createEl('td', { text: type });
			row.createEl('td', { text: assembly, cls: 'code' });
			row.createEl('td', { text: dimension });
		});
	}
}
