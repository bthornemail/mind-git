import { App, Notice, Plugin, PluginSettingTab, Setting, TFile, Menu } from 'obsidian';
import { LogosPluginSettings, DEFAULT_SETTINGS } from './src/types/settings';
import { CompilerModal } from './src/ui/CompilerModal';
import { CanvasParser } from './src/parsers/CanvasParser';
import { StateManager } from './src/state/StateManager';
import { CLIIntegration } from './src/services/CLIIntegration';
import { PathResolver } from './src/utils/PathResolver';

export default class LogosPlugin extends Plugin {
	settings: LogosPluginSettings;
	private parser: CanvasParser;
	private stateManager: StateManager;
	private cliIntegration: CLIIntegration;

	async onload() {
		await this.loadSettings();
		this.parser = new CanvasParser();
		
		// Initialize state management
		this.stateManager = new StateManager({
			cliPath: this.settings.mindGitCliPath,
			autoCompile: this.settings.autoCompileOnFileChange,
			showErrorsInline: this.settings.errorDisplayMode === 'inline',
			preferredOutputFormat: this.settings.preferredOutputFormat,
			compilationTimeout: this.settings.cliTimeout
		});
		
		// Initialize CLI integration
		this.cliIntegration = new CLIIntegration(
			this.app,
			this.stateManager,
			this.settings.debounceDelay
		);

		console.log('Loading Logos Visual Compiler Plugin with CLI Integration');

		this.addRibbonIcon('zap', 'Compile Canvas', async (evt: MouseEvent) => {
			await this.compileActiveCanvas();
		});

		this.addCommand({
			id: 'compile-active-canvas',
			name: 'Compile Active Canvas',
			callback: async () => {
				await this.compileActiveCanvas();
			}
		});

		this.addCommand({
			id: 'compile-canvas-file',
			name: 'Compile Canvas File...',
			callback: async () => {
				await this.selectAndCompileCanvas();
			}
		});

		this.registerEvent(
			this.app.workspace.on('file-menu', (menu: Menu, file: TFile) => {
				if (file.extension === 'canvas') {
					menu.addItem((item) => {
						item
							.setTitle('🎨 Compile with Logos')
							.setIcon('zap')
							.onClick(async () => {
								await this.compileCanvas(file);
							});
					});
				}
			})
		);

		this.addSettingTab(new LogosSettingTab(this.app, this));

		// Initialize status bar
		const statusBarItemEl = this.addStatusBarItem();
		statusBarItemEl.setText('Logos Ready');
		
		// Subscribe to state changes for status updates
		this.stateManager.subscribe((state) => {
			if (state.isCompiling) {
				statusBarItemEl.setText('🔧 Compiling...');
			} else if (state.cliAvailable) {
				statusBarItemEl.setText('✅ Logos Ready');
			} else {
				statusBarItemEl.setText('⚠️ Logos Limited');
			}
		});

		new Notice('Logos Visual Compiler with CLI Integration loaded');
	}

	onunload() {
		console.log('Unloading Logos Visual Compiler Plugin');
		
		// Clean up CLI integration
		if (this.cliIntegration) {
			this.cliIntegration.dispose();
		}
	}

	async loadSettings() {
		this.settings = Object.assign({}, DEFAULT_SETTINGS, await this.loadData());
	}

	async saveSettings() {
		await this.saveData(this.settings);
	}

	private async compileActiveCanvas() {
		const activeFile = this.app.workspace.getActiveFile();
		
		if (!activeFile) {
			new Notice('No active file');
			return;
		}

		if (activeFile.extension !== 'canvas') {
			new Notice('Active file is not a canvas file');
			return;
		}

		await this.compileCanvas(activeFile);
	}

	private async selectAndCompileCanvas() {
		const canvasFiles = this.parser.findCanvasFiles(this.app.vault.getFiles());

		if (canvasFiles.length === 0) {
			new Notice('No canvas files found in vault');
			return;
		}

		if (canvasFiles.length === 1) {
			await this.compileCanvas(canvasFiles[0]);
			return;
		}

		new Notice(`Found ${canvasFiles.length} canvas files. Please open one and use "Compile Active Canvas"`);
	}

	private async compileCanvas(file: TFile) {
		try {
			if (this.settings.showDebugInfo) {
				console.log(`Compiling canvas: ${file.path}`);
			}

			const modal = new CompilerModal(
				this.app, 
				this.parser, 
				this.stateManager, 
				this.cliIntegration
			);
			await modal.openWithFile(file);

			new Notice(`Compiled: ${file.basename}`);
		} catch (error) {
			console.error('Compilation error:', error);
			new Notice(`Compilation failed: ${error.message}`);
		}
	}
}

class LogosSettingTab extends PluginSettingTab {
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
			.setDesc('URL for the Racket backend server with CanvasL mathematical foundation')
			.addText(text => text
				.setPlaceholder('http://localhost:8080')
				.setValue(this.plugin.settings.racketServerUrl)
				.onChange(async (value) => {
					this.plugin.settings.racketServerUrl = value;
					await this.plugin.saveSettings();
				}));

		new Setting(containerEl)
			.setName('Enable Racket Backend')
			.setDesc('Enable communication with Racket server for mathematical code generation')
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

		// CLI Integration Settings
		containerEl.createEl('h3', { text: '🔧 CLI Integration Settings' });

		new Setting(containerEl)
			.setName('Enable CLI Integration')
			.setDesc('Enable integration with mind-git CLI for advanced compilation features')
			.addToggle(toggle => toggle
				.setValue(this.plugin.settings.enableCliIntegration)
				.onChange(async (value) => {
					this.plugin.settings.enableCliIntegration = value;
					await this.plugin.saveSettings();
				}));

		new Setting(containerEl)
			.setName('CLI Path')
			.setDesc('Path to mind-git CLI executable (leave empty for auto-detection)')
			.addText(text => text
				.setPlaceholder('/home/main/devops/mind-git/bin/mind-git-simple.cjs')
				.setValue(this.plugin.settings.mindGitCliPath)
				.onChange(async (value) => {
					this.plugin.settings.mindGitCliPath = value;
					await this.plugin.saveSettings();
					// Clear path resolver cache to test new path
					PathResolver.clearCache();
				}));

		new Setting(containerEl)
			.setName('Preferred Output Format')
			.setDesc('Choose your preferred compilation method')
			.addDropdown(dropdown => dropdown
				.addOption('cli', 'CLI (Recommended)')
				.addOption('builtin', 'Built-in Generator')
				.addOption('racket', 'Racket Backend')
				.setValue(this.plugin.settings.preferredOutputFormat)
				.onChange(async (value) => {
					this.plugin.settings.preferredOutputFormat = value as any;
					await this.plugin.saveSettings();
				}));

		new Setting(containerEl)
			.setName('Auto-compile on File Change')
			.setDesc('Automatically recompile when canvas file is modified (with debouncing)')
			.addToggle(toggle => toggle
				.setValue(this.plugin.settings.autoCompileOnFileChange)
				.onChange(async (value) => {
					this.plugin.settings.autoCompileOnFileChange = value;
					await this.plugin.saveSettings();
				}));

		new Setting(containerEl)
			.setName('Debounce Delay (ms)')
			.setDesc('Delay before auto-compilation to prevent excessive recompilation')
			.addSlider(slider => slider
				.setLimits(100, 2000, 50)
				.setValue(this.plugin.settings.debounceDelay)
				.setDynamicTooltip()
				.onChange(async (value) => {
					this.plugin.settings.debounceDelay = value;
					await this.plugin.saveSettings();
				}));

		new Setting(containerEl)
			.setName('CLI Timeout (ms)')
			.setDesc('Maximum time to wait for CLI compilation')
			.addSlider(slider => slider
				.setLimits(5000, 60000, 1000)
				.setValue(this.plugin.settings.cliTimeout)
				.setDynamicTooltip()
				.onChange(async (value) => {
					this.plugin.settings.cliTimeout = value;
					await this.plugin.saveSettings();
				}));

		// Error Display Settings
		containerEl.createEl('h3', { text: '⚠️ Error Display Settings' });

		new Setting(containerEl)
			.setName('Error Display Mode')
			.setDesc('How to display compilation errors')
			.addDropdown(dropdown => dropdown
				.addOption('inline', 'Inline (Red Underline)')
				.addOption('console', 'Console Only')
				.addOption('both', 'Both')
				.setValue(this.plugin.settings.errorDisplayMode)
				.onChange(async (value) => {
					this.plugin.settings.errorDisplayMode = value as any;
					await this.plugin.saveSettings();
				}));

		new Setting(containerEl)
			.setName('Show Error Tooltips')
			.setDesc('Show detailed error information in tooltips')
			.addToggle(toggle => toggle
				.setValue(this.plugin.settings.showErrorTooltips)
				.onChange(async (value) => {
					this.plugin.settings.showErrorTooltips = value;
					await this.plugin.saveSettings();
				}));

		// Cache Settings
		containerEl.createEl('h3', { text: '💾 Cache Settings' });

		new Setting(containerEl)
			.setName('Enable Compilation Cache')
			.setDesc('Cache compilation results to improve performance')
			.addToggle(toggle => toggle
				.setValue(this.plugin.settings.enableCompilationCache)
				.onChange(async (value) => {
					this.plugin.settings.enableCompilationCache = value;
					await this.plugin.saveSettings();
				}));

		new Setting(containerEl)
			.setName('Max Cache Entries')
			.setDesc('Maximum number of compilation results to cache')
			.addSlider(slider => slider
				.setLimits(10, 500, 10)
				.setValue(this.plugin.settings.maxCacheEntries)
				.setDynamicTooltip()
				.onChange(async (value) => {
					this.plugin.settings.maxCacheEntries = value;
					await this.plugin.saveSettings();
				}));

		new Setting(containerEl)
			.setName('Cache Max Age (minutes)')
			.setDesc('Maximum age for cached entries before expiration')
			.addSlider(slider => slider
				.setLimits(5, 120, 5)
				.setValue(this.plugin.settings.cacheMaxAge / 60000)
				.setDynamicTooltip()
				.onChange(async (value) => {
					this.plugin.settings.cacheMaxAge = value * 60000;
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