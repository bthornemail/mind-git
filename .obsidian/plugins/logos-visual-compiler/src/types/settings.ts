export interface LogosPluginSettings {
	// Existing Racket settings
	racketServerUrl: string;
	racketServerEnabled: boolean;
	defaultOutputLanguage: 'typescript' | 'javascript' | 'racket';
	autoCompileOnSave: boolean;
	showDebugInfo: boolean;
	outputDirectory: string;
	
	// CLI Integration settings
	mindGitCliPath: string;
	enableCliIntegration: boolean;
	cliTimeout: number;
	preferredOutputFormat: 'cli' | 'builtin' | 'racket';
	autoCompileOnFileChange: boolean;
	debounceDelay: number;
	
	// Error display settings
	errorDisplayMode: 'inline' | 'console' | 'both';
	showErrorTooltips: boolean;
	
	// Cache settings
	enableCompilationCache: boolean;
	maxCacheEntries: number;
	cacheMaxAge: number;
	
	// Template settings
	enableTemplates: boolean;
	templateDirectory: string;
}

export const DEFAULT_SETTINGS: LogosPluginSettings = {
	// Existing Racket settings
	racketServerUrl: 'http://localhost:8080',
	racketServerEnabled: false,
	defaultOutputLanguage: 'typescript',
	autoCompileOnSave: false,
	showDebugInfo: true,
	outputDirectory: 'generated',
	
	// CLI Integration settings
	mindGitCliPath: '',
	enableCliIntegration: true,
	cliTimeout: 15000,
	preferredOutputFormat: 'cli',
	autoCompileOnFileChange: false,
	debounceDelay: 300,
	
	// Error display settings
	errorDisplayMode: 'inline',
	showErrorTooltips: true,
	
	// Cache settings
	enableCompilationCache: true,
	maxCacheEntries: 100,
	cacheMaxAge: 30 * 60 * 1000, // 30 minutes
	
	// Template settings
	enableTemplates: true,
	templateDirectory: 'templates'
};
