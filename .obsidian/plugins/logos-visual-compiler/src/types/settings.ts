export interface LogosPluginSettings {
	racketServerUrl: string;
	racketServerEnabled: boolean;
	defaultOutputLanguage: 'typescript' | 'javascript' | 'racket';
	autoCompileOnSave: boolean;
	showDebugInfo: boolean;
	outputDirectory: string;
}

export const DEFAULT_SETTINGS: LogosPluginSettings = {
	racketServerUrl: 'http://localhost:8080',
	racketServerEnabled: false,
	defaultOutputLanguage: 'typescript',
	autoCompileOnSave: false,
	showDebugInfo: true,
	outputDirectory: 'generated'
};
