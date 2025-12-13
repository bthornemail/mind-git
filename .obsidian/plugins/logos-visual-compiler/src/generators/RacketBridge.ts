import { AST } from '../types/ast';
import { Notice } from 'obsidian';

export interface RacketCompilationRequest {
	ast: AST;
	options: {
		outputLanguage: 'racket' | 'scheme' | 'aal';
		includeDebugInfo: boolean;
		optimizationLevel: 0 | 1 | 2 | 3;
	};
}

export interface RacketCompilationResult {
	success: boolean;
	code?: string;
	errors?: string[];
	warnings?: string[];
	metadata: {
		compilationTime: number;
		outputLanguage: string;
		linesGenerated: number;
	};
}

export class RacketBridge {
	private serverUrl: string;
	private timeout: number;
	private isConnected: boolean = false;

	constructor(serverUrl: string = 'http://localhost:8080', timeout: number = 30000) {
		this.serverUrl = serverUrl;
		this.timeout = timeout;
	}

	async checkConnection(): Promise<boolean> {
		try {
			const controller = new AbortController();
			const timeoutId = setTimeout(() => controller.abort(), 5000);

			const response = await fetch(`${this.serverUrl}/health`, {
				method: 'GET',
				signal: controller.signal
			});

			clearTimeout(timeoutId);
			this.isConnected = response.ok;
			return this.isConnected;
		} catch (error) {
			console.error('Racket server connection failed:', error);
			this.isConnected = false;
			return false;
		}
	}

	async compileAST(request: RacketCompilationRequest): Promise<RacketCompilationResult> {
		if (!this.isConnected) {
			const connected = await this.checkConnection();
			if (!connected) {
				return {
					success: false,
					errors: ['Racket server is not available. Please start the server and try again.'],
					metadata: {
						compilationTime: 0,
						outputLanguage: request.options.outputLanguage,
						linesGenerated: 0
					}
				};
			}
		}

		try {
			const controller = new AbortController();
			const timeoutId = setTimeout(() => controller.abort(), this.timeout);

			const response = await fetch(`${this.serverUrl}/compile`, {
				method: 'POST',
				headers: {
					'Content-Type': 'application/json',
				},
				body: JSON.stringify(request),
				signal: controller.signal
			});

			clearTimeout(timeoutId);

			if (!response.ok) {
				const errorText = await response.text();
				return {
					success: false,
					errors: [`Server error: ${response.status} - ${errorText}`],
					metadata: {
						compilationTime: 0,
						outputLanguage: request.options.outputLanguage,
						linesGenerated: 0
					}
				};
			}

			const result: RacketCompilationResult = await response.json();
			return result;

		} catch (error) {
			if (error.name === 'AbortError') {
				return {
					success: false,
					errors: ['Compilation timeout - server took too long to respond'],
					metadata: {
						compilationTime: this.timeout,
						outputLanguage: request.options.outputLanguage,
						linesGenerated: 0
					}
				};
			}

			return {
				success: false,
				errors: [`Compilation failed: ${error.message}`],
				metadata: {
					compilationTime: 0,
					outputLanguage: request.options.outputLanguage,
					linesGenerated: 0
				}
			};
		}
	}

	async getServerInfo(): Promise<any> {
		try {
			const response = await fetch(`${this.serverUrl}/info`, {
				method: 'GET'
			});

			if (!response.ok) {
				return null;
			}

			return await response.json();
		} catch (error) {
			console.error('Failed to get server info:', error);
			return null;
		}
	}

	async generateCode(ast: AST): Promise<string> {
		try {
			const controller = new AbortController();
			const timeoutId = setTimeout(() => controller.abort(), this.timeout);

			const response = await fetch(`${this.serverUrl}/generate`, {
				method: 'POST',
				headers: {
					'Content-Type': 'application/json',
				},
				body: JSON.stringify(ast),
				signal: controller.signal
			});

			clearTimeout(timeoutId);

			if (!response.ok) {
				const errorText = await response.text();
				throw new Error(`Server error: ${response.status} - ${errorText}`);
			}

			const result = await response.json();
			
			if (!result.success) {
				throw new Error(result.error || 'Unknown compilation error');
			}

			return result.code || '// No code generated';

		} catch (error) {
			if (error.name === 'AbortError') {
				throw new Error('Code generation timeout - server took too long to respond');
			}

			throw new Error(`Code generation failed: ${error.message}`);
		}
	}

	async validateAST(ast: AST): Promise<{ valid: boolean; errors: string[] }> {
		try {
			const response = await fetch(`${this.serverUrl}/validate`, {
				method: 'POST',
				headers: {
					'Content-Type': 'application/json',
				},
				body: JSON.stringify({ ast })
			});

			if (!response.ok) {
				return {
					valid: false,
					errors: ['Validation endpoint not available']
				};
			}

			return await response.json();
		} catch (error) {
			return {
				valid: false,
				errors: [`Validation failed: ${error.message}`]
			};
		}
	}

	setServerUrl(url: string): void {
		this.serverUrl = url;
		this.isConnected = false;
	}

	getServerUrl(): string {
		return this.serverUrl;
	}

	isServerConnected(): boolean {
		return this.isConnected;
	}
}

// Singleton instance
let racketBridgeInstance: RacketBridge | null = null;

export function getRacketBridge(serverUrl?: string): RacketBridge {
	if (!racketBridgeInstance) {
		racketBridgeInstance = new RacketBridge(serverUrl);
	} else if (serverUrl && serverUrl !== racketBridgeInstance.getServerUrl()) {
		racketBridgeInstance.setServerUrl(serverUrl);
	}
	return racketBridgeInstance;
}
