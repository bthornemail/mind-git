import { App, TFile, Notice } from 'obsidian';
import { execSync } from 'child_process';
import { PathResolver } from '../utils/PathResolver';
import { StateManager, CompilationResult, CompilationError } from '../state/StateManager';
import { CompilationCache } from '../cache/CompilationCache';

/**
 * Debounce utility function
 */
function debounce<T extends (...args: any[]) => any>(
  func: T,
  wait: number
): (...args: Parameters<T>) => void {
  let timeout: NodeJS.Timeout;
  return (...args: Parameters<T>) => {
    clearTimeout(timeout);
    timeout = setTimeout(() => func(...args), wait);
  };
}

/**
 * CLI Integration Service
 * Handles communication with mind-git CLI, file watching, and debounced compilation
 */
export class CLIIntegration {
  private cache: CompilationCache;
  private watchers = new Map<string, () => void>();
  private debouncedCompile: (file: TFile) => Promise<void>;
  
  constructor(
    private app: App,
    private stateManager: StateManager,
    private debounceDelay = 300
  ) {
    this.cache = new CompilationCache();
    
    // Initialize debounced compilation
    this.debouncedCompile = debounce(this.performCompilation.bind(this), this.debounceDelay);
    
    // Initialize CLI status
    this.initializeCLIStatus();
  }
  
  /**
   * Initialize CLI availability status
   */
  private async initializeCLIStatus(): Promise<void> {
    try {
      const cliTest = await PathResolver.testCLI();
      this.stateManager.setCLIStatus(cliTest.available, cliTest.version);
      
      if (!cliTest.available) {
        console.warn('⚠️ CLI not available:', cliTest.error);
        new Notice('Mind-Git CLI not available. Some features may be limited.');
      }
    } catch (error) {
      console.error('Error testing CLI:', error);
      this.stateManager.setCLIStatus(false);
    }
  }
  
  /**
   * Compile canvas file using CLI
   */
  async compileCanvas(
    file: TFile, 
    options: {
      outputFormat?: 'javascript' | 'typescript' | 'racket' | 'aal';
      outputPath?: string;
      force?: boolean;
    } = {}
  ): Promise<CompilationResult> {
    const startTime = Date.now();
    
    try {
      // Set compilation status
      this.stateManager.setCurrentFile(file);
      this.stateManager.setCompilationStatus(true);
      
      // Check cache first (unless forced)
      if (!options.force) {
        const fileContent = await this.app.vault.read(file);
        const cached = this.cache.get(file.path, fileContent);
        if (cached) {
          console.log(`📋 Using cached compilation for ${file.path}`);
          this.stateManager.setCompilationResult(cached);
          return cached;
        }
      }
      
      // Prepare compilation command
      const cliCommand = PathResolver.getCLICommand();
      const canvasPath = file.path;
      
      let command = `${cliCommand} compile "${canvasPath}"`;
      
      // Add output format option
      if (options.outputFormat) {
        command += ` --format=${options.outputFormat}`;
      }
      
      // Add output path option
      if (options.outputPath) {
        command += ` --output="${options.outputPath}"`;
      }
      
      console.log(`🔧 Executing: ${command}`);
      
      // Execute CLI command
      const output = execSync(command, {
        encoding: 'utf8',
        stdio: 'pipe',
        timeout: this.stateManager.getState().compilationTimeout,
        cwd: '/home/main/devops/mind-git'
      });
      
      // Parse CLI output
      const result = await this.parseCLIOutput(output, file, options.outputFormat || 'javascript');
      
      // Cache the result
      const fileContent = await this.app.vault.read(file);
      this.cache.set(file.path, fileContent, result);
      
      // Update state
      this.stateManager.setCompilationResult(result);
      
      console.log(`✅ Compilation completed in ${Date.now() - startTime}ms`);
      return result;
      
    } catch (error) {
      const compilationError: CompilationResult = {
        success: false,
        errors: [{
          message: error.message,
          severity: 'error'
        }],
        timestamp: Date.now(),
        source: 'cli'
      };
      
      this.stateManager.setCompilationResult(compilationError);
      
      console.error('❌ CLI compilation failed:', error);
      new Notice(`Compilation failed: ${error.message}`);
      
      return compilationError;
    }
  }
  
  /**
   * Parse CLI output into CompilationResult
   */
  private async parseCLIOutput(
    output: string, 
    file: TFile, 
    outputFormat: string
  ): Promise<CompilationResult> {
    try {
      // Try to parse as JSON first (enhanced CLI output)
      if (output.trim().startsWith('{')) {
        const jsonOutput = JSON.parse(output);
        return {
          success: jsonOutput.success || true,
          code: jsonOutput.code,
          metadata: {
            nodes_processed: jsonOutput.nodes_processed || 0,
            edges_processed: jsonOutput.edges_processed || 0,
            compilation_time: jsonOutput.compilation_time || '0ms',
            verification_passed: jsonOutput.verification_passed,
            output_format: outputFormat
          },
          errors: jsonOutput.errors || [],
          timestamp: Date.now(),
          source: 'cli'
        };
      }
      
      // Parse simple CLI output (current implementation)
      const lines = output.split('\n');
      const code = lines.filter(line => 
        line.startsWith('//') || line.startsWith('console.log') || line.includes('Hello from CanvasL')
      ).join('\n');
      
      // Extract metadata from output
      const nodesMatch = output.match(/Found (\d+) nodes/);
      const edgesMatch = output.match(/(\d+) edges/);
      
      return {
        success: true,
        code: code || output,
        metadata: {
          nodes_processed: parseInt(nodesMatch?.[1] || '0'),
          edges_processed: parseInt(edgesMatch?.[1] || '0'),
          compilation_time: '<100ms',
          output_format: outputFormat
        },
        errors: [],
        timestamp: Date.now(),
        source: 'cli'
      };
      
    } catch (error) {
      return {
        success: true,
        code: output,
        metadata: {
          nodes_processed: 0,
          edges_processed: 0,
          compilation_time: 'unknown',
          output_format: outputFormat
        },
        errors: [{
          message: `Warning: Could not parse CLI output: ${error.message}`,
          severity: 'warning'
        }],
        timestamp: Date.now(),
        source: 'cli'
      };
    }
  }
  
  /**
   * Start watching a file for changes
   */
  startWatching(file: TFile, onCompile: (result: CompilationResult) => void): void {
    if (this.watchers.has(file.path)) {
      return; // Already watching
    }
    
    // Create file change handler
    const handleFileChange = async (changedFile: TFile) => {
      if (changedFile.path === file.path) {
        console.log(`📁 File changed: ${file.path}`);
        
        // Update file modification time
        this.stateManager.updateFileModified(file.path);
        
        // Trigger debounced compilation
        this.debouncedCompile(file);
      }
    };
    
    // Register file change listener
    const unregister = this.app.vault.on('modify', handleFileChange);
    this.watchers.set(file.path, unregister);
    
    // Add to state
    this.stateManager.addWatchedFile(file.path);
    
    console.log(`👁️ Started watching: ${file.path}`);
  }
  
  /**
   * Stop watching a file
   */
  stopWatching(file: TFile): void {
    const unregister = this.watchers.get(file.path);
    if (unregister) {
      unregister();
      this.watchers.delete(file.path);
      this.stateManager.removeWatchedFile(file.path);
      console.log(`👁️ Stopped watching: ${file.path}`);
    }
  }
  
  /**
   * Stop watching all files
   */
  stopWatchingAll(): void {
    for (const [filePath, unregister] of this.watchers) {
      unregister();
    }
    this.watchers.clear();
    
    // Clear state
    const state = this.stateManager.getState();
    for (const filePath of state.watchedFiles) {
      this.stateManager.removeWatchedFile(filePath);
    }
    
    console.log('👁️ Stopped watching all files');
  }
  
  /**
   * Perform actual compilation (used by debounced function)
   */
  private async performCompilation(file: TFile): Promise<void> {
    try {
      const result = await this.compileCanvas(file);
      
      // Notify callback if provided
      // This could be enhanced to pass callbacks to the service
      
    } catch (error) {
      console.error('Debounced compilation failed:', error);
    }
  }
  
  /**
   * Get cache statistics
   */
  getCacheStats() {
    return this.cache.getStats();
  }
  
  /**
   * Clear compilation cache
   */
  clearCache(): void {
    this.cache.clear();
    console.log('🗑️ Compilation cache cleared');
  }
  
  /**
   * Force cache cleanup
   */
  cleanupCache(): number {
    const removed = this.cache.forceCleanup();
    console.log(`🧹 Cache cleanup removed ${removed} entries`);
    return removed;
  }
  
  /**
   * Test CLI availability
   */
  async testCLI(): Promise<{ available: boolean; version?: string; error?: string }> {
    return PathResolver.testCLI();
  }
  
  /**
   * Get supported output formats
   */
  getSupportedFormats(): string[] {
    return ['javascript', 'typescript', 'racket', 'aal'];
  }
  
  /**
   * Check if file is being watched
   */
  isWatching(file: TFile): boolean {
    return this.watchers.has(file.path);
  }
  
  /**
   * Get list of watched files
   */
  getWatchedFiles(): string[] {
    return Array.from(this.watchers.keys());
  }
  
  /**
   * Dispose of resources
   */
  dispose(): void {
    this.stopWatchingAll();
    this.cache.clear();
  }
}