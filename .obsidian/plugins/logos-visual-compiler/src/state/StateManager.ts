import { TFile } from 'obsidian';

/**
 * Plugin-level state management for Logos Visual Compiler
 * Centralizes state and provides reactive updates
 */

export interface CompilationResult {
  success: boolean;
  code?: string;
  metadata?: {
    nodes_processed: number;
    edges_processed: number;
    compilation_time: string;
    verification_passed?: boolean;
    output_format: string;
  };
  errors?: CompilationError[];
  timestamp: number;
  source: 'cli' | 'builtin' | 'racket';
}

export interface CompilationError {
  node_id?: string;
  message: string;
  line?: number;
  column?: number;
  severity: 'error' | 'warning';
}

export interface PluginState {
  // CLI Integration
  cliPath: string;
  cliAvailable: boolean;
  cliVersion?: string;
  
  // Current Compilation
  currentFile: TFile | null;
  lastResult: CompilationResult | null;
  isCompiling: boolean;
  
  // Settings
  autoCompile: boolean;
  showErrorsInline: boolean;
  preferredOutputFormat: 'javascript' | 'typescript' | 'racket' | 'aal';
  compilationTimeout: number;
  
  // UI State
  activeModal: string | null;
  expandedSections: Set<string>;
  
  // File Watching
  watchedFiles: Set<string>;
  lastModified: Map<string, number>;
}

export class StateManager {
  private state: PluginState;
  private listeners: Set<(state: PluginState) => void> = new Set();
  
  constructor(initialState: Partial<PluginState> = {}) {
    this.state = {
      // CLI Integration
      cliPath: '',
      cliAvailable: false,
      
      // Current Compilation
      currentFile: null,
      lastResult: null,
      isCompiling: false,
      
      // Settings
      autoCompile: false,
      showErrorsInline: true,
      preferredOutputFormat: 'typescript',
      compilationTimeout: 15000,
      
      // UI State
      activeModal: null,
      expandedSections: new Set(),
      
      // File Watching
      watchedFiles: new Set(),
      lastModified: new Map(),
      
      ...initialState
    };
  }
  
  /**
   * Subscribe to state changes
   */
  subscribe(listener: (state: PluginState) => void): () => void {
    this.listeners.add(listener);
    
    // Immediately call with current state
    listener(this.getState());
    
    // Return unsubscribe function
    return () => this.listeners.delete(listener);
  }
  
  /**
   * Get current state (immutable copy)
   */
  getState(): PluginState {
    return {
      ...this.state,
      expandedSections: new Set(this.state.expandedSections),
      watchedFiles: new Set(this.state.watchedFiles),
      lastModified: new Map(this.state.lastModified)
    };
  }
  
  /**
   * Update state with partial changes
   */
  updateState(updates: Partial<PluginState>): void {
    this.state = {
      ...this.state,
      ...updates,
      // Handle Set and Map merging
      expandedSections: updates.expandedSections || this.state.expandedSections,
      watchedFiles: updates.watchedFiles || this.state.watchedFiles,
      lastModified: updates.lastModified || this.state.lastModified
    };
    
    // Notify all listeners
    this.listeners.forEach(listener => listener(this.getState()));
  }
  
  /**
   * Update CLI availability status
   */
  setCLIStatus(available: boolean, version?: string): void {
    this.updateState({
      cliAvailable: available,
      cliVersion: version
    });
  }
  
  /**
   * Set current compilation file
   */
  setCurrentFile(file: TFile | null): void {
    this.updateState({ currentFile: file });
  }
  
  /**
   * Update compilation status
   */
  setCompilationStatus(isCompiling: boolean): void {
    this.updateState({ isCompiling });
  }
  
  /**
   * Store compilation result
   */
  setCompilationResult(result: CompilationResult): void {
    this.updateState({ 
      lastResult: result,
      isCompiling: false 
    });
  }
  
  /**
   * Add file to watch list
   */
  addWatchedFile(filePath: string): void {
    const watchedFiles = new Set(this.state.watchedFiles);
    watchedFiles.add(filePath);
    
    const lastModified = new Map(this.state.lastModified);
    lastModified.set(filePath, Date.now());
    
    this.updateState({ watchedFiles, lastModified });
  }
  
  /**
   * Remove file from watch list
   */
  removeWatchedFile(filePath: string): void {
    const watchedFiles = new Set(this.state.watchedFiles);
    watchedFiles.delete(filePath);
    
    const lastModified = new Map(this.state.lastModified);
    lastModified.delete(filePath);
    
    this.updateState({ watchedFiles, lastModified });
  }
  
  /**
   * Update file modification time
   */
  updateFileModified(filePath: string): void {
    const lastModified = new Map(this.state.lastModified);
    lastModified.set(filePath, Date.now());
    this.updateState({ lastModified });
  }
  
  /**
   * Toggle section expansion
   */
  toggleSection(sectionId: string): void {
    const expandedSections = new Set(this.state.expandedSections);
    if (expandedSections.has(sectionId)) {
      expandedSections.delete(sectionId);
    } else {
      expandedSections.add(sectionId);
    }
    this.updateState({ expandedSections });
  }
  
  /**
   * Set active modal
   */
  setActiveModal(modalId: string | null): void {
    this.updateState({ activeModal: modalId });
  }
  
  /**
   * Update settings
   */
  updateSettings(settings: Partial<PluginState>): void {
    this.updateState(settings);
  }
  
  /**
   * Get compilation errors for a specific file
   */
  getErrorsForFile(filePath: string): CompilationError[] {
    if (!this.state.lastResult || this.state.currentFile?.path !== filePath) {
      return [];
    }
    return this.state.lastResult.errors || [];
  }
  
  /**
   * Check if file has errors
   */
  fileHasErrors(filePath: string): boolean {
    return this.getErrorsForFile(filePath).some(error => error.severity === 'error');
  }
  
  /**
   * Get last successful compilation for file
   */
  getLastSuccessfulCompilation(filePath: string): CompilationResult | null {
    if (!this.state.lastResult || 
        this.state.currentFile?.path !== filePath || 
        !this.state.lastResult.success) {
      return null;
    }
    return this.state.lastResult;
  }
  
  /**
   * Reset state (useful for testing or reinitialization)
   */
  reset(): void {
    this.state = {
      // CLI Integration
      cliPath: '',
      cliAvailable: false,
      
      // Current Compilation
      currentFile: null,
      lastResult: null,
      isCompiling: false,
      
      // Settings
      autoCompile: false,
      showErrorsInline: true,
      preferredOutputFormat: 'typescript',
      compilationTimeout: 15000,
      
      // UI State
      activeModal: null,
      expandedSections: new Set(),
      
      // File Watching
      watchedFiles: new Set(),
      lastModified: new Map()
    };
    
    this.listeners.forEach(listener => listener(this.getState()));
  }
}