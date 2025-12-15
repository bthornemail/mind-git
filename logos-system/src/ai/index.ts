// AI Module Main Export
// Integrates H²GNN intelligence, canvas learning, and suggestion engine

export * from './h2gnn-bridge';
export * from './canvas-learning';
export * from './suggestion-engine';

import { H2GNNBridge, H2GNNConfig } from './h2gnn-bridge';
import { CanvasLearning } from './canvas-learning';
import { SuggestionEngine, SuggestionContext, SuggestionFilter } from './suggestion-engine';

export interface AIConfig {
  h2gnn: H2GNNConfig;
  learning: {
    maxSessions: number;
    retentionDays: number;
    minPatternFrequency: number;
  };
  suggestions: {
    enabled: boolean;
    autoRefresh: boolean;
    maxSuggestions: number;
    minConfidence: number;
  };
}

export class AIIntelligence {
  private h2gnnBridge: H2GNNBridge;
  private canvasLearning: CanvasLearning;
  private suggestionEngine: SuggestionEngine;
  private config: AIConfig;

  constructor(config: AIConfig) {
    this.config = config;
    this.h2gnnBridge = new H2GNNBridge(config.h2gnn);
    this.canvasLearning = new CanvasLearning();
    this.suggestionEngine = new SuggestionEngine(this.h2gnnBridge, this.canvasLearning);
  }

  /**
   * Initialize AI system with canvas
   */
  async initialize(canvas: any): Promise<void> {
    // Start learning session
    const sessionId = this.canvasLearning.startSession('initial', canvas);
    
    // Generate initial embeddings
    await this.h2gnnBridge.embedCanvas(canvas);
    
    console.log(`AI Intelligence initialized with session: ${sessionId}`);
  }

  /**
   * Get intelligent suggestions for canvas
   */
  async getSuggestions(canvas: any, context?: Partial<SuggestionContext>): Promise<any[]> {
    const fullContext: SuggestionContext = {
      canvas,
      skillLevel: 'intermediate',
      preferences: {
        suggestionStyle: 'balanced',
        showReasoning: true,
        autoApply: false
      },
      ...context
    };

    const filter: SuggestionFilter = {
      minConfidence: this.config.suggestions.minConfidence,
      types: ['node_addition', 'connection_optimization', 'pattern_completion', 'error_prevention'],
      maxSuggestions: this.config.suggestions.maxSuggestions
    };

    return this.suggestionEngine.generateSuggestions(fullContext, filter);
  }

  /**
   * Record user action for learning
   */
  recordAction(action: any): void {
    this.canvasLearning.recordAction(action);
  }

  /**
   * End learning session with outcome
   */
  endSession(outcome: 'success' | 'error' | 'warning', performance?: any): void {
    this.canvasLearning.endSession(outcome, performance);
  }

  /**
   * Apply AI suggestion to canvas
   */
  async applySuggestion(suggestionId: string, canvas: any): Promise<any> {
    // Get suggestion details (would need to store/retrieve by ID)
    const suggestion = await this.getSuggestionById(suggestionId);
    if (!suggestion) {
      throw new Error(`Suggestion not found: ${suggestionId}`);
    }

    const updatedCanvas = await this.suggestionEngine.applySuggestion(suggestion, canvas);
    
    // Record feedback
    this.suggestionEngine.recordFeedback(suggestionId, 'applied');
    
    return updatedCanvas;
  }

  /**
   * Get comprehensive AI statistics
   */
  getStatistics(): any {
    return {
      learning: this.canvasLearning.getStatistics(),
      suggestions: this.suggestionEngine.getStatistics(),
      h2gnn: {
        status: 'connected',
        model: this.config.h2gnn.model,
        dimensions: this.config.h2gnn.dimensions
      },
      overall: {
        uptime: Date.now(), // Would track actual start time
        sessionsProcessed: this.canvasLearning.getStatistics().totalSessions,
        suggestionsGenerated: this.suggestionEngine.getStatistics().totalSuggestions,
        userSatisfaction: this.suggestionEngine.getStatistics().userSatisfaction
      }
    };
  }

  /**
   * Update AI configuration
   */
  updateConfig(newConfig: Partial<AIConfig>): void {
    this.config = { ...this.config, ...newConfig };
    
    // Reinitialize components if needed
    if (newConfig.h2gnn) {
      this.h2gnnBridge = new H2GNNBridge(this.config.h2gnn);
      this.suggestionEngine = new SuggestionEngine(this.h2gnnBridge, this.canvasLearning);
    }
  }

  /**
   * Export learning data for backup/analysis
   */
  exportLearningData(): any {
    return {
      sessions: this.canvasLearning['sessions'], // Access private property for export
      patterns: this.canvasLearning['patterns'],
      statistics: this.getStatistics(),
      exportDate: new Date().toISOString()
    };
  }

  /**
   * Import learning data from backup
   */
  importLearningData(data: any): void {
    // Would implement proper data restoration
    console.log('Importing learning data:', data.exportDate);
  }

  private async getSuggestionById(suggestionId: string): Promise<any> {
    // Would implement proper suggestion storage/retrieval
    return null;
  }
}

// Factory function for easy initialization
export function createAIIntelligence(endpoint: string = 'http://localhost:8080'): AIIntelligence {
  const config: AIConfig = {
    h2gnn: {
      endpoint,
      model: 'poincare',
      dimensions: 128,
      curvature: -1
    },
    learning: {
      maxSessions: 1000,
      retentionDays: 30,
      minPatternFrequency: 3
    },
    suggestions: {
      enabled: true,
      autoRefresh: true,
      maxSuggestions: 5,
      minConfidence: 0.6
    }
  };

  return new AIIntelligence(config);
}

// Version and metadata
export const AI_MODULE_VERSION = '1.0.0';
export const AI_CAPABILITIES = {
  HYPERBOLIC_EMBEDDINGS: true,
  PATTERN_LEARNING: true,
  INTELLIGENT_SUGGESTIONS: true,
  USER_ADAPTATION: true,
  REAL_TIME_ANALYSIS: true
} as const;