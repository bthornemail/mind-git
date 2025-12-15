// AI-Enhanced Compiler Integration
// Integrates AI intelligence into the AAL compilation pipeline

import { AALCanvasCompiler, AALCanvasCompilationResult } from './aal-compiler';
import { createAIIntelligence, AIIntelligence, SuggestionContext } from '../ai';
import { analyzeCanvas } from '../scheme-theory';

export interface AIEnhancedCompilationConfig {
  enableAISuggestions: boolean;
  enableLearning: boolean;
  enableTopologicalAnalysis: boolean;
  suggestionThreshold: number;
  autoApplySuggestions: boolean;
}

export interface AIEnhancedCompilationResult extends AALCanvasCompilationResult {
  aiSuggestions?: any[];
  topologicalAnalysis?: any;
  learningMetrics?: any;
  aiOptimizations?: any[];
}

export class AIEnhancedCompiler extends AALCanvasCompiler {
  private ai: AIIntelligence;
  private aiConfig: AIEnhancedCompilationConfig;
  private compilationHistory: any[] = [];

  constructor(aiConfig: AIEnhancedCompilationConfig = {
    enableAISuggestions: true,
    enableLearning: true,
    enableTopologicalAnalysis: true,
    suggestionThreshold: 0.7,
    autoApplySuggestions: false
  }) {
    super();
    this.aiConfig = aiConfig;
    this.ai = createAIIntelligence('http://localhost:8080');
  }

  /**
   * Compile canvas with AI enhancement
   */
  async compileWithAI(canvas: any, context?: Partial<SuggestionContext>): Promise<AIEnhancedCompilationResult> {
    console.log('🧠 Starting AI-enhanced compilation...');
    
    // Initialize AI with canvas
    if (this.aiConfig.enableLearning) {
      await this.ai.initialize(canvas);
    }

    // Perform topological analysis
    let topologicalAnalysis = null;
    if (this.aiConfig.enableTopologicalAnalysis) {
      topologicalAnalysis = analyzeCanvas(canvas);
      console.log(`📊 Topological analysis: H¹=${topologicalAnalysis.h1BettiNumber}, cycles=${topologicalAnalysis.hasCycles}`);
    }

    // Generate AI suggestions
    let aiSuggestions = [];
    if (this.aiConfig.enableAISuggestions) {
      try {
        aiSuggestions = await this.ai.getSuggestions(canvas, {
          currentTask: context?.currentTask || 'algorithm_design',
          skillLevel: context?.skillLevel || 'intermediate',
          userHistory: this.getUserHistory(),
          preferences: {
            suggestionStyle: 'balanced',
            showReasoning: true,
            autoApply: this.aiConfig.autoApplySuggestions
          }
        });

        // Filter by confidence threshold
        aiSuggestions = aiSuggestions.filter(s => s.confidence >= this.aiConfig.suggestionThreshold);
        console.log(`🤖 Generated ${aiSuggestions.length} AI suggestions`);

      } catch (error) {
        console.warn('AI suggestions failed, continuing without AI:', error);
      }
    }

    // Apply AI optimizations if enabled
    let optimizedCanvas = canvas;
    if (this.aiConfig.autoApplySuggestions && aiSuggestions.length > 0) {
      optimizedCanvas = await this.applyAIOptimizations(canvas, aiSuggestions);
      console.log(`🔧 Applied ${aiSuggestions.length} AI optimizations`);
    }

    // Perform standard compilation
    const compilationResult = await this.compile(optimizedCanvas);

    // Enhance result with AI insights
    const enhancedResult: AIEnhancedCompilationResult = {
      ...compilationResult,
      aiSuggestions,
      topologicalAnalysis,
      learningMetrics: this.aiConfig.enableLearning ? this.ai.getStatistics() : null,
      aiOptimizations: this.aiConfig.autoApplySuggestions ? this.getAppliedOptimizations(canvas, optimizedCanvas) : []
    };

    // Record compilation for learning
    if (this.aiConfig.enableLearning) {
      await this.recordCompilationForLearning(canvas, enhancedResult);
    }

    console.log('✅ AI-enhanced compilation complete');
    return enhancedResult;
  }

  /**
   * Get real-time AI suggestions during editing
   */
  async getLiveSuggestions(canvas: any, editContext?: any): Promise<any[]> {
    if (!this.aiConfig.enableAISuggestions) return [];

    try {
      const suggestions = await this.ai.getSuggestions(canvas, {
        currentTask: editContext?.task || 'editing',
        skillLevel: editContext?.skillLevel || 'intermediate'
      });

      return suggestions.filter(s => s.confidence >= this.aiConfig.suggestionThreshold);
    } catch (error) {
      console.warn('Live suggestions failed:', error);
      return [];
    }
  }

  /**
   * Record user action for learning
   */
  recordUserAction(action: any): void {
    if (this.aiConfig.enableLearning) {
      this.ai.recordAction(action);
    }
  }

  /**
   * Apply AI optimizations to canvas
   */
  private async applyAIOptimizations(canvas: any, suggestions: any[]): Promise<any> {
    let optimizedCanvas = JSON.parse(JSON.stringify(canvas)); // Deep copy

    // Apply high-confidence suggestions
    const highConfidenceSuggestions = suggestions.filter(s => s.confidence >= 0.8);
    
    for (const suggestion of highConfidenceSuggestions) {
      try {
        optimizedCanvas = await this.ai.applySuggestion(suggestion.id || 'auto', optimizedCanvas);
      } catch (error) {
        console.warn('Failed to apply suggestion:', error);
      }
    }

    return optimizedCanvas;
  }

  /**
   * Get applied optimizations for reporting
   */
  private getAppliedOptimizations(original: any, optimized: any): any[] {
    const optimizations = [];
    
    // Compare nodes
    if (optimized.nodes && original.nodes) {
      const addedNodes = optimized.nodes.filter((node: any) => 
        !original.nodes.some((orig: any) => orig.id === node.id)
      );
      
      optimizations.push(...addedNodes.map((node: any) => ({
        type: 'node_added',
        element: node,
        source: 'ai_optimization'
      })));
    }

    // Compare edges
    if (optimized.edges && original.edges) {
      const addedEdges = optimized.edges.filter((edge: any) => 
        !original.edges.some((orig: any) => orig.id === edge.id)
      );
      
      optimizations.push(...addedEdges.map((edge: any) => ({
        type: 'edge_added',
        element: edge,
        source: 'ai_optimization'
      })));
    }

    return optimizations;
  }

  /**
   * Record compilation outcome for learning
   */
  private async recordCompilationForLearning(canvas: any, result: AIEnhancedCompilationResult): Promise<void> {
    if (!this.aiConfig.enableLearning) return;

    // Determine outcome based on compilation result
    let outcome: 'success' | 'error' | 'warning' = 'success';
    
    if (result.errors && result.errors.length > 0) {
      outcome = 'error';
    } else if (result.warnings && result.warnings.length > 0) {
      outcome = 'warning';
    }

    // Record performance metrics
    const performance = {
      compilationTime: result.compilationTime,
      errorCount: result.errors?.length || 0,
      warningCount: result.warnings?.length || 0,
      topologicalComplexity: result.topologicalAnalysis?.h1BettiNumber || 0
    };

    // End learning session
    this.ai.endSession(outcome, performance);

    // Store in compilation history
    this.compilationHistory.push({
      timestamp: new Date(),
      canvas: canvas,
      result,
      outcome,
      performance
    });

    // Limit history size
    if (this.compilationHistory.length > 100) {
      this.compilationHistory = this.compilationHistory.slice(-50);
    }
  }

  /**
   * Get user learning history
   */
  private getUserHistory(): any {
    return {
      compilationCount: this.compilationHistory.length,
      successRate: this.calculateSuccessRate(),
      commonPatterns: this.identifyCommonPatterns(),
      averageComplexity: this.calculateAverageComplexity()
    };
  }

  /**
   * Calculate compilation success rate
   */
  private calculateSuccessRate(): number {
    if (this.compilationHistory.length === 0) return 0;
    
    const successful = this.compilationHistory.filter(h => h.outcome === 'success').length;
    return successful / this.compilationHistory.length;
  }

  /**
   * Identify common patterns in user's work
   */
  private identifyCommonPatterns(): any[] {
    const patterns = new Map();
    
    for (const compilation of this.compilationHistory) {
      const canvas = compilation.canvas;
      const nodeCount = canvas.nodes?.length || 0;
      const edgeCount = canvas.edges?.length || 0;
      
      const pattern = `nodes_${nodeCount}_edges_${edgeCount}`;
      patterns.set(pattern, (patterns.get(pattern) || 0) + 1);
    }
    
    return Array.from(patterns.entries())
      .map(([pattern, frequency]) => ({ pattern, frequency }))
      .sort((a, b) => b.frequency - a.frequency)
      .slice(0, 5);
  }

  /**
   * Calculate average canvas complexity
   */
  private calculateAverageComplexity(): number {
    if (this.compilationHistory.length === 0) return 0;
    
    const complexities = this.compilationHistory.map(h => 
      h.result.topologicalAnalysis?.h1BettiNumber || 0
    );
    
    return complexities.reduce((sum, c) => sum + c, 0) / complexities.length;
  }

  /**
   * Get AI-enhanced compiler statistics
   */
  getAIStatistics(): any {
    return {
      compiler: {
        totalCompilations: this.compilationHistory.length,
        successRate: this.calculateSuccessRate(),
        averageComplexity: this.calculateAverageComplexity()
      },
      ai: this.aiConfig.enableLearning ? this.ai.getStatistics() : null,
      configuration: this.aiConfig
    };
  }

  /**
   * Update AI configuration
   */
  updateAIConfig(newConfig: Partial<AIEnhancedCompilationConfig>): void {
    this.aiConfig = { ...this.aiConfig, ...newConfig };
    
    if (newConfig.enableAISuggestions !== undefined || newConfig.enableLearning !== undefined) {
      this.ai.updateConfig({
        suggestions: {
          enabled: this.aiConfig.enableAISuggestions,
          autoRefresh: true,
          maxSuggestions: 5,
          minConfidence: this.aiConfig.suggestionThreshold
        }
      });
    }
  }

  /**
   * Export learning data
   */
  exportAILearningData(): any {
    if (!this.aiConfig.enableLearning) return null;
    
    return {
      compilationHistory: this.compilationHistory,
      aiLearningData: this.ai.exportLearningData(),
      statistics: this.getAIStatistics(),
      exportDate: new Date().toISOString()
    };
  }
}