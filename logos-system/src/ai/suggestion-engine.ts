// AI Suggestion Engine
// Integrates H²GNN insights and learning patterns to provide intelligent suggestions

import { H2GNNBridge, AISuggestion } from './h2gnn-bridge';
import { CanvasLearning } from './canvas-learning';

export interface SuggestionContext {
  canvas: any;
  userHistory?: any;
  currentTask?: string;
  skillLevel?: 'beginner' | 'intermediate' | 'expert';
  preferences?: {
    suggestionStyle: 'conservative' | 'balanced' | 'aggressive';
    showReasoning: boolean;
    autoApply: boolean;
  };
}

export interface SuggestionFilter {
  minConfidence: number;
  types: AISuggestion['type'][];
  maxSuggestions: number;
}

export class SuggestionEngine {
  private h2gnnBridge: H2GNNBridge;
  private canvasLearning: CanvasLearning;
  private suggestionHistory: AISuggestion[] = [];
  private userFeedback: Map<string, number> = new Map();

  constructor(h2gnnBridge: H2GNNBridge, canvasLearning: CanvasLearning) {
    this.h2gnnBridge = h2gnnBridge;
    this.canvasLearning = canvasLearning;
  }

  /**
   * Generate comprehensive suggestions for canvas improvement
   */
  async generateSuggestions(context: SuggestionContext, filter?: SuggestionFilter): Promise<AISuggestion[]> {
    const allSuggestions: AISuggestion[] = [];

    // Get H²GNN suggestions (hyperbolic geometry insights)
    try {
      const h2gnnSuggestions = await this.h2gnnBridge.generateSuggestions(context.canvas);
      allSuggestions.push(...h2gnnSuggestions);
    } catch (error) {
      console.warn('H²GNN suggestions failed:', error);
    }

    // Get learning-based suggestions (user pattern analysis)
    try {
      const learningSuggestions = this.canvasLearning.getSuggestions(
        context.canvas, 
        context.userHistory
      );
      
      // Convert learning suggestions to AISuggestion format
      const convertedSuggestions = learningSuggestions.map(ls => ({
        type: ls.pattern.type.includes('error') ? 'error_prevention' : 'pattern_completion',
        confidence: ls.confidence,
        reasoning: ls.reasoning,
        suggested_elements: ls.suggestedActions || [],
        expected_improvement: 'Based on your successful patterns'
      }));
      
      allSuggestions.push(...convertedSuggestions);
    } catch (error) {
      console.warn('Learning suggestions failed:', error);
    }

    // Add contextual suggestions
    const contextualSuggestions = this.generateContextualSuggestions(context);
    allSuggestions.push(...contextualSuggestions);

    // Apply filters and ranking
    const filteredSuggestions = this.applyFilters(allSuggestions, filter);
    const rankedSuggestions = this.rankSuggestions(filteredSuggestions, context);

    return rankedSuggestions.slice(0, filter?.maxSuggestions || 5);
  }

  /**
   * Record user feedback for suggestion improvement
   */
  recordFeedback(suggestionId: string, feedback: 'helpful' | 'not_helpful' | 'applied'): void {
    const score = feedback === 'helpful' ? 1 : feedback === 'applied' ? 2 : -1;
    this.userFeedback.set(suggestionId, score);
  }

  /**
   * Apply suggestion to canvas
   */
  async applySuggestion(suggestion: AISuggestion, canvas: any): Promise<any> {
    const updatedCanvas = JSON.parse(JSON.stringify(canvas)); // Deep copy

    try {
      switch (suggestion.type) {
        case 'node_addition':
          return this.applyNodeAddition(suggestion, updatedCanvas);
        
        case 'connection_optimization':
          return this.applyConnectionOptimization(suggestion, updatedCanvas);
        
        case 'pattern_completion':
          return this.applyPatternCompletion(suggestion, updatedCanvas);
        
        case 'error_prevention':
          return this.applyErrorPrevention(suggestion, updatedCanvas);
        
        default:
          console.warn('Unknown suggestion type:', suggestion.type);
          return updatedCanvas;
      }
    } catch (error) {
      console.error('Failed to apply suggestion:', error);
      throw new Error(`Suggestion application failed: ${error.message}`);
    }
  }

  /**
   * Generate contextual suggestions based on current state
   */
  private generateContextualSuggestions(context: SuggestionContext): AISuggestion[] {
    const suggestions: AISuggestion[] = [];
    const canvas = context.canvas;
    const nodes = canvas.nodes || [];
    const edges = canvas.edges || [];

    // Beginner suggestions
    if (context.skillLevel === 'beginner') {
      if (nodes.length === 0) {
        suggestions.push({
          type: 'node_addition',
          confidence: 0.9,
          reasoning: 'Start by adding your first node to the canvas',
          suggested_elements: [
            {
              type: 'node',
              id: 'start_node',
              text: 'Start Here',
              x: 400,
              y: 300
            }
          ],
          expected_improvement: 'Get started with canvas creation'
        });
      }

      if (nodes.length === 1 && edges.length === 0) {
        suggestions.push({
          type: 'node_addition',
          confidence: 0.8,
          reasoning: 'Add another node to create connections',
          suggested_elements: [
            {
              type: 'node',
              id: 'second_node',
              text: 'Next Step',
              x: 600,
              y: 300
            }
          ],
          expected_improvement: 'Enable connection creation'
        });
      }
    }

    // Task-specific suggestions
    if (context.currentTask === 'algorithm_design') {
      suggestions.push({
        type: 'pattern_completion',
        confidence: 0.7,
        reasoning: 'Consider adding input/output nodes for your algorithm',
        suggested_elements: [
          { type: 'node', role: 'input', style: 'input' },
          { type: 'node', role: 'output', style: 'output' }
        ],
        expected_improvement: 'Clear algorithm boundaries'
      });
    }

    // Performance suggestions
    if (nodes.length > 50) {
      suggestions.push({
        type: 'error_prevention',
        confidence: 0.8,
        reasoning: 'Large canvas detected. Consider organizing into modules.',
        expected_improvement: 'Improved performance and maintainability'
      });
    }

    return suggestions;
  }

  /**
   * Apply node addition suggestion
   */
  private applyNodeAddition(suggestion: AISuggestion, canvas: any): any {
    if (!canvas.nodes) canvas.nodes = [];
    
    for (const element of suggestion.suggested_elements) {
      if (element.type === 'node') {
        canvas.nodes.push({
          ...element,
          id: element.id || `node_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
          created: new Date().toISOString(),
          source: 'ai_suggestion'
        });
      }
    }

    return canvas;
  }

  /**
   * Apply connection optimization suggestion
   */
  private applyConnectionOptimization(suggestion: AISuggestion, canvas: any): any {
    if (!canvas.edges) canvas.edges = [];
    
    for (const element of suggestion.suggested_elements) {
      if (element.type === 'edge') {
        canvas.edges.push({
          ...element,
          id: element.id || `edge_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`,
          created: new Date().toISOString(),
          source: 'ai_suggestion',
          style: element.style || 'suggested'
        });
      }
    }

    return canvas;
  }

  /**
   * Apply pattern completion suggestion
   */
  private applyPatternCompletion(suggestion: AISuggestion, canvas: any): any {
    // Apply suggested elements based on pattern
    for (const element of suggestion.suggested_elements) {
      if (element.type === 'node') {
        if (!canvas.nodes) canvas.nodes = [];
        canvas.nodes.push({
          ...element,
          id: element.id || `pattern_node_${Date.now()}`,
          source: 'ai_pattern_completion'
        });
      } else if (element.type === 'edge') {
        if (!canvas.edges) canvas.edges = [];
        canvas.edges.push({
          ...element,
          id: element.id || `pattern_edge_${Date.now()}`,
          source: 'ai_pattern_completion'
        });
      }
    }

    return canvas;
  }

  /**
   * Apply error prevention suggestion
   */
  private applyErrorPrevention(suggestion: AISuggestion, canvas: any): any {
    // Error prevention suggestions are typically warnings, not modifications
    // But we can add helpful annotations
    if (!canvas.annotations) canvas.annotations = [];
    
    canvas.annotations.push({
      id: `warning_${Date.now()}`,
      type: 'warning',
      message: suggestion.reasoning,
      confidence: suggestion.confidence,
      created: new Date().toISOString(),
      source: 'ai_error_prevention'
    });

    return canvas;
  }

  /**
   * Apply filters to suggestions
   */
  private applyFilters(suggestions: AISuggestion[], filter?: SuggestionFilter): AISuggestion[] {
    if (!filter) return suggestions;

    return suggestions.filter(suggestion => {
      // Confidence filter
      if (suggestion.confidence < filter.minConfidence) return false;
      
      // Type filter
      if (filter.types.length > 0 && !filter.types.includes(suggestion.type)) return false;
      
      return true;
    });
  }

  /**
   * Rank suggestions based on multiple factors
   */
  private rankSuggestions(suggestions: AISuggestion[], context: SuggestionContext): AISuggestion[] {
    return suggestions.map(suggestion => {
      let score = suggestion.confidence;

      // Boost based on user feedback history
      const feedbackScore = this.getAverageFeedbackScore(suggestion.type);
      score += feedbackScore * 0.2;

      // Boost based on skill level
      if (context.skillLevel === 'beginner' && suggestion.type === 'node_addition') {
        score += 0.1;
      } else if (context.skillLevel === 'expert' && suggestion.type === 'pattern_completion') {
        score += 0.1;
      }

      // Boost based on current task
      if (context.currentTask && this.isRelevantToTask(suggestion, context.currentTask)) {
        score += 0.15;
      }

      // Apply user preference weighting
      if (context.preferences) {
        switch (context.preferences.suggestionStyle) {
          case 'conservative':
            if (suggestion.type === 'error_prevention') score += 0.1;
            break;
          case 'aggressive':
            if (suggestion.type === 'pattern_completion') score += 0.1;
            break;
        }
      }

      return { ...suggestion, _rankingScore: score };
    }).sort((a, b) => (b as any)._rankingScore - (a as any)._rankingScore);
  }

  /**
   * Check if suggestion is relevant to current task
   */
  private isRelevantToTask(suggestion: AISuggestion, task: string): boolean {
    const taskRelevance: Record<string, AISuggestion['type'][]> = {
      'algorithm_design': ['pattern_completion', 'node_addition'],
      'debugging': ['error_prevention', 'connection_optimization'],
      'optimization': ['connection_optimization', 'pattern_completion'],
      'learning': ['node_addition', 'pattern_completion']
    };

    return taskRelevance[task]?.includes(suggestion.type) || false;
  }

  /**
   * Get average feedback score for suggestion type
   */
  private getAverageFeedbackScore(type: AISuggestion['type']): number {
    const typeFeedback = Array.from(this.userFeedback.entries())
      .filter(([id]) => id.includes(type))
      .map(([, score]) => score);
    
    if (typeFeedback.length === 0) return 0;
    return typeFeedback.reduce((sum, score) => sum + score, 0) / typeFeedback.length;
  }

  /**
   * Get suggestion engine statistics
   */
  getStatistics(): any {
    const totalSuggestions = this.suggestionHistory.length;
    const appliedSuggestions = Array.from(this.userFeedback.values())
      .filter(score => score > 0).length;
    
    return {
      totalSuggestions,
      applicationRate: totalSuggestions > 0 ? appliedSuggestions / totalSuggestions : 0,
      averageConfidence: totalSuggestions > 0 ? 
        this.suggestionHistory.reduce((sum, s) => sum + s.confidence, 0) / totalSuggestions : 0,
      typeDistribution: this.getSuggestionTypeDistribution(),
      userSatisfaction: this.calculateUserSatisfaction()
    };
  }

  private getSuggestionTypeDistribution(): Record<string, number> {
    const distribution: Record<string, number> = {};
    
    for (const suggestion of this.suggestionHistory) {
      distribution[suggestion.type] = (distribution[suggestion.type] || 0) + 1;
    }
    
    return distribution;
  }

  private calculateUserSatisfaction(): number {
    const feedbackScores = Array.from(this.userFeedback.values());
    if (feedbackScores.length === 0) return 0;
    
    return feedbackScores.reduce((sum, score) => sum + Math.max(0, score), 0) / feedbackScores.length;
  }
}