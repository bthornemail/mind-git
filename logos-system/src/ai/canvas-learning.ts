// Canvas Learning System
// Learns from user patterns and improves suggestions over time

export interface LearningSession {
  id: string;
  startTime: Date;
  endTime?: Date;
  canvasState: any;
  actions: CanvasAction[];
  outcome: 'success' | 'error' | 'warning' | 'aborted';
  performance: PerformanceMetrics;
}

export interface CanvasAction {
  type: 'node_add' | 'node_remove' | 'edge_add' | 'edge_remove' | 'node_move' | 'compile';
  timestamp: Date;
  elementId?: string;
  properties?: any;
  userIntent?: string;
}

export interface PerformanceMetrics {
  compilationTime?: number;
  errorCount: number;
  warningCount: number;
  topologicalComplexity: number;
  userSatisfaction?: number; // 1-5 rating
}

export interface LearnedPattern {
  id: string;
  pattern: any;
  frequency: number;
  successRate: number;
  averageTime: number;
  context: any;
  lastSeen: Date;
}

export class CanvasLearning {
  private sessions: LearningSession[] = [];
  private patterns: Map<string, LearnedPattern> = new Map();
  private currentSession?: LearningSession;

  /**
   * Start a new learning session
   */
  startSession(canvasId: string, initialCanvasState: any): string {
    const sessionId = `session_${Date.now()}_${Math.random().toString(36).substr(2, 9)}`;
    
    this.currentSession = {
      id: sessionId,
      startTime: new Date(),
      canvasState: JSON.parse(JSON.stringify(initialCanvasState)),
      actions: [],
      outcome: 'aborted',
      performance: {
        errorCount: 0,
        warningCount: 0,
        topologicalComplexity: 0
      }
    };

    this.sessions.push(this.currentSession);
    return sessionId;
  }

  /**
   * Record an action in the current session
   */
  recordAction(action: Omit<CanvasAction, 'timestamp'>): void {
    if (!this.currentSession) return;

    this.currentSession.actions.push({
      ...action,
      timestamp: new Date()
    });

    // Update canvas state
    this.applyActionToCanvas(this.currentSession.canvasState, action);
  }

  /**
   * End the current session with outcome
   */
  endSession(outcome: 'success' | 'error' | 'warning', performance?: Partial<PerformanceMetrics>): void {
    if (!this.currentSession) return;

    this.currentSession.endTime = new Date();
    this.currentSession.outcome = outcome;
    
    if (performance) {
      this.currentSession.performance = {
        ...this.currentSession.performance,
        ...performance
      };
    }

    // Learn from this session
    this.learnFromSession(this.currentSession);
    
    this.currentSession = undefined;
  }

  /**
   * Get suggestions based on learned patterns
   */
  getSuggestions(currentCanvas: any, userContext?: any): any[] {
    const suggestions = [];
    
    // Find similar successful patterns
    const similarPatterns = this.findSimilarPatterns(currentCanvas);
    
    for (const pattern of similarPatterns) {
      if (pattern.successRate > 0.7) {
        suggestions.push({
          type: 'learned_pattern',
          confidence: pattern.successRate,
          pattern: pattern.pattern,
          reasoning: `Similar successful pattern found (used ${pattern.frequency} times)`,
          suggestedActions: this.generateSuggestedActions(pattern, currentCanvas)
        });
      }
    }

    // Get contextual suggestions
    const contextualSuggestions = this.getContextualSuggestions(currentCanvas, userContext);
    suggestions.push(...contextualSuggestions);

    return suggestions.sort((a, b) => b.confidence - a.confidence).slice(0, 3);
  }

  /**
   * Learn from a completed session
   */
  private learnFromSession(session: LearningSession): void {
    const patterns = this.extractPatternsFromSession(session);
    
    for (const pattern of patterns) {
      const key = this.patternKey(pattern);
      const existing = this.patterns.get(key);

      if (existing) {
        // Update existing pattern
        existing.frequency += 1;
        existing.successRate = (existing.successRate * 0.8) + 
          ((session.outcome === 'success' ? 1 : 0) * 0.2);
        existing.averageTime = (existing.averageTime * 0.8) + 
          (this.getSessionDuration(session) * 0.2);
        existing.lastSeen = new Date();
      } else {
        // New pattern
        this.patterns.set(key, {
          id: key,
          pattern,
          frequency: 1,
          successRate: session.outcome === 'success' ? 1.0 : 0.0,
          averageTime: this.getSessionDuration(session),
          context: session.canvasState,
          lastSeen: new Date()
        });
      }
    }
  }

  /**
   * Extract patterns from a session
   */
  private extractPatternsFromSession(session: LearningSession): any[] {
    const patterns = [];
    
    // Action sequence patterns
    const actionSequence = session.actions.map(a => a.type);
    if (actionSequence.length >= 3) {
      patterns.push({
        type: 'action_sequence',
        sequence: actionSequence,
        context: this.getSessionContext(session)
      });
    }

    // Structural patterns
    const structuralPatterns = this.extractStructuralPatterns(session.canvasState);
    patterns.push(...structuralPatterns);

    // Error patterns
    if (session.outcome === 'error') {
      const errorPatterns = this.extractErrorPatterns(session);
      patterns.push(...errorPatterns);
    }

    return patterns;
  }

  /**
   * Extract structural patterns from canvas
   */
  private extractStructuralPatterns(canvasState: any): any[] {
    const patterns = [];
    const nodes = canvasState.nodes || [];
    const edges = canvasState.edges || [];

    // Node count patterns
    if (nodes.length > 0) {
      patterns.push({
        type: 'node_count',
        count: nodes.length,
        density: edges.length / (nodes.length * (nodes.length - 1) / 2)
      });
    }

    // Connection patterns
    const nodeTypes = new Map();
    nodes.forEach(node => {
      const type = node.type || 'default';
      nodeTypes.set(type, (nodeTypes.get(type) || 0) + 1);
    });

    if (nodeTypes.size > 1) {
      patterns.push({
        type: 'node_type_distribution',
        distribution: Object.fromEntries(nodeTypes)
      });
    }

    return patterns;
  }

  /**
   * Extract error patterns from session
   */
  private extractErrorPatterns(session: LearningSession): any[] {
    const patterns = [];
    
    // Actions leading to errors
    const errorActions = session.actions.filter((_, index) => {
      // Check if this action was followed by errors
      const subsequentActions = session.actions.slice(index + 1);
      return subsequentActions.some(a => a.type === 'compile' && 
        session.performance.errorCount > 0);
    });

    if (errorActions.length > 0) {
      patterns.push({
        type: 'error_prone_action',
        actions: errorActions.map(a => a.type),
        context: this.getSessionContext(session)
      });
    }

    return patterns;
  }

  /**
   * Find patterns similar to current canvas
   */
  private findSimilarPatterns(currentCanvas: any): LearnedPattern[] {
    const currentPatterns = this.extractStructuralPatterns(currentCanvas);
    const similarPatterns: LearnedPattern[] = [];

    for (const pattern of this.patterns.values()) {
      const similarity = this.calculatePatternSimilarity(currentPatterns, pattern.pattern);
      if (similarity > 0.6) {
        similarPatterns.push(pattern);
      }
    }

    return similarPatterns.sort((a, b) => b.successRate - a.successRate);
  }

  /**
   * Get contextual suggestions based on user behavior
   */
  private getContextualSuggestions(canvas: any, userContext?: any): any[] {
    const suggestions = [];
    
    // Time-based suggestions
    const hour = new Date().getHours();
    if (hour >= 22 || hour <= 6) {
      suggestions.push({
        type: 'contextual',
        confidence: 0.6,
        reasoning: 'Late night coding detected - consider simplifying structure',
        suggestedActions: ['reduce_complexity', 'add_comments']
      });
    }

    // Session length suggestions
    const recentSessions = this.sessions.slice(-5);
    const avgSessionLength = recentSessions.reduce((sum, s) => 
      sum + this.getSessionDuration(s), 0) / recentSessions.length;

    if (avgSessionLength > 30 * 60 * 1000) { // 30 minutes
      suggestions.push({
        type: 'contextual',
        confidence: 0.7,
        reasoning: 'Long coding session detected - consider taking a break',
        suggestedActions: ['save_work', 'create_checkpoint']
      });
    }

    return suggestions;
  }

  /**
   * Generate suggested actions based on learned patterns
   */
  private generateSuggestedActions(pattern: LearnedPattern, currentCanvas: any): string[] {
    const actions = [];
    
    if (pattern.pattern.type === 'action_sequence') {
      // Suggest next action in successful sequence
      const currentSequence = this.getCurrentActionSequence();
      const patternSequence = pattern.pattern.sequence;
      
      for (let i = 0; i < patternSequence.length - 1; i++) {
        if (this.sequenceMatches(currentSequence, patternSequence.slice(0, i + 1))) {
          actions.push(patternSequence[i + 1]);
          break;
        }
      }
    }

    if (pattern.pattern.type === 'node_count') {
      const currentCount = (currentCanvas.nodes || []).length;
      if (currentCount < pattern.pattern.count) {
        actions.push('add_nodes');
      } else if (currentCount > pattern.pattern.count) {
        actions.push('remove_nodes');
      }
    }

    return actions;
  }

  /**
   * Helper methods
   */
  private applyActionToCanvas(canvasState: any, action: Omit<CanvasAction, 'timestamp'>): void {
    // Simple state updates - can be enhanced
    switch (action.type) {
      case 'node_add':
        if (!canvasState.nodes) canvasState.nodes = [];
        canvasState.nodes.push({ id: action.elementId, ...action.properties });
        break;
      case 'edge_add':
        if (!canvasState.edges) canvasState.edges = [];
        canvasState.edges.push({ id: action.elementId, ...action.properties });
        break;
      // Add more action types as needed
    }
  }

  private getSessionDuration(session: LearningSession): number {
    const end = session.endTime || new Date();
    return end.getTime() - session.startTime.getTime();
  }

  private getSessionContext(session: LearningSession): any {
    return {
      nodeCount: session.canvasState.nodes?.length || 0,
      edgeCount: session.canvasState.edges?.length || 0,
      actionCount: session.actions.length,
      duration: this.getSessionDuration(session)
    };
  }

  private getCurrentActionSequence(): string[] {
    return this.currentSession?.actions.map(a => a.type) || [];
  }

  private sequenceMatches(current: string[], pattern: string[]): boolean {
    if (current.length < pattern.length) return false;
    return pattern.every((action, index) => current[current.length - pattern.length + index] === action);
  }

  private calculatePatternSimilarity(current: any[], learned: any): number {
    // Simple similarity calculation - can be enhanced
    if (current.length === 0 || learned.length === 0) return 0;
    
    let matches = 0;
    for (const currPattern of current) {
      for (const learnedPattern of learned) {
        if (currPattern.type === learnedPattern.type) {
          matches++;
          break;
        }
      }
    }
    
    return matches / Math.max(current.length, learned.length);
  }

  private patternKey(pattern: any): string {
    return `${pattern.type}_${JSON.stringify(pattern).slice(0, 50)}`;
  }

  /**
   * Get learning statistics
   */
  getStatistics(): any {
    const totalSessions = this.sessions.length;
    const successfulSessions = this.sessions.filter(s => s.outcome === 'success').length;
    const totalPatterns = this.patterns.size;
    const avgSuccessRate = Array.from(this.patterns.values())
      .reduce((sum, p) => sum + p.successRate, 0) / totalPatterns || 0;

    return {
      totalSessions,
      successRate: totalSessions > 0 ? successfulSessions / totalSessions : 0,
      totalPatterns,
      avgPatternSuccessRate: avgSuccessRate,
      learningProgress: Math.min(totalSessions / 100, 1.0) // Normalize to 0-1
    };
  }
}