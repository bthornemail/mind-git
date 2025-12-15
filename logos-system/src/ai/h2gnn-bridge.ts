// H²GNN Intelligence Bridge
// Connects mind-git spatial programming to hyperbolic geometric neural networks

export interface HyperbolicEmbedding {
  id: string;
  coordinates: number[]; // Hyperbolic space coordinates
  curvature: number;
  confidence: number;
}

export interface CanvasPattern {
  type: 'node_cluster' | 'connection_pattern' | 'flow_structure' | 'topological_feature';
  embedding: HyperbolicEmbedding;
  frequency: number;
  success_rate: number;
  metadata: any;
}

export interface AISuggestion {
  type: 'node_addition' | 'connection_optimization' | 'pattern_completion' | 'error_prevention';
  confidence: number;
  reasoning: string;
  canvas_position?: { x: number, y: number, z: number };
  suggested_elements: any[];
  expected_improvement: string;
}

export interface H2GNNConfig {
  endpoint: string;
  apiKey?: string;
  model: 'poincare' | 'lorentz' | 'hyperbolic';
  dimensions: number;
  curvature: number;
}

export class H2GNNBridge {
  private config: H2GNNConfig;
  private patternCache: Map<string, CanvasPattern> = new Map();
  private learningHistory: CanvasPattern[] = [];

  constructor(config: H2GNNConfig) {
    this.config = config;
  }

  /**
   * Convert canvas nodes to hyperbolic embeddings
   */
  async embedCanvas(canvas: any): Promise<HyperbolicEmbedding[]> {
    try {
      const response = await fetch(`${this.config.endpoint}/embed`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
          ...(this.config.apiKey && { 'Authorization': `Bearer ${this.config.apiKey}` })
        },
        body: JSON.stringify({
          nodes: canvas.nodes || [],
          edges: canvas.edges || [],
          model: this.config.model,
          dimensions: this.config.dimensions,
          curvature: this.config.curvature
        })
      });

      if (!response.ok) {
        throw new Error(`H²GNN embedding failed: ${response.statusText}`);
      }

      const result = await response.json();
      return result.embeddings || [];
    } catch (error) {
      console.warn('H²GNN embedding failed, using fallback:', error);
      return this.fallbackEmbedding(canvas);
    }
  }

  /**
   * Learn patterns from canvas structure
   */
  async learnFromCanvas(canvas: any, outcome: 'success' | 'error' | 'warning'): Promise<void> {
    const embeddings = await this.embedCanvas(canvas);
    const patterns = this.extractPatterns(canvas, embeddings);

    for (const pattern of patterns) {
      const key = this.patternKey(pattern);
      const existing = this.patternCache.get(key);

      if (existing) {
        // Update existing pattern
        existing.frequency += 1;
        if (outcome === 'success') {
          existing.success_rate = (existing.success_rate * 0.9) + (1.0 * 0.1);
        } else {
          existing.success_rate = (existing.success_rate * 0.9) + (0.0 * 0.1);
        }
      } else {
        // New pattern
        pattern.frequency = 1;
        pattern.success_rate = outcome === 'success' ? 1.0 : 0.0;
        this.patternCache.set(key, pattern);
      }

      this.learningHistory.push(pattern);
    }
  }

  /**
   * Generate AI suggestions for canvas improvement
   */
  async generateSuggestions(canvas: any): Promise<AISuggestion[]> {
    const embeddings = await this.embedCanvas(canvas);
    const currentPatterns = this.extractPatterns(canvas, embeddings);
    const suggestions: AISuggestion[] = [];

    // Analyze for missing connections
    const connectionSuggestions = this.suggestConnections(canvas, embeddings);
    suggestions.push(...connectionSuggestions);

    // Analyze for pattern completion
    const patternSuggestions = this.suggestPatternCompletion(currentPatterns);
    suggestions.push(...patternSuggestions);

    // Analyze for error prevention
    const errorSuggestions = this.suggestErrorPrevention(canvas);
    suggestions.push(...errorSuggestions);

    // Sort by confidence and return top suggestions
    return suggestions
      .sort((a, b) => b.confidence - a.confidence)
      .slice(0, 5); // Top 5 suggestions
  }

  /**
   * Suggest optimal connections based on hyperbolic distance
   */
  private suggestConnections(canvas: any, embeddings: HyperbolicEmbedding[]): AISuggestion[] {
    const suggestions: AISuggestion[] = [];
    const nodes = canvas.nodes || [];
    
    if (nodes.length < 2) return suggestions;

    // Calculate hyperbolic distances between all node pairs
    for (let i = 0; i < embeddings.length; i++) {
      for (let j = i + 1; j < embeddings.length; j++) {
        const distance = this.hyperbolicDistance(embeddings[i], embeddings[j]);
        
        // Suggest connection if nodes are close in hyperbolic space but not connected
        if (distance < 0.5 && !this.areConnected(canvas, i, j)) {
          suggestions.push({
            type: 'connection_optimization',
            confidence: 0.8 - distance,
            reasoning: `Nodes are close in hyperbolic space (distance: ${distance.toFixed(3)}) but not connected`,
            suggested_elements: [
              {
                type: 'edge',
                from: nodes[i].id,
                to: nodes[j].id,
                style: 'suggested'
              }
            ],
            expected_improvement: 'Improved information flow and reduced path length'
          });
        }
      }
    }

    return suggestions;
  }

  /**
   * Suggest completion of partial patterns
   */
  private suggestPatternCompletion(currentPatterns: CanvasPattern[]): AISuggestion[] {
    const suggestions: AISuggestion[] = [];

    for (const pattern of currentPatterns) {
      // Find similar successful patterns in history
      const similarPatterns = this.learningHistory.filter(p => 
        p.type === pattern.type && 
        p.success_rate > 0.8 &&
        this.patternSimilarity(p, pattern) > 0.7
      );

      if (similarPatterns.length > 0) {
        suggestions.push({
          type: 'pattern_completion',
          confidence: 0.7,
          reasoning: `Similar successful patterns found (${similarPatterns.length} matches)`,
          suggested_elements: this.generateCompletionElements(pattern, similarPatterns),
          expected_improvement: 'Pattern completion based on successful similar structures'
        });
      }
    }

    return suggestions;
  }

  /**
   * Suggest error prevention based on topological analysis
   */
  private suggestErrorPrevention(canvas: any): AISuggestion[] {
    const suggestions: AISuggestion[] = [];
    
    // Import scheme theory for topological analysis
    const { computeH1, detectCycles, getConnectedComponents } = require('../scheme-theory/compute-h1.ts');
    
    const h1 = computeH1(canvas);
    const hasCycles = detectCycles(canvas);
    const components = getConnectedComponents(canvas);

    // Warn about excessive complexity
    if (h1 > 5) {
      suggestions.push({
        type: 'error_prevention',
        confidence: 0.9,
        reasoning: `High cyclomatic complexity detected (H¹ = ${h1}). Consider simplifying structure.`,
        expected_improvement: 'Reduced complexity and improved maintainability'
      });
    }

    // Suggest connecting disconnected components
    if (components.length > 1) {
      suggestions.push({
        type: 'connection_optimization',
        confidence: 0.8,
        reasoning: `${components.length} disconnected components detected. Consider adding bridges.`,
        expected_improvement: 'Improved connectivity and information flow'
      });
    }

    return suggestions;
  }

  /**
   * Extract patterns from canvas structure
   */
  private extractPatterns(canvas: any, embeddings: HyperbolicEmbedding[]): CanvasPattern[] {
    const patterns: CanvasPattern[] = [];
    const nodes = canvas.nodes || [];
    const edges = canvas.edges || [];

    // Node clusters (groups of closely positioned nodes)
    const clusters = this.identifyClusters(embeddings);
    for (const cluster of clusters) {
      patterns.push({
        type: 'node_cluster',
        embedding: cluster.centroid,
        frequency: 0,
        success_rate: 0,
        metadata: { size: cluster.nodes.length, density: cluster.density }
      });
    }

    // Connection patterns
    const connectionPatterns = this.identifyConnectionPatterns(edges);
    for (const connPattern of connectionPatterns) {
      patterns.push({
        type: 'connection_pattern',
        embedding: connPattern.embedding,
        frequency: 0,
        success_rate: 0,
        metadata: connPattern
      });
    }

    return patterns;
  }

  /**
   * Identify clusters in hyperbolic space
   */
  private identifyClusters(embeddings: HyperbolicEmbedding[]): Array<{centroid: HyperbolicEmbedding, nodes: number[], density: number}> {
    // Simple clustering based on hyperbolic distance
    const clusters: Array<{centroid: HyperbolicEmbedding, nodes: number[], density: number}> = [];
    const visited = new Set<number>();

    for (let i = 0; i < embeddings.length; i++) {
      if (visited.has(i)) continue;

      const cluster = { nodes: [i] };
      for (let j = i + 1; j < embeddings.length; j++) {
        if (!visited.has(j) && this.hyperbolicDistance(embeddings[i], embeddings[j]) < 0.3) {
          cluster.nodes.push(j);
          visited.add(j);
        }
      }

      if (cluster.nodes.length > 1) {
        const centroid = this.calculateCentroid(cluster.nodes.map(idx => embeddings[idx]));
        clusters.push({
          centroid,
          nodes: cluster.nodes,
          density: cluster.nodes.length / embeddings.length
        });
      }

      visited.add(i);
    }

    return clusters;
  }

  /**
   * Calculate hyperbolic distance between two embeddings
   */
  private hyperbolicDistance(a: HyperbolicEmbedding, b: HyperbolicEmbedding): number {
    // Poincaré disk model distance
    const euclideanDist = Math.sqrt(
      a.coordinates.reduce((sum, coord, i) => sum + Math.pow(coord - b.coordinates[i], 2), 0)
    );
    
    const normA = Math.sqrt(a.coordinates.reduce((sum, coord) => sum + coord * coord, 0));
    const normB = Math.sqrt(b.coordinates.reduce((sum, coord) => sum + coord * coord, 0));
    
    const numerator = 2 * euclideanDist * euclideanDist;
    const denominator = (1 - normA * normA) * (1 - normB * normB);
    
    return Math.acosh(1 + numerator / denominator);
  }

  /**
   * Calculate centroid of embeddings
   */
  private calculateCentroid(embeddings: HyperbolicEmbedding[]): HyperbolicEmbedding {
    const dimensions = embeddings[0].coordinates.length;
    const centroid = new Array(dimensions).fill(0);
    
    for (const embedding of embeddings) {
      for (let i = 0; i < dimensions; i++) {
        centroid[i] += embedding.coordinates[i];
      }
    }
    
    for (let i = 0; i < dimensions; i++) {
      centroid[i] /= embeddings.length;
    }
    
    return {
      id: 'centroid',
      coordinates: centroid,
      curvature: embeddings[0].curvature,
      confidence: embeddings.reduce((sum, e) => sum + e.confidence, 0) / embeddings.length
    };
  }

  /**
   * Fallback embedding when H²GNN service is unavailable
   */
  private fallbackEmbedding(canvas: any): HyperbolicEmbedding[] {
    const nodes = canvas.nodes || [];
    return nodes.map((node: any, index: number) => ({
      id: node.id,
      coordinates: [
        (node.x || 0) / 1000, // Normalize to [-1, 1]
        (node.y || 0) / 1000,
        Math.sin(index * 0.1) // Add some dimensionality
      ],
      curvature: -1, // Hyperbolic curvature
      confidence: 0.5 // Lower confidence for fallback
    }));
  }

  /**
   * Helper methods
   */
  private areConnected(canvas: any, i: number, j: number): boolean {
    const edges = canvas.edges || [];
    const nodes = canvas.nodes || [];
    
    return edges.some((edge: any) => 
      (edge.from === nodes[i].id && edge.to === nodes[j].id) ||
      (edge.from === nodes[j].id && edge.to === nodes[i].id)
    );
  }

  private patternKey(pattern: CanvasPattern): string {
    return `${pattern.type}_${pattern.embedding.coordinates.slice(0, 3).join('_')}`;
  }

  private patternSimilarity(a: CanvasPattern, b: CanvasPattern): number {
    if (a.type !== b.type) return 0;
    return 1 - this.hyperbolicDistance(a.embedding, b.embedding);
  }

  private identifyConnectionPatterns(edges: any[]): any[] {
    // Simple pattern detection - can be enhanced
    const patterns = [];
    
    // Look for common connection patterns (stars, chains, cycles)
    const nodeDegrees = new Map<string, number>();
    edges.forEach(edge => {
      nodeDegrees.set(edge.from, (nodeDegrees.get(edge.from) || 0) + 1);
      nodeDegrees.set(edge.to, (nodeDegrees.get(edge.to) || 0) + 1);
    });

    // Star pattern detection
    const stars = Array.from(nodeDegrees.entries()).filter(([_, degree]) => degree > 3);
    if (stars.length > 0) {
      patterns.push({
        type: 'star',
        count: stars.length,
        embedding: { id: 'star', coordinates: [0.5, 0.5, 0.5], curvature: -1, confidence: 0.7 }
      });
    }

    return patterns;
  }

  private generateCompletionElements(pattern: CanvasPattern, similarPatterns: CanvasPattern[]): any[] {
    // Generate elements to complete the pattern based on similar successful patterns
    return similarPatterns[0]?.metadata?.suggested_elements || [];
  }

  private acosh(x: number): number {
    return Math.log(x + Math.sqrt(x * x - 1));
  }
}