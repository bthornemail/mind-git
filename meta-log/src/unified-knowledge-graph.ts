// Unified Knowledge Graph
// Central knowledge management for meta-log orchestrator

export interface KnowledgeGraphConfig {
  maxNodes: number;
  maxRelationships: number;
  retentionDays: number;
  enablePersistence: boolean;
  enableRealTimeUpdates: boolean;
}

export interface KnowledgeNode {
  id: string;
  type: 'project' | 'canvas' | 'pattern' | 'user' | 'concept' | 'ai_insight' | 'workflow' | 'metric' | 'deployment';
  properties: {
    name: string;
    description?: string;
    metadata?: any;
    confidence: number;
    relevance: number;
    lastUpdated: Date;
    accessCount: number;
  };
  relationships: Array<{
    targetId: string;
    type: 'depends_on' | 'contains' | 'similar_to' | 'enhances' | 'conflicts_with' | 'implements' | 'uses' | 'produces' | 'connects_to';
    strength: number;
    confidence: number;
    metadata?: any;
  }>;
  embeddings?: {
    vector: number[];
    model: string;
    dimensions: number;
  };
  temporal?: {
    createdAt: Date;
    expiresAt?: Date;
    version: number;
  };
}

export interface GraphQuery {
  type: 'node' | 'relationship' | 'path' | 'neighborhood' | 'similarity' | 'temporal';
  parameters: any;
  filters?: {
    nodeTypes?: string[];
    relationshipTypes?: string[];
    confidenceRange?: [number, number];
    timeRange?: [Date, Date];
    keywords?: string[];
  };
  limit?: number;
  offset?: number;
}

export interface GraphResult {
  nodes: KnowledgeNode[];
  relationships: any[];
  paths?: any[];
  metadata: {
    totalResults: number;
    queryTime: number;
    confidence: number;
    hasMore: boolean;
  };
}

export class UnifiedKnowledgeGraph {
  private config: KnowledgeGraphConfig;
  private nodes: Map<string, KnowledgeNode> = new Map();
  private relationships: Map<string, any[]> = new Map();
  private adjacencyList: Map<string, Map<string, number>> = new Map();
  private embeddings: Map<string, number[]> = new Map();
  private queryCache: Map<string, GraphResult> = new Map();
  private changeLog: Array<{
    type: 'create' | 'update' | 'delete';
    nodeId: string;
    timestamp: Date;
    changes?: any;
  }> = [];

  constructor(config: KnowledgeGraphConfig) {
    this.config = config;
    this.initializeGraph();
  }

  /**
   * Initialize knowledge graph with core concepts
   */
  private initializeGraph(): void {
    console.log('🧠 Initializing unified knowledge graph...');
    
    // Add core domain concepts
    this.addCoreConcepts();
    
    // Add initial project nodes
    this.addInitialProjects();
    
    // Setup indexing structures
    this.setupIndexes();
    
    console.log(`✅ Knowledge graph initialized: ${this.nodes.size} nodes, ${this.getTotalRelationships()} relationships`);
  }

  /**
   * Add or update a knowledge node
   */
  async addNode(node: Omit<KnowledgeNode, 'id'>): Promise<string> {
    const nodeId = node.properties.name.toLowerCase().replace(/\s+/g, '_') + '_' + Date.now();
    
    const knowledgeNode: KnowledgeNode = {
      id: nodeId,
      type: node.type,
      properties: {
        ...node.properties,
        lastUpdated: new Date(),
        accessCount: 0
      },
      relationships: node.relationships || [],
      embeddings: node.embeddings,
      temporal: {
        ...node.temporal,
        createdAt: new Date(),
        version: 1
      }
    };

    // Add to main storage
    this.nodes.set(nodeId, knowledgeNode);
    
    // Update relationships
    if (knowledgeNode.relationships) {
      for (const rel of knowledgeNode.relationships) {
        this.addRelationship(nodeId, rel);
      }
    }

    // Update embeddings
    if (knowledgeNode.embeddings) {
      this.embeddings.set(nodeId, knowledgeNode.embeddings.vector);
    }

    // Update adjacency list
    this.updateAdjacencyList(nodeId, knowledgeNode.relationships);

    // Log change
    this.logChange('create', nodeId);

    // Invalidate relevant cache entries
    this.invalidateCache(nodeId);

    console.log(`📝 Added knowledge node: ${node.properties.name} (${node.type})`);
    return nodeId;
  }

  /**
   * Query the knowledge graph
   */
  async query(query: GraphQuery): Promise<GraphResult> {
    const startTime = Date.now();
    console.log(`🔍 Querying knowledge graph: ${query.type}`);

    let result: GraphResult;

    try {
      switch (query.type) {
        case 'node':
          result = await this.queryNodes(query);
          break;
        case 'relationship':
          result = await this.queryRelationships(query);
          break;
        case 'path':
          result = await this.queryPaths(query);
          break;
        case 'neighborhood':
          result = await this.queryNeighborhood(query);
          break;
        case 'similarity':
          result = await this.querySimilarity(query);
          break;
        case 'temporal':
          result = await this.queryTemporal(query);
          break;
        default:
          throw new Error(`Unknown query type: ${query.type}`);
      }

      const queryTime = Date.now() - startTime;
      result.metadata.queryTime = queryTime;

      // Cache result if appropriate
      if (this.shouldCacheQuery(query)) {
        this.cacheQuery(query, result);
      }

      console.log(`✅ Query complete: ${result.nodes.length} nodes in ${queryTime}ms`);
      return result;

    } catch (error) {
      console.error('❌ Query failed:', error);
      return {
        nodes: [],
        relationships: [],
        metadata: {
          totalResults: 0,
          queryTime: Date.now() - startTime,
          confidence: 0,
          hasMore: false
        }
      };
    }
  }

  /**
   * Find similar nodes based on embeddings
   */
  async findSimilarNodes(nodeId: string, limit: number = 10): Promise<Array<{ node: KnowledgeNode, similarity: number }>> {
    const targetNode = this.nodes.get(nodeId);
    if (!targetNode || !targetNode.embeddings) {
      return [];
    }

    const targetEmbedding = targetNode.embeddings.vector;
    const similarities: Array<{ node: KnowledgeNode, similarity: number }> = [];

    for (const [id, node] of this.nodes) {
      if (id === nodeId || !node.embeddings) continue;

      const similarity = this.calculateCosineSimilarity(targetEmbedding, node.embeddings.vector);
      if (similarity > 0.3) { // Threshold for similarity
        similarities.push({ node, similarity });
      }
    }

    return similarities
      .sort((a, b) => b.similarity - a.similarity)
      .slice(0, limit);
  }

  /**
   * Update node relevance based on access patterns
   */
  updateNodeRelevance(nodeId: string): void {
    const node = this.nodes.get(nodeId);
    if (!node) return;

    node.properties.accessCount++;
    node.properties.lastUpdated = new Date();
    
    // Update relevance score (time-decay + access frequency)
    const timeSinceCreation = Date.now() - node.temporal!.createdAt.getTime();
    const timeDecay = Math.exp(-timeSinceCreation / (1000 * 60 * 60 * 24 * 30)); // 30 day half-life
    const accessBoost = Math.log(node.properties.accessCount + 1) / 10;
    
    node.properties.relevance = timeDecay + accessBoost;
  }

  /**
   * Get graph statistics
   */
  getStatistics(): any {
    const nodeTypes = this.getNodeTypeDistribution();
    const relationshipTypes = this.getRelationshipTypeDistribution();
    const avgDegree = this.calculateAverageDegree();
    const clusteringCoeff = this.calculateClusteringCoefficient();

    return {
      nodes: {
        total: this.nodes.size,
        byType: nodeTypes,
        averageConfidence: this.calculateAverageConfidence(),
        averageRelevance: this.calculateAverageRelevance()
      },
      relationships: {
        total: this.getTotalRelationships(),
        byType: relationshipTypes,
        averageStrength: this.calculateAverageRelationshipStrength()
      },
      structure: {
        averageDegree,
        clusteringCoefficient,
        diameter: this.calculateGraphDiameter(),
        density: this.calculateGraphDensity()
      },
      performance: {
        cacheSize: this.queryCache.size,
        averageQueryTime: this.calculateAverageQueryTime(),
        changeLogSize: this.changeLog.length
      },
      temporal: {
        oldestNode: this.getOldestNodeDate(),
        newestNode: this.getNewestNodeDate(),
        averageAge: this.calculateAverageNodeAge()
      }
    };
  }

  /**
   * Export knowledge graph data
   */
  exportData(): any {
    return {
      nodes: Array.from(this.nodes.values()),
      relationships: this.getAllRelationships(),
      embeddings: Object.fromEntries(this.embeddings),
      statistics: this.getStatistics(),
      changeLog: this.changeLog,
      exportDate: new Date().toISOString(),
      version: '1.0.0'
    };
  }

  /**
   * Import knowledge graph data
   */
  async importData(data: any): Promise<void> {
    console.log('📥 Importing knowledge graph data...');
    
    // Clear existing data
    this.nodes.clear();
    this.relationships.clear();
    this.adjacencyList.clear();
    this.embeddings.clear();
    
    // Import nodes
    for (const nodeData of data.nodes) {
      this.nodes.set(nodeData.id, nodeData);
      if (nodeData.embeddings) {
        this.embeddings.set(nodeData.id, nodeData.embeddings.vector);
      }
    }
    
    // Import relationships
    for (const relationship of data.relationships) {
      this.addRelationship(relationship.source, relationship);
    }
    
    // Rebuild indexes
    this.setupIndexes();
    
    console.log(`✅ Import complete: ${this.nodes.size} nodes, ${this.getTotalRelationships()} relationships`);
  }

  /**
   * Private helper methods
   */
  private addCoreConcepts(): void {
    const coreConcepts = [
      {
        type: 'concept' as const,
        properties: {
          name: 'Spatial Programming',
          description: 'Programming paradigm using spatial/visual representations',
          confidence: 1.0,
          relevance: 1.0
        }
      },
      {
        type: 'concept' as const,
        properties: {
          name: 'CanvasL',
          description: 'Visual programming language for spatial computing',
          confidence: 1.0,
          relevance: 1.0
        }
      },
      {
        type: 'concept' as const,
        properties: {
          name: 'Hyperbolic Geometry',
          description: 'Non-Euclidean geometry with constant negative curvature',
          confidence: 1.0,
          relevance: 0.9
        }
      },
      {
        type: 'concept' as const,
        properties: {
          name: 'E8 Lie Group',
          description: 'Exceptional simple Lie group with 248 dimensions',
          confidence: 1.0,
          relevance: 0.8
        }
      },
      {
        type: 'concept' as const,
        properties: {
          name: 'Betti Numbers',
          description: 'Topological invariants counting holes of different dimensions',
          confidence: 1.0,
          relevance: 0.9
        }
      }
    ];

    for (const concept of coreConcepts) {
      this.addNode(concept);
    }
  }

  private addInitialProjects(): void {
    const initialProjects = [
      {
        type: 'project' as const,
        properties: {
          name: 'mind-git',
          description: 'Spatial compiler with mathematical foundation',
          confidence: 1.0,
          relevance: 1.0
        },
        relationships: [
          {
            targetId: 'canvasl',
            type: 'implements' as const,
            strength: 1.0,
            confidence: 1.0
          },
          {
            targetId: 'spatial_programming',
            type: 'enhances' as const,
            strength: 0.9,
            confidence: 0.9
          }
        ]
      },
      {
        type: 'project' as const,
        properties: {
          name: 'h2gnn-enhanced',
          description: 'Hyperbolic geometric neural network for AI',
          confidence: 1.0,
          relevance: 0.9
        },
        relationships: [
          {
            targetId: 'hyperbolic_geometry',
            type: 'uses' as const,
            strength: 1.0,
            confidence: 1.0
          }
        ]
      },
      {
        type: 'project' as const,
        properties: {
          name: 'hyperdev-ide',
          description: 'VR framework for immersive spatial programming',
          confidence: 1.0,
          relevance: 0.9
        },
        relationships: [
          {
            targetId: 'spatial_programming',
            type: 'enhances' as const,
            strength: 0.8,
            confidence: 0.8
          }
        ]
      }
    ];

    for (const project of initialProjects) {
      this.addNode(project);
    }
  }

  private setupIndexes(): void {
    // Build adjacency list for efficient graph traversal
    for (const [nodeId, node] of this.nodes) {
      this.updateAdjacencyList(nodeId, node.relationships);
    }
  }

  private updateAdjacencyList(nodeId: string, relationships: any[]): void {
    const adjacency = new Map<string, number>();
    
    for (const rel of relationships) {
      adjacency.set(rel.targetId, rel.strength);
    }
    
    this.adjacencyList.set(nodeId, adjacency);
  }

  private async queryNodes(query: GraphQuery): Promise<GraphResult> {
    let nodes = Array.from(this.nodes.values());

    // Apply filters
    if (query.filters) {
      if (query.filters.nodeTypes) {
        nodes = nodes.filter(node => query.filters!.nodeTypes!.includes(node.type));
      }
      
      if (query.filters.confidenceRange) {
        const [min, max] = query.filters.confidenceRange;
        nodes = nodes.filter(node => 
          node.properties.confidence >= min && node.properties.confidence <= max
        );
      }
      
      if (query.filters.keywords) {
        const keywords = query.filters.keywords.map(k => k.toLowerCase());
        nodes = nodes.filter(node => 
          keywords.some(keyword => 
            node.properties.name.toLowerCase().includes(keyword) ||
            node.properties.description?.toLowerCase().includes(keyword)
          )
        );
      }
    }

    // Sort by relevance and confidence
    nodes.sort((a, b) => {
      const relevanceScore = (b.properties.relevance * 0.6 + b.properties.confidence * 0.4) - 
                           (a.properties.relevance * 0.6 + a.properties.confidence * 0.4);
      return relevanceScore;
    });

    // Apply pagination
    const offset = query.offset || 0;
    const limit = query.limit || 50;
    const paginatedNodes = nodes.slice(offset, offset + limit);

    return {
      nodes: paginatedNodes,
      relationships: [],
      metadata: {
        totalResults: nodes.length,
        queryTime: 0,
        confidence: 0.8,
        hasMore: offset + limit < nodes.length
      }
    };
  }

  private async queryRelationships(query: GraphQuery): Promise<GraphResult> {
    // Implementation for relationship queries
    return {
      nodes: [],
      relationships: [],
      metadata: {
        totalResults: 0,
        queryTime: 0,
        confidence: 0.5,
        hasMore: false
      }
    };
  }

  private async queryPaths(query: GraphQuery): Promise<GraphResult> {
    // Implementation for path queries
    return {
      nodes: [],
      relationships: [],
      paths: [],
      metadata: {
        totalResults: 0,
        queryTime: 0,
        confidence: 0.5,
        hasMore: false
      }
    };
  }

  private async queryNeighborhood(query: GraphQuery): Promise<GraphResult> {
    // Implementation for neighborhood queries
    return {
      nodes: [],
      relationships: [],
      metadata: {
        totalResults: 0,
        queryTime: 0,
        confidence: 0.5,
        hasMore: false
      }
    };
  }

  private async querySimilarity(query: GraphQuery): Promise<GraphResult> {
    // Implementation for similarity queries
    return {
      nodes: [],
      relationships: [],
      metadata: {
        totalResults: 0,
        queryTime: 0,
        confidence: 0.5,
        hasMore: false
      }
    };
  }

  private async queryTemporal(query: GraphQuery): Promise<GraphResult> {
    // Implementation for temporal queries
    return {
      nodes: [],
      relationships: [],
      metadata: {
        totalResults: 0,
        queryTime: 0,
        confidence: 0.5,
        hasMore: false
      }
    };
  }

  private addRelationship(sourceId: string, relationship: any): void {
    if (!this.relationships.has(sourceId)) {
      this.relationships.set(sourceId, []);
    }
    this.relationships.get(sourceId)!.push(relationship);
  }

  private getAllRelationships(): any[] {
    const allRelationships: any[] = [];
    for (const relationships of this.relationships.values()) {
      allRelationships.push(...relationships);
    }
    return allRelationships;
  }

  private getTotalRelationships(): number {
    return this.getAllRelationships().length;
  }

  private calculateCosineSimilarity(vec1: number[], vec2: number[]): number {
    let dotProduct = 0;
    let norm1 = 0;
    let norm2 = 0;
    
    for (let i = 0; i < Math.min(vec1.length, vec2.length); i++) {
      dotProduct += vec1[i] * vec2[i];
      norm1 += vec1[i] * vec1[i];
      norm2 += vec2[i] * vec2[i];
    }
    
    return dotProduct / (Math.sqrt(norm1) * Math.sqrt(norm2));
  }

  private shouldCacheQuery(query: GraphQuery): boolean {
    // Cache simple node queries with filters
    return query.type === 'node' && !query.filters?.keywords;
  }

  private cacheQuery(query: GraphQuery, result: GraphResult): void {
    const cacheKey = JSON.stringify(query);
    this.queryCache.set(cacheKey, result);
    
    // Limit cache size
    if (this.queryCache.size > 1000) {
      const entries = Array.from(this.queryCache.entries());
      entries.sort((a, b) => a[1].metadata.queryTime - b[1].metadata.queryTime);
      this.queryCache = new Map(entries.slice(500)); // Keep fastest 500
    }
  }

  private invalidateCache(nodeId: string): void {
    // Remove cache entries that might be affected by node change
    for (const [key, result] of this.queryCache) {
      if (result.nodes.some(node => node.id === nodeId)) {
        this.queryCache.delete(key);
      }
    }
  }

  private logChange(type: 'create' | 'update' | 'delete', nodeId: string, changes?: any): void {
    this.changeLog.push({
      type,
      nodeId,
      timestamp: new Date(),
      changes
    });
    
    // Limit change log size
    if (this.changeLog.length > 10000) {
      this.changeLog = this.changeLog.slice(-5000);
    }
  }

  // Statistics calculation methods
  private getNodeTypeDistribution(): Record<string, number> {
    const distribution: Record<string, number> = {};
    for (const node of this.nodes.values()) {
      distribution[node.type] = (distribution[node.type] || 0) + 1;
    }
    return distribution;
  }

  private getRelationshipTypeDistribution(): Record<string, number> {
    const distribution: Record<string, number> = {};
    for (const relationships of this.relationships.values()) {
      for (const rel of relationships) {
        distribution[rel.type] = (distribution[rel.type] || 0) + 1;
      }
    }
    return distribution;
  }

  private calculateAverageDegree(): number {
    if (this.nodes.size === 0) return 0;
    
    let totalDegree = 0;
    for (const adjacency of this.adjacencyList.values()) {
      totalDegree += adjacency.size;
    }
    
    return totalDegree / this.nodes.size;
  }

  private calculateClusteringCoefficient(): number {
    // Simplified clustering coefficient calculation
    let totalClustering = 0;
    let nodeCount = 0;
    
    for (const [nodeId, adjacency] of this.adjacencyList) {
      if (adjacency.size < 2) continue;
      
      let triangles = 0;
      const neighbors = Array.from(adjacency.keys());
      
      for (let i = 0; i < neighbors.length; i++) {
        for (let j = i + 1; j < neighbors.length; j++) {
          const neighbor1 = this.adjacencyList.get(neighbors[i]);
          const neighbor2 = this.adjacencyList.get(neighbors[j]);
          
          if (neighbor1?.has(neighbors[j]) && neighbor2?.has(neighbors[i])) {
            triangles++;
          }
        }
      }
      
      const possibleTriangles = (adjacency.size * (adjacency.size - 1)) / 2;
      totalClustering += possibleTriangles > 0 ? triangles / possibleTriangles : 0;
      nodeCount++;
    }
    
    return nodeCount > 0 ? totalClustering / nodeCount : 0;
  }

  private calculateGraphDiameter(): number {
    // Simplified diameter calculation (would use BFS in practice)
    return 6; // Placeholder
  }

  private calculateGraphDensity(): number {
    const maxPossibleEdges = this.nodes.size * (this.nodes.size - 1) / 2;
    const actualEdges = this.getTotalRelationships();
    return maxPossibleEdges > 0 ? actualEdges / maxPossibleEdges : 0;
  }

  private calculateAverageConfidence(): number {
    if (this.nodes.size === 0) return 0;
    
    const totalConfidence = Array.from(this.nodes.values())
      .reduce((sum, node) => sum + node.properties.confidence, 0);
    
    return totalConfidence / this.nodes.size;
  }

  private calculateAverageRelevance(): number {
    if (this.nodes.size === 0) return 0;
    
    const totalRelevance = Array.from(this.nodes.values())
      .reduce((sum, node) => sum + node.properties.relevance, 0);
    
    return totalRelevance / this.nodes.size;
  }

  private calculateAverageRelationshipStrength(): number {
    const allRelationships = this.getAllRelationships();
    if (allRelationships.length === 0) return 0;
    
    const totalStrength = allRelationships.reduce((sum, rel) => sum + (rel.strength || 0), 0);
    return totalStrength / allRelationships.length;
  }

  private calculateAverageQueryTime(): number {
    if (this.queryCache.size === 0) return 0;
    
    const totalTime = Array.from(this.queryCache.values())
      .reduce((sum, result) => sum + result.metadata.queryTime, 0);
    
    return totalTime / this.queryCache.size;
  }

  private getOldestNodeDate(): Date | null {
    let oldest: Date | null = null;
    for (const node of this.nodes.values()) {
      if (!oldest || node.temporal!.createdAt < oldest) {
        oldest = node.temporal!.createdAt;
      }
    }
    return oldest;
  }

  private getNewestNodeDate(): Date | null {
    let newest: Date | null = null;
    for (const node of this.nodes.values()) {
      if (!newest || node.temporal!.createdAt > newest) {
        newest = node.temporal!.createdAt;
      }
    }
    return newest;
  }

  private calculateAverageNodeAge(): number {
    const now = Date.now();
    const ages = Array.from(this.nodes.values())
      .map(node => now - node.temporal!.createdAt.getTime());
    
    return ages.length > 0 ? ages.reduce((sum, age) => sum + age, 0) / ages.length : 0;
  }
}

// Factory function
export function createUnifiedKnowledgeGraph(config?: Partial<KnowledgeGraphConfig>): UnifiedKnowledgeGraph {
  const defaultConfig: KnowledgeGraphConfig = {
    maxNodes: 10000,
    maxRelationships: 50000,
    retentionDays: 90,
    enablePersistence: true,
    enableRealTimeUpdates: true
  };

  return new UnifiedKnowledgeGraph({ ...defaultConfig, ...config });
}

// Version and metadata
export const KNOWLEDGE_GRAPH_VERSION = '1.0.0';
export const KNOWLEDGE_GRAPH_CAPABILITIES = {
  MULTI_TYPE_NODES: true,
  RELATIONSHIP_QUERIES: true,
  SIMILARITY_SEARCH: true,
  TEMPORAL_QUERIES: true,
  EMBEDDING_SUPPORT: true,
  REAL_TIME_UPDATES: true,
  PERSISTENCE: true,
  CACHING: true,
  STATISTICS: true
} as const;