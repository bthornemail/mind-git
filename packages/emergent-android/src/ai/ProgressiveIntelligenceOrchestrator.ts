import { MathematicalConstraintEngine, MathematicalSolution, E8RoutingPath } from './MathematicalConstraintEngine';
import { HybridIntelligenceCoordinator, DecisionContext } from './HybridIntelligenceCoordinator';
import { SwarmIntelligenceEngine, SwarmNode, Task, SwarmState } from './SwarmIntelligenceEngine';
import { EventEmitter } from 'events';

export interface ProgressiveDecision {
  action: string;
  confidence: number;
  reasoning: string;
  allocation?: any[];
  mathematicalSolution?: MathematicalSolution;
  aiEnhancement?: any;
  e8Routing?: E8RoutingPath;
  decisionPath: 'mathematical' | 'hybrid' | 'llm_enhanced' | 'constraint_violation';
  explanation: {
    mathematical: string;
    ai: string;
    combined: string;
  };
}

export interface ProgressiveMetrics {
  totalDecisions: number;
  mathematicalDecisions: number;
  hybridDecisions: number;
  llmDecisions: number;
  constraintViolations: number;
  averageConfidence: number;
  decisionLatency: number;
  constraintEffectiveness: number;
}

export class ProgressiveIntelligenceOrchestrator extends EventEmitter {
  private constraintEngine: MathematicalConstraintEngine;
  private hybridCoordinator?: HybridIntelligenceCoordinator;
  private tfEngine: SwarmIntelligenceEngine;
  private metrics: ProgressiveMetrics;
  private decisionThresholds: {
    mathematical: number;
    hybrid: number;
    llm: number;
  };

  constructor(tfEngine: SwarmIntelligenceEngine, llmEndpoint?: string) {
    super();
    
    this.tfEngine = tfEngine;
    this.constraintEngine = new MathematicalConstraintEngine();
    
    if (llmEndpoint) {
      this.hybridCoordinator = new HybridIntelligenceCoordinator(tfEngine, llmEndpoint);
    }

    this.metrics = {
      totalDecisions: 0,
      mathematicalDecisions: 0,
      hybridDecisions: 0,
      llmDecisions: 0,
      constraintViolations: 0,
      averageConfidence: 0,
      decisionLatency: 0,
      constraintEffectiveness: 0
    };

    this.decisionThresholds = {
      mathematical: 0.9,  // High confidence needed for pure mathematical
      hybrid: 0.7,        // Medium confidence for hybrid
      llm: 0.5           // Low confidence triggers LLM
    };

    this.setupEventListeners();
  }

  private setupEventListeners(): void {
    this.constraintEngine.on('constraintsApplied', (solution) => {
      this.emit('constraintsApplied', solution);
    });

    this.constraintEngine.on('e8PathFound', (path) => {
      this.emit('e8PathFound', path);
    });

    if (this.hybridCoordinator) {
      this.hybridCoordinator.on('decision', (data) => {
        this.emit('hybridDecision', data);
      });
    }

    this.tfEngine.on('learning', (data) => {
      this.emit('tensorflowLearning', data);
    });
  }

  // CORE DECISION MAKING - Progressive Intelligence
  async makeDecision(context: DecisionContext): Promise<ProgressiveDecision> {
    const startTime = Date.now();
    this.metrics.totalDecisions++;

    console.log(`🧠 Progressive Decision ${this.metrics.totalDecisions}: Analyzing ${context.tasks.length} tasks across ${context.nodes.length} nodes`);

    try {
      // LEVEL 1: Mathematical Constraints (ALWAYS FIRST)
      const mathematicalSolution = this.constraintEngine.applyConstraints(context.nodes, context.tasks);
      
      console.log(`📐 Mathematical solution: ${mathematicalSolution.validNodes.length}/${context.nodes.length} nodes valid, ${(mathematicalSolution.confidence * 100).toFixed(1)}% confidence`);

      // Check if mathematical solution is sufficient
      if (mathematicalSolution.confidence >= this.decisionThresholds.mathematical) {
        const decision = await this.createMathematicalDecision(mathematicalSolution, context);
        this.metrics.mathematicalDecisions++;
        
        const latency = Date.now() - startTime;
        this.updateMetrics(decision, latency);
        
        console.log(`✅ Pure mathematical decision: ${decision.action} (${latency}ms)`);
        this.emit('decisionMade', { type: 'mathematical', decision, latency });
        
        return decision;
      }

      // LEVEL 2: Hybrid Intelligence (Mathematical + TensorFlow)
      if (this.hybridCoordinator && mathematicalSolution.confidence >= this.decisionThresholds.hybrid) {
        console.log(`🤖 Mathematical confidence insufficient, using hybrid intelligence...`);
        
        // Create constrained context for AI
        const constrainedContext = this.createConstrainedContext(mathematicalSolution, context);
        const aiDecision = await this.hybridCoordinator.makeDecision(constrainedContext);
        
        const decision = await this.createHybridDecision(mathematicalSolution, aiDecision, context);
        this.metrics.hybridDecisions++;
        
        const latency = Date.now() - startTime;
        this.updateMetrics(decision, latency);
        
        console.log(`🤖 Hybrid decision: ${decision.action} (${latency}ms)`);
        this.emit('decisionMade', { type: 'hybrid', decision, latency });
        
        return decision;
      }

      // LEVEL 3: LLM Enhanced (Complex reasoning needed)
      if (this.hybridCoordinator && context.requiresExplanation) {
        console.log(`🧠 Complex scenario detected, using LLM-enhanced reasoning...`);
        
        const constrainedContext = this.createConstrainedContext(mathematicalSolution, context);
        const aiDecision = await this.hybridCoordinator.makeDecision(constrainedContext);
        
        const decision = await this.createLLMEnhancedDecision(mathematicalSolution, aiDecision, context);
        this.metrics.llmDecisions++;
        
        const latency = Date.now() - startTime;
        this.updateMetrics(decision, latency);
        
        console.log(`🧠 LLM-enhanced decision: ${decision.action} (${latency}ms)`);
        this.emit('decisionMade', { type: 'llm_enhanced', decision, latency });
        
        return decision;
      }

      // LEVEL 4: Constraint Violation (No valid solution)
      const decision = this.createConstraintViolationDecision(mathematicalSolution, context);
      this.metrics.constraintViolations++;
      
      const latency = Date.now() - startTime;
      this.updateMetrics(decision, latency);
      
      console.log(`❌ Constraint violation decision: ${decision.action} (${latency}ms)`);
      this.emit('decisionMade', { type: 'constraint_violation', decision, latency });
      
      return decision;

    } catch (error) {
      console.error(`❌ Progressive decision making failed:`, error);
      
      const fallbackDecision: ProgressiveDecision = {
        action: 'error',
        confidence: 0.0,
        reasoning: `Decision making failed: ${error.message}`,
        decisionPath: 'constraint_violation',
        explanation: {
          mathematical: 'Error in constraint processing',
          ai: 'Error in AI processing',
          combined: 'System error - fallback decision'
        }
      };

      const latency = Date.now() - startTime;
      this.updateMetrics(fallbackDecision, latency);
      
      return fallbackDecision;
    }
  }

  private async createMathematicalDecision(mathematicalSolution: MathematicalSolution, context: DecisionContext): Promise<ProgressiveDecision> {
    // Create allocation based purely on mathematical constraints
    const allocation = this.createMathematicalAllocation(mathematicalSolution.validNodes, context.tasks);
    
    // Find E8 routing paths
    const e8Routing = this.findE8RoutingForAllocation(allocation, mathematicalSolution.validNodes);

    return {
      action: 'allocate_tasks',
      confidence: mathematicalSolution.confidence,
      reasoning: mathematicalSolution.reasoning,
      allocation,
      mathematicalSolution,
      e8Routing,
      decisionPath: 'mathematical',
      explanation: {
        mathematical: mathematicalSolution.reasoning,
        ai: 'No AI enhancement needed - mathematical solution sufficient',
        combined: `Pure mathematical solution with ${(mathematicalSolution.confidence * 100).toFixed(1)}% confidence`
      }
    };
  }

  private async createHybridDecision(mathematicalSolution: MathematicalSolution, aiDecision: any, context: DecisionContext): Promise<ProgressiveDecision> {
    // Combine mathematical constraints with AI optimization
    const enhancedAllocation = this.enhanceAllocationWithAI(mathematicalSolution, aiDecision, context);
    
    // Find E8 routing paths
    const e8Routing = this.findE8RoutingForAllocation(enhancedAllocation, mathematicalSolution.validNodes);

    // Calculate combined confidence
    const combinedConfidence = (mathematicalSolution.confidence + aiDecision.confidence) / 2;

    return {
      action: aiDecision.action || 'allocate_tasks',
      confidence: combinedConfidence,
      reasoning: `Mathematical constraints + AI optimization: ${mathematicalSolution.reasoning} | ${aiDecision.reasoning}`,
      allocation: enhancedAllocation,
      mathematicalSolution,
      aiEnhancement: aiDecision,
      e8Routing,
      decisionPath: 'hybrid',
      explanation: {
        mathematical: mathematicalSolution.reasoning,
        ai: aiDecision.reasoning,
        combined: `Mathematical constraints define valid space, AI optimizes within it (${(combinedConfidence * 100).toFixed(1)}% confidence)`
      }
    };
  }

  private async createLLMEnhancedDecision(mathematicalSolution: MathematicalSolution, aiDecision: any, context: DecisionContext): Promise<ProgressiveDecision> {
    // Use LLM reasoning to explain and potentially modify the decision
    const enhancedAllocation = this.enhanceAllocationWithAI(mathematicalSolution, aiDecision, context);
    
    // Find E8 routing paths
    const e8Routing = this.findE8RoutingForAllocation(enhancedAllocation, mathematicalSolution.validNodes);

    // Calculate combined confidence with LLM weighting
    const combinedConfidence = (mathematicalSolution.confidence * 0.4 + aiDecision.confidence * 0.6);

    return {
      action: aiDecision.action || 'allocate_tasks',
      confidence: combinedConfidence,
      reasoning: `LLM-enhanced decision: ${aiDecision.reasoning}`,
      allocation: enhancedAllocation,
      mathematicalSolution,
      aiEnhancement: aiDecision,
      e8Routing,
      decisionPath: 'llm_enhanced',
      explanation: {
        mathematical: mathematicalSolution.reasoning,
        ai: aiDecision.reasoning,
        combined: `LLM provides complex reasoning for mathematically constrained solution (${(combinedConfidence * 100).toFixed(1)}% confidence)`
      }
    };
  }

  private createConstraintViolationDecision(mathematicalSolution: MathematicalSolution, context: DecisionContext): ProgressiveDecision {
    return {
      action: 'constraint_violation',
      confidence: 0.0,
      reasoning: 'No nodes satisfy mathematical constraints - system cannot proceed',
      mathematicalSolution,
      decisionPath: 'constraint_violation',
      explanation: {
        mathematical: mathematicalSolution.reasoning,
        ai: 'No AI processing possible due to constraint violations',
        combined: 'System constraint violation - requires human intervention or constraint relaxation'
      }
    };
  }

  private createConstrainedContext(mathematicalSolution: MathematicalSolution, originalContext: DecisionContext): DecisionContext {
    return {
      ...originalContext,
      nodes: mathematicalSolution.validNodes,
      hasUnusualConstraints: mathematicalSolution.violations.length > 0,
      requiresExplanation: originalContext.requiresExplanation || mathematicalSolution.confidence < 0.8
    };
  }

  private createMathematicalAllocation(validNodes: SwarmNode[], tasks: Task[]): any[] {
    const allocation = [];

    // Simple round-robin within mathematically valid nodes
    for (let i = 0; i < tasks.length; i++) {
      const task = tasks[i];
      const node = validNodes[i % validNodes.length];
      
      allocation.push({
        taskId: task.id,
        nodeId: node.id,
        confidence: 1.0, // Mathematical certainty
        expectedCompletion: this.estimateCompletionTime(task, node),
        reasoning: `Mathematically valid allocation to ${node.id}`
      });
    }

    return allocation;
  }

  private enhanceAllocationWithAI(mathematicalSolution: MathematicalSolution, aiDecision: any, context: DecisionContext): any[] {
    // Start with mathematical allocation
    const baseAllocation = this.createMathematicalAllocation(mathematicalSolution.validNodes, context.tasks);
    
    // Enhance with AI optimization if available
    if (aiDecision && aiDecision.allocation) {
      // Merge AI optimizations while respecting mathematical constraints
      return this.mergeAllocations(baseAllocation, aiDecision.allocation, mathematicalSolution.validNodes);
    }

    return baseAllocation;
  }

  private mergeAllocations(mathematicalAllocation: any[], aiAllocation: any[], validNodes: SwarmNode[]): any[] {
    const merged = [];
    const validNodeIds = new Set(validNodes.map(n => n.id));

    // Start with mathematical allocation
    for (const mathAlloc of mathematicalAllocation) {
      // Find corresponding AI allocation
      const aiAlloc = aiAllocation.find(a => a.taskId === mathAlloc.taskId);
      
      if (aiAlloc && validNodeIds.has(aiAlloc.nodeId)) {
        // Use AI allocation if it respects constraints
        merged.push({
          ...aiAlloc,
          confidence: (mathAlloc.confidence + aiAlloc.confidence) / 2,
          reasoning: `Mathematical constraints + AI optimization: ${mathAlloc.reasoning} | ${aiAlloc.reasoning}`
        });
      } else {
        // Fall back to mathematical allocation
        merged.push(mathAlloc);
      }
    }

    return merged;
  }

  private findE8RoutingForAllocation(allocation: any[], validNodes: SwarmNode[]): E8RoutingPath | undefined {
    if (allocation.length < 2 || !validNodes[0]?.location) {
      return undefined;
    }

    try {
      // Find routing between first two allocated nodes
      const sourceNode = validNodes.find(n => n.id === allocation[0].nodeId);
      const destNode = validNodes.find(n => n.id === allocation[1].nodeId);

      if (sourceNode && destNode) {
        return this.constraintEngine.findOptimalE8Path(sourceNode, destNode);
      }
    } catch (error) {
      console.warn('E8 routing calculation failed:', error);
    }

    return undefined;
  }

  private estimateCompletionTime(task: Task, node: SwarmNode): number {
    // Mathematical estimation based on capabilities
    const complexity = task.requirements.cpu + task.requirements.memory / 100;
    const capability = node.capabilities.cpu + node.capabilities.memory / 100;
    return Math.max(1, (complexity / capability) * 60); // minutes
  }

  private updateMetrics(decision: ProgressiveDecision, latency: number): void {
    // Update average confidence
    this.metrics.averageConfidence = 
      (this.metrics.averageConfidence * (this.metrics.totalDecisions - 1) + decision.confidence) / this.metrics.totalDecisions;
    
    // Update average latency
    this.metrics.decisionLatency = 
      (this.metrics.decisionLatency * (this.metrics.totalDecisions - 1) + latency) / this.metrics.totalDecisions;
  }

  // Public API methods

  async optimizeSwarmWithMathematics(swarmState: SwarmState): Promise<{
    mathematicalSolution: MathematicalSolution;
    routing: { [sourceId: string]: string };
    behavior: { [nodeId: string]: { dx: number; dy: number } };
    health: any;
    anomalies: { [nodeId: string]: number };
    e8Paths: { [sourceId: string]: E8RoutingPath };
  }> {
    console.log('🔧 Optimizing swarm with progressive mathematics...');

    // Apply mathematical constraints first
    const mathematicalSolution = this.constraintEngine.applyConstraints(swarmState.nodes, swarmState.tasks);

    if (mathematicalSolution.validNodes.length === 0) {
      throw new Error('No nodes satisfy mathematical constraints - cannot optimize swarm');
    }

    // Use TensorFlow optimization within constrained space
    const constrainedSwarmState = {
      ...swarmState,
      nodes: mathematicalSolution.validNodes
    };

    const [routing, behavior, health, anomalies] = await Promise.all([
      this.tfEngine.optimizeNetworkRouting(constrainedSwarmState),
      this.tfEngine.calculateSwarmBehavior(constrainedSwarmState.nodes),
      this.tfEngine.getSwarmHealth(constrainedSwarmState),
      this.tfEngine.detectAnomalies(constrainedSwarmState)
    ]);

    // Calculate E8 routing paths
    const e8Paths: { [sourceId: string]: E8RoutingPath } = {};
    
    for (let i = 0; i < mathematicalSolution.validNodes.length - 1; i++) {
      const source = mathematicalSolution.validNodes[i];
      const dest = mathematicalSolution.validNodes[i + 1];
      
      if (source.location && dest.location) {
        try {
          const path = this.constraintEngine.findOptimalE8Path(source, dest);
          e8Paths[source.id] = path;
        } catch (error) {
          console.warn(`Failed to calculate E8 path from ${source.id} to ${dest.id}:`, error);
        }
      }
    }

    const result = {
      mathematicalSolution,
      routing,
      behavior,
      health,
      anomalies,
      e8Paths
    };

    console.log(`✅ Progressive swarm optimization complete:`, {
      validNodes: `${mathematicalSolution.validNodes.length}/${swarmState.nodes.length}`,
      routingRules: Object.keys(routing).length,
      e8Paths: Object.keys(e8Paths).length,
      health: `${health.overall.toFixed(1)}%`
    });

    this.emit('swarmOptimized', result);
    return result;
  }

  // Constraint management
  addConstraint(constraint: any): void {
    this.constraintEngine.addConstraint(constraint);
  }

  removeConstraint(type: string): void {
    this.constraintEngine.removeConstraint(type);
  }

  updateConstraint(type: string, updates: any): void {
    this.constraintEngine.updateConstraint(type, updates);
  }

  getConstraints(): any[] {
    return this.constraintEngine.getConstraints();
  }

  // Analysis and verification
  analyzeConstraintEffectiveness(nodes: SwarmNode[]): any[] {
    return this.constraintEngine.analyzeConstraintEffectiveness(nodes);
  }

  verifyMathematicalSolution(solution: MathematicalSolution): any {
    return this.constraintEngine.verifySolution(solution);
  }

  // Metrics and monitoring
  getMetrics(): ProgressiveMetrics {
    return { ...this.metrics };
  }

  getDecisionBreakdown(): {
    mathematical: number;
    hybrid: number;
    llm: number;
    violations: number;
    percentages: {
      mathematical: number;
      hybrid: number;
      llm: number;
      violations: number;
    };
  } {
    const total = Math.max(1, this.metrics.totalDecisions);
    
    return {
      mathematical: this.metrics.mathematicalDecisions,
      hybrid: this.metrics.hybridDecisions,
      llm: this.metrics.llmDecisions,
      violations: this.metrics.constraintViolations,
      percentages: {
        mathematical: (this.metrics.mathematicalDecisions / total) * 100,
        hybrid: (this.metrics.hybridDecisions / total) * 100,
        llm: (this.metrics.llmDecisions / total) * 100,
        violations: (this.metrics.constraintViolations / total) * 100
      }
    };
  }

  // Configuration
  updateDecisionThresholds(thresholds: Partial<typeof this.decisionThresholds>): void {
    this.decisionThresholds = { ...this.decisionThresholds, ...thresholds };
    console.log('📝 Decision thresholds updated:', this.decisionThresholds);
    this.emit('thresholdsUpdated', this.decisionThresholds);
  }

  getDecisionThresholds(): typeof this.decisionThresholds {
    return { ...this.decisionThresholds };
  }

  // Cleanup
  dispose(): void {
    this.constraintEngine.dispose();
    if (this.hybridCoordinator) {
      this.hybridCoordinator.removeAllListeners();
    }
    this.removeAllListeners();
    console.log('🧹 Progressive Intelligence Orchestrator disposed');
  }
}