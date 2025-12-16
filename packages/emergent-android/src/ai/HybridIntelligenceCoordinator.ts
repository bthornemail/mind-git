import { SwarmIntelligenceEngine, SwarmNode, Task, SwarmState, AllocationDecision } from './SwarmIntelligenceEngine';
import { EventEmitter } from 'events';

export interface DecisionContext {
  tasks: Task[];
  nodes: SwarmNode[];
  swarmState: SwarmState;
  hasUnusualConstraints?: boolean;
  requiresExplanation?: boolean;
  complexity?: number;
}

export interface Decision {
  action: string;
  confidence: number;
  reasoning: string;
  allocation?: AllocationDecision[];
  alternative?: Decision;
}

export interface LLMReasoning {
  analysis: string;
  suggestions: string[];
  confidence: number;
  explanation: string;
}

export class HybridIntelligenceCoordinator extends EventEmitter {
  private tfEngine: SwarmIntelligenceEngine;
  private llmAvailable: boolean = false;
  private llmEndpoint?: string;
  private reasoningCache: Map<string, LLMReasoning> = new Map();
  
  constructor(tfEngine: SwarmIntelligenceEngine, llmEndpoint?: string) {
    super();
    this.tfEngine = tfEngine;
    this.llmEndpoint = llmEndpoint;
    this.checkLLMAvailability();
  }

  private async checkLLMAvailability(): Promise<void> {
    if (!this.llmEndpoint) {
      console.log('🤖 LLM endpoint not configured - using TensorFlow-only mode');
      this.llmAvailable = false;
      return;
    }

    try {
      // Simple health check for LLM service
      const response = await fetch(`${this.llmEndpoint}/health`, { 
        method: 'GET',
        timeout: 5000 
      });
      
      this.llmAvailable = response.ok;
      console.log(this.llmAvailable ? 
        '✅ LLM service available' : 
        '⚠️ LLM service unavailable - using TensorFlow-only mode'
      );
    } catch (error) {
      console.log('⚠️ Cannot reach LLM service - using TensorFlow-only mode');
      this.llmAvailable = false;
    }
  }

  async makeDecision(context: DecisionContext): Promise<Decision> {
    console.log(`🧠 Making decision for ${context.tasks.length} tasks across ${context.nodes.length} nodes`);

    // 1. First try TensorFlow (fast, efficient)
    const startTime = Date.now();
    const tfDecision = await this.makeTensorFlowDecision(context);
    const tfTime = Date.now() - startTime;

    console.log(`⚡ TensorFlow decision: ${tfTime}ms, confidence: ${(tfDecision.confidence * 100).toFixed(1)}%`);

    // 2. Determine if LLM reasoning is needed
    const needsLLM = this.needsComplexReasoning(tfDecision, context);
    
    if (needsLLM && this.llmAvailable) {
      console.log('🤖 Consulting LLM for complex reasoning...');
      const llmStartTime = Date.now();
      
      try {
        const llmReasoning = await this.consultLLM(tfDecision, context);
        const llmTime = Date.now() - llmStartTime;
        
        console.log(`🤖 LLM reasoning: ${llmTime}ms, confidence: ${(llmReasoning.confidence * 100).toFixed(1)}%`);
        
        // 3. Integrate LLM reasoning with TensorFlow optimization
        const hybridDecision = this.integrateReasoning(tfDecision, llmReasoning, context);
        
        this.emit('decision', { 
          type: 'hybrid', 
          tfTime, 
          llmTime, 
          totalTime: tfTime + llmTime 
        });
        
        return hybridDecision;
      } catch (error) {
        console.error('❌ LLM reasoning failed, falling back to TensorFlow:', error);
      }
    }

    // 4. Return TensorFlow decision if LLM not available or not needed
    this.emit('decision', { type: 'tensorflow', time: tfTime });
    return tfDecision;
  }

  private async makeTensorFlowDecision(context: DecisionContext): Promise<Decision> {
    try {
      // Use TensorFlow engine for optimization
      const allocations = await this.tfEngine.optimizeTaskAllocation(context.tasks, context.nodes);
      
      // Get swarm health for decision confidence
      const health = await this.tfEngine.getSwarmHealth(context.swarmState);
      
      // Calculate overall confidence based on allocations and health
      const avgConfidence = allocations.length > 0 ? 
        allocations.reduce((sum, a) => sum + a.confidence, 0) / allocations.length : 0;
      
      const confidence = avgConfidence * (health.overall / 100);

      return {
        action: 'allocate_tasks',
        confidence: Math.max(0.1, Math.min(0.99, confidence)),
        reasoning: `TensorFlow optimization based on resource capabilities and swarm health (${health.overall.toFixed(1)}%)`,
        allocation: allocations
      };
    } catch (error) {
      console.error('❌ TensorFlow decision failed:', error);
      return {
        action: 'fallback',
        confidence: 0.1,
        reasoning: `TensorFlow optimization failed: ${error.message}`
      };
    }
  }

  private needsComplexReasoning(tfDecision: Decision, context: DecisionContext): boolean {
    // Multiple heuristics for when to use LLM
    const conditions = [
      {
        name: 'High Task Complexity',
        condition: context.tasks.length > 10,
        weight: 0.3
      },
      {
        name: 'Low TensorFlow Confidence',
        condition: tfDecision.confidence < 0.7,
        weight: 0.4
      },
      {
        name: 'Unusual Constraints',
        condition: context.hasUnusualConstraints === true,
        weight: 0.5
      },
      {
        name: 'User Requested Explanation',
        condition: context.requiresExplanation === true,
        weight: 0.6
      },
      {
        name: 'High Node Count',
        condition: context.nodes.length > 15,
        weight: 0.2
      },
      {
        name: 'Mixed Task Types',
        condition: new Set(context.tasks.map(t => t.type)).size > 2,
        weight: 0.3
      }
    ];

    const score = conditions
      .filter(c => c.condition)
      .reduce((sum, c) => sum + c.weight, 0);

    const shouldUseLLM = score > 0.5;
    
    if (shouldUseLLM) {
      const activeConditions = conditions
        .filter(c => c.condition)
        .map(c => c.name)
        .join(', ');
      console.log(`🤖 LLM reasoning triggered: ${activeConditions} (score: ${score.toFixed(2)})`);
    }

    return shouldUseLLM;
  }

  private async consultLLM(tfDecision: Decision, context: DecisionContext): Promise<LLMReasoning> {
    // Create cache key
    const cacheKey = this.createCacheKey(tfDecision, context);
    
    // Check cache first
    if (this.reasoningCache.has(cacheKey)) {
      console.log('📋 Using cached LLM reasoning');
      return this.reasoningCache.get(cacheKey)!;
    }

    // Prepare prompt for LLM
    const prompt = this.createLLMPrompt(tfDecision, context);
    
    try {
      // Call LLM service
      const response = await fetch(`${this.llmEndpoint}/api/generate`, {
        method: 'POST',
        headers: {
          'Content-Type': 'application/json',
        },
        body: JSON.stringify({
          prompt,
          max_tokens: 500,
          temperature: 0.3,
          system_prompt: 'You are an expert in distributed systems and swarm intelligence. Analyze the given task allocation and provide insightful recommendations.'
        })
      });

      if (!response.ok) {
        throw new Error(`LLM service error: ${response.status}`);
      }

      const result = await response.json();
      const reasoning = this.parseLLMResponse(result.text);
      
      // Cache the result
      this.reasoningCache.set(cacheKey, reasoning);
      
      // Limit cache size
      if (this.reasoningCache.size > 100) {
        const firstKey = this.reasoningCache.keys().next().value;
        this.reasoningCache.delete(firstKey);
      }

      return reasoning;
    } catch (error) {
      console.error('❌ LLM consultation failed:', error);
      throw error;
    }
  }

  private createCacheKey(tfDecision: Decision, context: DecisionContext): string {
    const keyData = {
      taskCount: context.tasks.length,
      nodeCount: context.nodes.length,
      tfConfidence: tfDecision.confidence,
      taskTypes: [...new Set(context.tasks.map(t => t.type))].sort(),
      nodeRoles: [...new Set(context.nodes.map(n => n.role))].sort(),
      timestamp: Math.floor(Date.now() / (1000 * 60)) // Cache per minute
    };
    
    return Buffer.from(JSON.stringify(keyData)).toString('base64');
  }

  private createLLMPrompt(tfDecision: Decision, context: DecisionContext): string {
    const taskSummary = context.tasks.map(t => 
      `${t.type} (CPU:${t.requirements.cpu}, MEM:${t.requirements.memory}MB, BAT:${t.requirements.battery}%)`
    ).join('\n');

    const nodeSummary = context.nodes.map(n => 
      `${n.role} (CPU:${n.capabilities.cpu}%, MEM:${n.capabilities.memory}MB, BAT:${n.capabilities.battery}%)`
    ).join('\n');

    return `
Analyze this swarm intelligence task allocation:

**TASKS (${context.tasks.length}):**
${taskSummary}

**NODES (${context.nodes.length}):**
${nodeSummary}

**TENSORFLOW DECISION:**
Action: ${tfDecision.action}
Confidence: ${(tfDecision.confidence * 100).toFixed(1)}%
Reasoning: ${tfDecision.reasoning}

**ALLOCATION PROPOSAL:**
${tfDecision.allocation?.map(a => 
  `Task ${a.taskId} → Node ${a.nodeId} (${(a.confidence * 100).toFixed(1)}% confidence)`
).join('\n') || 'No allocations proposed'}

**ANALYSIS REQUESTED:**
1. Is this allocation optimal? Why or why not?
2. What are the potential failure points?
3. Suggest specific improvements
4. Identify any unusual patterns or edge cases
5. Rate the overall quality (0-100) and explain

Provide a concise, actionable analysis focusing on swarm optimization principles.
`;
  }

  private parseLLMResponse(response: string): LLMReasoning {
    // Simple parsing - in production, you'd use more sophisticated parsing
    const lines = response.split('\n').filter(line => line.trim());
    
    const analysis = lines.find(line => 
      line.toLowerCase().includes('analysis') || 
      line.toLowerCase().includes('overall')
    ) || response.substring(0, 200);

    const suggestions = lines.filter(line => 
      line.toLowerCase().includes('suggest') ||
      line.toLowerCase().includes('recommend') ||
      line.toLowerCase().includes('improve')
    ).slice(0, 3);

    // Extract confidence from response
    const confidenceMatch = response.match(/(\d+)%/);
    const confidence = confidenceMatch ? 
      Math.min(0.99, Math.max(0.01, parseInt(confidenceMatch[1]) / 100)) : 0.75;

    return {
      analysis: analysis.trim(),
      suggestions: suggestions.length > 0 ? suggestions : ['Consider load balancing', 'Monitor battery levels', 'Optimize network routes'],
      confidence,
      explanation: response.substring(0, 300) + (response.length > 300 ? '...' : '')
    };
  }

  private integrateReasoning(tfDecision: Decision, llmReasoning: LLMReasoning, context: DecisionContext): Decision {
    // Combine TensorFlow optimization with LLM insights
    const integratedConfidence = (tfDecision.confidence + llmReasoning.confidence) / 2;
    
    let integratedReasoning = tfDecision.reasoning;
    
    // Add LLM insights to reasoning
    if (llmReasoning.suggestions.length > 0) {
      integratedReasoning += `\n\nLLM Insights:\n${llmReasoning.suggestions.map(s => `• ${s}`).join('\n')}`;
    }

    // Create alternative decision if LLM suggests major changes
    let alternative: Decision | undefined;
    if (llmReasoning.confidence > 0.8 && llmReasoning.suggestions.length > 2) {
      alternative = {
        action: 'reallocate_with_llm_insights',
        confidence: llmReasoning.confidence,
        reasoning: `LLM-driven reallocation: ${llmReasoning.analysis}`,
        allocation: tfDecision.allocation // Would be modified based on LLM suggestions
      };
    }

    return {
      action: tfDecision.action,
      confidence: integratedConfidence,
      reasoning: integratedReasoning,
      allocation: tfDecision.allocation,
      alternative
    };
  }

  // Performance monitoring
  async benchmarkDecisionMaking(context: DecisionContext, iterations: number = 10): Promise<{
    tensorflow: { avgTime: number; avgConfidence: number };
    hybrid: { avgTime: number; avgConfidence: number };
    improvement: { time: number; confidence: number };
  }> {
    console.log(`🏃 Running benchmark: ${iterations} iterations`);

    const tfTimes: number[] = [];
    const tfConfidences: number[] = [];
    const hybridTimes: number[] = [];
    const hybridConfidences: number[] = [];

    for (let i = 0; i < iterations; i++) {
      // TensorFlow only
      const tfStart = Date.now();
      const tfDecision = await this.makeTensorFlowDecision(context);
      const tfTime = Date.now() - tfStart;
      
      tfTimes.push(tfTime);
      tfConfidences.push(tfDecision.confidence);

      // Hybrid (if LLM available)
      if (this.llmAvailable) {
        const hybridStart = Date.now();
        const hybridDecision = await this.makeDecision(context);
        const hybridTime = Date.now() - hybridStart;
        
        hybridTimes.push(hybridTime);
        hybridConfidences.push(hybridDecision.confidence);
      }
    }

    const tfAvgTime = tfTimes.reduce((a, b) => a + b, 0) / tfTimes.length;
    const tfAvgConfidence = tfConfidences.reduce((a, b) => a + b, 0) / tfConfidences.length;

    const hybridAvgTime = hybridTimes.length > 0 ? 
      hybridTimes.reduce((a, b) => a + b, 0) / hybridTimes.length : 0;
    const hybridAvgConfidence = hybridConfidences.length > 0 ?
      hybridConfidences.reduce((a, b) => a + b, 0) / hybridConfidences.length : 0;

    return {
      tensorflow: {
        avgTime: tfAvgTime,
        avgConfidence: tfAvgConfidence
      },
      hybrid: {
        avgTime: hybridAvgTime,
        avgConfidence: hybridAvgConfidence
      },
      improvement: {
        time: hybridAvgTime > 0 ? ((hybridAvgTime - tfAvgTime) / tfAvgTime) * 100 : 0,
        confidence: hybridAvgConfidence > 0 ? ((hybridAvgConfidence - tfAvgConfidence) / tfAvgConfidence) * 100 : 0
      }
    };
  }

  // Adaptive capability detection
  async detectCapabilities(): Promise<{
    tensorflow: boolean;
    llm: boolean;
    gpu: boolean;
    memory: number;
    recommendations: string[];
  }> {
    const capabilities = {
      tensorflow: true, // Always available in this setup
      llm: this.llmAvailable,
      gpu: false, // Would need to check WebGL/WebGPU
      memory: 0, // Would need to check available memory
      recommendations: [] as string[]
    };

    // Check GPU availability
    try {
      const gl = document?.createElement('canvas')?.getContext('webgl');
      capabilities.gpu = !!gl;
    } catch (error) {
      capabilities.gpu = false;
    }

    // Estimate available memory (simplified)
    if (typeof performance !== 'undefined' && performance.memory) {
      capabilities.memory = performance.memory.jsHeapSizeLimit / (1024 * 1024); // MB
    }

    // Generate recommendations
    if (!capabilities.llm) {
      capabilities.recommendations.push('Consider configuring LLM endpoint for enhanced reasoning');
    }
    
    if (!capabilities.gpu) {
      capabilities.recommendations.push('GPU acceleration unavailable - consider WebGL-enabled browser');
    }
    
    if (capabilities.memory < 1000) {
      capabilities.recommendations.push('Limited memory detected - consider using smaller models');
    }

    return capabilities;
  }

  // Cache management
  clearCache(): void {
    this.reasoningCache.clear();
    console.log('🗑️ LLM reasoning cache cleared');
  }

  getCacheStats(): { size: number; keys: string[] } {
    return {
      size: this.reasoningCache.size,
      keys: Array.from(this.reasoningCache.keys()).slice(0, 10) // Show first 10 keys
    };
  }
}