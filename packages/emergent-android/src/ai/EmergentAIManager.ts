import { SwarmIntelligenceEngine, SwarmNode, Task, SwarmState } from './SwarmIntelligenceEngine';
import { HybridIntelligenceCoordinator, DecisionContext } from './HybridIntelligenceCoordinator';
import { DeviceIntelligenceManager } from './DeviceIntelligenceManager';
import { EventEmitter } from 'events';

export interface EmergentAIConfig {
  enableTensorFlow: boolean;
  enableLLM: boolean;
  llmEndpoint?: string;
  intelligenceLevel?: 'basic' | 'enhanced' | 'advanced' | 'hybrid';
  learningRate?: number;
  federatedLearning?: boolean;
  modelUpdateInterval?: number;
}

export interface SwarmMetrics {
  totalNodes: number;
  activeNodes: number;
  totalTasks: number;
  completedTasks: number;
  failedTasks: number;
  averageLatency: number;
  swarmHealth: number;
  learningRounds: number;
  modelAccuracy: number;
}

export class EmergentAIManager extends EventEmitter {
  private tfEngine: SwarmIntelligenceEngine;
  private hybridCoordinator?: HybridIntelligenceCoordinator;
  private deviceManager: DeviceIntelligenceManager;
  private config: EmergentAIConfig;
  private isInitialized = false;
  private metrics: SwarmMetrics;
  private modelUpdateTimer?: NodeJS.Timeout;

  constructor(config: EmergentAIConfig) {
    super();
    this.config = {
      enableTensorFlow: true,
      enableLLM: false,
      learningRate: 0.001,
      federatedLearning: true,
      modelUpdateInterval: 60000, // 1 minute
      ...config
    };

    this.tfEngine = new SwarmIntelligenceEngine();
    this.deviceManager = new DeviceIntelligenceManager();
    
    this.metrics = {
      totalNodes: 0,
      activeNodes: 0,
      totalTasks: 0,
      completedTasks: 0,
      failedTasks: 0,
      averageLatency: 0,
      swarmHealth: 100,
      learningRounds: 0,
      modelAccuracy: 0.85
    };
  }

  async initialize(): Promise<void> {
    console.log('🚀 Initializing Emergent AI Manager...');

    try {
      // 1. Initialize device capabilities
      await this.deviceManager.initialize();
      console.log('✅ Device capabilities detected');

      // 2. Adjust configuration based on device capabilities
      await this.adjustConfigurationForDevice();

      // 3. Initialize TensorFlow engine if enabled
      if (this.config.enableTensorFlow) {
        await this.tfEngine.initialize();
        console.log('✅ TensorFlow engine initialized');
      }

      // 4. Initialize hybrid coordinator if LLM is enabled
      if (this.config.enableLLM && this.config.llmEndpoint) {
        this.hybridCoordinator = new HybridIntelligenceCoordinator(
          this.tfEngine,
          this.config.llmEndpoint
        );
        console.log('✅ Hybrid intelligence coordinator initialized');
      }

      // 5. Set up event listeners
      this.setupEventListeners();

      // 6. Start periodic model updates if federated learning is enabled
      if (this.config.federatedLearning) {
        this.startModelUpdates();
      }

      this.isInitialized = true;
      console.log('🎉 Emergent AI Manager initialized successfully!');
      this.emit('initialized', this.getCapabilities());
    } catch (error) {
      console.error('❌ Failed to initialize Emergent AI Manager:', error);
      throw error;
    }
  }

  private async adjustConfigurationForDevice(): Promise<void> {
    const capabilities = this.deviceManager.getCapabilities();
    const currentLevel = this.deviceManager.getCurrentLevel();

    console.log(`🔧 Adjusting configuration for ${currentLevel.level} intelligence level`);

    // Disable TensorFlow if not supported
    if (!capabilities.tensorFlowCapable) {
      this.config.enableTensorFlow = false;
      console.log('⚠️ TensorFlow disabled - not supported on this device');
    }

    // Disable LLM if not capable
    if (!capabilities.llmCapable) {
      this.config.enableLLM = false;
      console.log('⚠️ LLM disabled - insufficient device capabilities');
    }

    // Adjust learning rate based on device performance
    if (capabilities.cpu < 50) {
      this.config.learningRate = 0.0005; // Slower learning for slower devices
      console.log('🐌 Learning rate reduced for slower CPU');
    }

    // Adjust model update interval based on network
    if (capabilities.network < 50) {
      this.config.modelUpdateInterval = 300000; // 5 minutes for poor network
      console.log('📶 Model update interval increased for poor network');
    }
  }

  private setupEventListeners(): void {
    // TensorFlow engine events
    this.tfEngine.on('learning', (data) => {
      this.metrics.learningRounds = data.round;
      this.emit('learning', data);
    });

    this.tfEngine.on('modelUpdate', (data) => {
      this.emit('modelUpdate', data);
    });

    this.tfEngine.on('psoProgress', (data) => {
      this.emit('optimization', data);
    });

    // Device manager events
    this.deviceManager.on('capabilitiesUpdated', (capabilities) => {
      this.emit('capabilitiesUpdated', capabilities);
    });

    // Hybrid coordinator events
    if (this.hybridCoordinator) {
      this.hybridCoordinator.on('decision', (data) => {
        this.emit('decision', data);
      });
    }
  }

  private startModelUpdates(): void {
    if (this.modelUpdateTimer) {
      clearInterval(this.modelUpdateTimer);
    }

    this.modelUpdateTimer = setInterval(async () => {
      try {
        await this.performModelUpdate();
      } catch (error) {
        console.error('❌ Model update failed:', error);
      }
    }, this.config.modelUpdateInterval);

    console.log(`🔄 Model updates started (interval: ${this.config.modelUpdateInterval}ms)`);
  }

  private async performModelUpdate(): Promise<void> {
    console.log('🔄 Performing periodic model update...');
    
    // This would typically involve:
    // 1. Collecting recent experiences
    // 2. Training models on new data
    // 3. Sharing updates with swarm
    
    this.emit('modelUpdateCompleted', {
      timestamp: Date.now(),
      learningRounds: this.metrics.learningRounds
    });
  }

  // Public API methods

  async makeDecision(context: DecisionContext): Promise<any> {
    if (!this.isInitialized) {
      throw new Error('Emergent AI Manager not initialized');
    }

    const startTime = Date.now();

    try {
      let decision;

      if (this.hybridCoordinator) {
        // Use hybrid intelligence (TensorFlow + LLM)
        decision = await this.hybridCoordinator.makeDecision(context);
      } else if (this.config.enableTensorFlow) {
        // Use TensorFlow only
        const allocations = await this.tfEngine.optimizeTaskAllocation(context.tasks, context.nodes);
        decision = {
          action: 'allocate_tasks',
          confidence: allocations.length > 0 ? 
            allocations.reduce((sum, a) => sum + a.confidence, 0) / allocations.length : 0,
          reasoning: 'TensorFlow optimization',
          allocation: allocations
        };
      } else {
        // Fallback to basic logic
        decision = this.makeBasicDecision(context);
      }

      const decisionTime = Date.now() - startTime;
      this.metrics.averageLatency = (this.metrics.averageLatency + decisionTime) / 2;

      this.emit('decisionMade', { decision, time: decisionTime });
      return decision;
    } catch (error) {
      console.error('❌ Decision making failed:', error);
      throw error;
    }
  }

  private makeBasicDecision(context: DecisionContext): any {
    // Simple round-robin allocation as fallback
    const allocations = context.tasks.map((task, index) => {
      const node = context.nodes[index % context.nodes.length];
      return {
        taskId: task.id,
        nodeId: node.id,
        confidence: 0.5,
        expectedCompletion: 60,
        reasoning: 'Round-robin allocation (fallback)'
      };
    });

    return {
      action: 'allocate_tasks',
      confidence: 0.5,
      reasoning: 'Basic round-robin allocation (no AI available)',
      allocation: allocations
    };
  }

  async optimizeSwarm(swarmState: SwarmState): Promise<{
    routing: { [sourceId: string]: string };
    behavior: { [nodeId: string]: { dx: number; dy: number } };
    health: any;
    anomalies: { [nodeId: string]: number };
  }> {
    if (!this.config.enableTensorFlow) {
      throw new Error('TensorFlow required for swarm optimization');
    }

    const [routing, behavior, health, anomalies] = await Promise.all([
      this.tfEngine.optimizeNetworkRouting(swarmState),
      this.tfEngine.calculateSwarmBehavior(swarmState.nodes),
      this.tfEngine.getSwarmHealth(swarmState),
      this.tfEngine.detectAnomalies(swarmState)
    ]);

    // Update metrics
    this.metrics.swarmHealth = health.overall;
    this.metrics.totalNodes = swarmState.nodes.length;
    this.metrics.activeNodes = swarmState.nodes.filter(n => 
      n.capabilities.battery > 20 && n.capabilities.cpu > 10
    ).length;

    return { routing, behavior, health, anomalies };
  }

  async learnFromExperience(experience: {
    state: any;
    action: any;
    reward: number;
    nextState: any;
  }): Promise<void> {
    if (!this.config.enableTensorFlow || !this.config.federatedLearning) {
      return;
    }

    await this.tfEngine.learnFromExperience(experience);
    this.metrics.modelAccuracy = Math.min(0.99, this.metrics.modelAccuracy + experience.reward * 0.001);
  }

  async solveOptimizationProblem(
    objective: (x: number[]) => number,
    dimensions?: number,
    options?: {
      swarmSize?: number;
      maxIterations?: number;
    }
  ): Promise<{ bestSolution: number[]; bestFitness: number }> {
    if (!this.config.enableTensorFlow) {
      throw new Error('TensorFlow required for optimization');
    }

    const result = await this.tfEngine.particleSwarmOptimization(
      objective,
      dimensions,
      options?.swarmSize,
      options?.maxIterations
    );

    return {
      bestSolution: result.bestSolution,
      bestFitness: result.bestFitness
    };
  }

  // Metrics and monitoring
  getMetrics(): SwarmMetrics {
    return { ...this.metrics };
  }

  async getDetailedStatus(): Promise<{
    initialized: boolean;
    capabilities: any;
    config: EmergentAIConfig;
    metrics: SwarmMetrics;
    modelInfo: any;
    health: any;
  }> {
    const capabilities = this.deviceManager.getCapabilities();
    const modelInfo = this.config.enableTensorFlow ? this.tfEngine.getModelInfo() : {};
    const health = await this.deviceManager.getHealthStatus();

    return {
      initialized: this.isInitialized,
      capabilities,
      config: this.config,
      metrics: this.getMetrics(),
      modelInfo,
      health
    };
  }

  getCapabilities(): any {
    return {
      device: this.deviceManager.getCapabilities(),
      intelligence: this.deviceManager.getCurrentLevel(),
      config: this.config,
      models: this.config.enableTensorFlow ? Object.keys(this.tfEngine.getModelInfo()) : [],
      features: this.deviceManager.getCurrentLevel().features
    };
  }

  // Configuration management
  async updateConfig(newConfig: Partial<EmergentAIConfig>): Promise<void> {
    const oldConfig = { ...this.config };
    this.config = { ...this.config, ...newConfig };

    console.log('⚙️ Updating configuration...');

    // Handle TensorFlow enable/disable
    if (oldConfig.enableTensorFlow !== this.config.enableTensorFlow) {
      if (this.config.enableTensorFlow && !this.isInitialized) {
        await this.tfEngine.initialize();
      } else if (!this.config.enableTensorFlow) {
        this.tfEngine.dispose();
      }
    }

    // Handle LLM enable/disable
    if (oldConfig.enableLLM !== this.config.enableLLM) {
      if (this.config.enableLLM && this.config.llmEndpoint) {
        this.hybridCoordinator = new HybridIntelligenceCoordinator(
          this.tfEngine,
          this.config.llmEndpoint
        );
      } else {
        this.hybridCoordinator = undefined;
      }
    }

    // Handle federated learning changes
    if (oldConfig.federatedLearning !== this.config.federatedLearning) {
      if (this.config.federatedLearning) {
        this.startModelUpdates();
      } else if (this.modelUpdateTimer) {
        clearInterval(this.modelUpdateTimer);
        this.modelUpdateTimer = undefined;
      }
    }

    this.emit('configUpdated', this.config);
    console.log('✅ Configuration updated');
  }

  // Benchmarking and testing
  async runBenchmark(iterations: number = 10): Promise<{
    decisionMaking: { avgTime: number; avgConfidence: number };
    optimization: { avgTime: number; avgFitness: number };
    learning: { avgTime: number; avgImprovement: number };
    overall: { score: number; grade: string };
  }> {
    console.log(`🏃 Running comprehensive benchmark (${iterations} iterations)...`);

    // Benchmark decision making
    const decisionTimes: number[] = [];
    const decisionConfidences: number[] = [];

    for (let i = 0; i < iterations; i++) {
      const context = this.createMockDecisionContext();
      const start = Date.now();
      const decision = await this.makeDecision(context);
      const time = Date.now() - start;

      decisionTimes.push(time);
      decisionConfidences.push(decision.confidence);
    }

    // Benchmark optimization
    const optimizationTimes: number[] = [];
    const optimizationFitness: number[] = [];

    for (let i = 0; i < Math.min(5, iterations); i++) {
      const start = Date.now();
      const result = await this.solveOptimizationProblem(
        x => x.reduce((sum, val) => sum + val * val, 0), // Sphere function
        3,
        { swarmSize: 10, maxIterations: 50 }
      );
      const time = Date.now() - start;

      optimizationTimes.push(time);
      optimizationFitness.push(result.bestFitness);
    }

    // Calculate averages
    const avgDecisionTime = decisionTimes.reduce((a, b) => a + b, 0) / decisionTimes.length;
    const avgDecisionConfidence = decisionConfidences.reduce((a, b) => a + b, 0) / decisionConfidences.length;
    const avgOptimizationTime = optimizationTimes.reduce((a, b) => a + b, 0) / optimizationTimes.length;
    const avgOptimizationFitness = optimizationFitness.reduce((a, b) => a + b, 0) / optimizationFitness.length;

    // Calculate overall score
    const timeScore = Math.max(0, 100 - (avgDecisionTime / 10)); // Lower is better
    const confidenceScore = avgDecisionConfidence * 100;
    const optimizationScore = Math.max(0, 100 - avgOptimizationFitness); // Lower fitness is better for sphere function
    const overallScore = (timeScore + confidenceScore + optimizationScore) / 3;

    let grade = 'F';
    if (overallScore >= 90) grade = 'A+';
    else if (overallScore >= 80) grade = 'A';
    else if (overallScore >= 70) grade = 'B';
    else if (overallScore >= 60) grade = 'C';
    else if (overallScore >= 50) grade = 'D';

    return {
      decisionMaking: {
        avgTime: avgDecisionTime,
        avgConfidence: avgDecisionConfidence
      },
      optimization: {
        avgTime: avgOptimizationTime,
        avgFitness: avgOptimizationFitness
      },
      learning: {
        avgTime: 0, // Would need actual learning benchmark
        avgImprovement: 0
      },
      overall: {
        score: Math.round(overallScore),
        grade
      }
    };
  }

  private createMockDecisionContext(): DecisionContext {
    const tasks: Task[] = [
      {
        id: 'task-1',
        type: 'computation',
        requirements: { cpu: 30, memory: 512, battery: 10, network: 20 },
        payload: {},
        priority: 5
      },
      {
        id: 'task-2',
        type: 'sensing',
        requirements: { cpu: 20, memory: 256, battery: 5, network: 30 },
        payload: {},
        priority: 3
      }
    ];

    const nodes: SwarmNode[] = [
      {
        id: 'node-1',
        capabilities: { cpu: 80, memory: 2048, battery: 75, network: 60 },
        role: 'coordinator',
        location: { x: 0, y: 0 }
      },
      {
        id: 'node-2',
        capabilities: { cpu: 60, memory: 1024, battery: 50, network: 40 },
        role: 'worker',
        location: { x: 10, y: 10 }
      }
    ];

    const swarmState: SwarmState = {
      nodes,
      tasks,
      networkLatency: 50,
      swarmHealth: 85
    };

    return {
      tasks,
      nodes,
      swarmState,
      complexity: 2,
      hasUnusualConstraints: false,
      requiresExplanation: false
    };
  }

  // Accessor methods for integration
  getTensorFlowEngine(): SwarmIntelligenceEngine {
    return this.tfEngine;
  }

  getDeviceManager(): any {
    return this.deviceManager;
  }

  getHybridCoordinator(): any {
    return this.hybridCoordinator;
  }

  // Cleanup
  async dispose(): Promise<void> {
    console.log('🧹 Disposing Emergent AI Manager...');

    if (this.modelUpdateTimer) {
      clearInterval(this.modelUpdateTimer);
      this.modelUpdateTimer = undefined;
    }

    if (this.config.enableTensorFlow) {
      this.tfEngine.dispose();
    }

    this.deviceManager.dispose();
    this.removeAllListeners();
    this.isInitialized = false;

    console.log('✅ Emergent AI Manager disposed');
  }
}