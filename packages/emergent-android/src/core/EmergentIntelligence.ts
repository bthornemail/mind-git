import { EmergentAIManager, EmergentAIConfig } from '../ai/EmergentAIManager';
import { SwarmNode, Task, SwarmState } from '../ai/SwarmIntelligenceEngine';
import { EventEmitter } from 'events';

export interface NodeConfig {
  id: string;
  role: 'coordinator' | 'worker' | 'hybrid';
  mqttBroker: string;
  mqttPort: number;
  webrtcPort: number;
  webPort: number;
  aiInterval: number;
  location?: { x: number; y: number };
}

export interface SwarmStatus {
  nodeId: string;
  role: string;
  status: 'initializing' | 'active' | 'idle' | 'error';
  uptime: number;
  tasksProcessed: number;
  decisionsMade: number;
  learningRounds: number;
  swarmHealth: number;
  capabilities: any;
}

export class EmergentIntelligence extends EventEmitter {
  private config: NodeConfig;
  private aiManager: EmergentAIManager;
  private isRunning = false;
  private startTime = 0;
  private status: SwarmStatus;
  private decisionTimer?: NodeJS.Timeout;
  private metricsTimer?: NodeJS.Timeout;

  constructor(config: NodeConfig) {
    super();
    this.config = config;
    
    // Initialize AI configuration based on node role
    const aiConfig: EmergentAIConfig = this.getAIConfigForRole(config.role);
    
    this.aiManager = new EmergentAIManager(aiConfig);
    
    this.status = {
      nodeId: config.id,
      role: config.role,
      status: 'initializing',
      uptime: 0,
      tasksProcessed: 0,
      decisionsMade: 0,
      learningRounds: 0,
      swarmHealth: 100,
      capabilities: {}
    };
  }

  private getAIConfigForRole(role: string): EmergentAIConfig {
    switch (role) {
      case 'coordinator':
        return {
          enableTensorFlow: true,
          enableLLM: true,
          llmEndpoint: process.env.LLM_ENDPOINT || 'http://localhost:11434',
          intelligenceLevel: 'hybrid',
          learningRate: 0.001,
          federatedLearning: true,
          modelUpdateInterval: 30000 // 30 seconds for coordinators
        };
      
      case 'hybrid':
        return {
          enableTensorFlow: true,
          enableLLM: true,
          llmEndpoint: process.env.LLM_ENDPOINT,
          intelligenceLevel: 'advanced',
          learningRate: 0.0008,
          federatedLearning: true,
          modelUpdateInterval: 60000 // 1 minute for hybrids
        };
      
      case 'worker':
      default:
        return {
          enableTensorFlow: true,
          enableLLM: false,
          intelligenceLevel: 'enhanced',
          learningRate: 0.0005,
          federatedLearning: true,
          modelUpdateInterval: 120000 // 2 minutes for workers
        };
    }
  }

  async initialize(): Promise<void> {
    console.log(`🧠 Initializing Emergent Intelligence Node: ${this.config.id}`);
    
    try {
      // Initialize AI manager
      await this.aiManager.initialize();
      
      // Set up event listeners
      this.setupEventListeners();
      
      // Update status
      this.status.status = 'idle';
      this.status.capabilities = this.aiManager.getCapabilities();
      
      console.log(`✅ Node ${this.config.id} initialized successfully`);
      this.emit('initialized', this.status);
    } catch (error) {
      console.error(`❌ Failed to initialize node ${this.config.id}:`, error);
      this.status.status = 'error';
      throw error;
    }
  }

  private setupEventListeners(): void {
    // AI Manager events
    this.aiManager.on('decisionMade', (data) => {
      this.status.decisionsMade++;
      this.emit('decision', data);
    });

    this.aiManager.on('learning', (data) => {
      this.status.learningRounds = data.round;
      this.emit('learning', data);
    });

    this.aiManager.on('modelUpdate', (data) => {
      this.emit('modelUpdate', data);
    });

    this.aiManager.on('optimization', (data) => {
      this.emit('optimization', data);
    });

    this.aiManager.on('capabilitiesUpdated', (capabilities) => {
      this.status.capabilities = capabilities;
      this.emit('capabilitiesUpdated', capabilities);
    });
  }

  async start(): Promise<void> {
    if (this.isRunning) {
      console.log(`⚠️ Node ${this.config.id} is already running`);
      return;
    }

    console.log(`🚀 Starting Emergent Intelligence Node: ${this.config.id}`);
    
    this.isRunning = true;
    this.startTime = Date.now();
    this.status.status = 'active';

    // Start periodic decision making
    this.startDecisionMaking();

    // Start metrics collection
    this.startMetricsCollection();

    console.log(`✅ Node ${this.config.id} started successfully`);
    this.emit('started', this.status);
  }

  private startDecisionMaking(): void {
    if (this.decisionTimer) {
      clearInterval(this.decisionTimer);
    }

    this.decisionTimer = setInterval(async () => {
      try {
        await this.makePeriodicDecision();
      } catch (error) {
        console.error(`❌ Decision making failed for node ${this.config.id}:`, error);
      }
    }, this.config.aiInterval * 1000);

    console.log(`🔄 Decision making started (interval: ${this.config.aiInterval}s)`);
  }

  private startMetricsCollection(): void {
    if (this.metricsTimer) {
      clearInterval(this.metricsTimer);
    }

    this.metricsTimer = setInterval(async () => {
      try {
        await this.updateMetrics();
      } catch (error) {
        console.error(`❌ Metrics update failed for node ${this.config.id}:`, error);
      }
    }, 5000); // Update every 5 seconds

    console.log('📊 Metrics collection started');
  }

  private async makePeriodicDecision(): Promise<void> {
    // Create a mock decision context for demonstration
    const context = this.createDecisionContext();
    
    const decision = await this.aiManager.makeDecision(context);
    
    console.log(`🧠 Decision made for node ${this.config.id}:`, {
      action: decision.action,
      confidence: (decision.confidence * 100).toFixed(1) + '%',
      allocations: decision.allocation?.length || 0
    });

    // Learn from decision (mock experience)
    if (Math.random() > 0.7) { // 30% chance of learning
      await this.aiManager.learnFromExperience({
        state: context,
        action: decision,
        reward: decision.confidence * (Math.random() * 0.4 + 0.8), // Random reward 0.8-1.2
        nextState: context
      });
    }
  }

  private createDecisionContext(): any {
    // Create mock tasks and nodes for demonstration
    const tasks: Task[] = [
      {
        id: `task-${Date.now()}`,
        type: ['computation', 'sensing', 'coordination'][Math.floor(Math.random() * 3)] as Task['type'],
        requirements: {
          cpu: Math.random() * 50 + 10,
          memory: Math.random() * 1024 + 256,
          battery: Math.random() * 20 + 5,
          network: Math.random() * 40 + 10
        },
        payload: {},
        priority: Math.random() * 10
      }
    ];

    const nodes: SwarmNode[] = [
      {
        id: this.config.id,
        capabilities: {
          cpu: 80,
          memory: 2048,
          battery: 75,
          network: 60
        },
        role: this.config.role,
        location: this.config.location || { x: 0, y: 0 }
      }
    ];

    const swarmState: SwarmState = {
      nodes,
      tasks,
      networkLatency: Math.random() * 100 + 20,
      swarmHealth: this.status.swarmHealth
    };

    return {
      tasks,
      nodes,
      swarmState,
      complexity: 1,
      hasUnusualConstraints: Math.random() > 0.8,
      requiresExplanation: Math.random() > 0.9
    };
  }

  private async updateMetrics(): Promise<void> {
    this.status.uptime = Date.now() - this.startTime;
    
    // Update swarm health from AI manager
    const aiMetrics = this.aiManager.getMetrics();
    this.status.swarmHealth = aiMetrics.swarmHealth;
    
    // Emit metrics update
    this.emit('metrics', this.status);
  }

  async stop(): Promise<void> {
    if (!this.isRunning) {
      console.log(`⚠️ Node ${this.config.id} is not running`);
      return;
    }

    console.log(`🛑 Stopping Emergent Intelligence Node: ${this.config.id}`);
    
    this.isRunning = false;
    this.status.status = 'idle';

    // Clear timers
    if (this.decisionTimer) {
      clearInterval(this.decisionTimer);
      this.decisionTimer = undefined;
    }

    if (this.metricsTimer) {
      clearInterval(this.metricsTimer);
      this.metricsTimer = undefined;
    }

    console.log(`✅ Node ${this.config.id} stopped successfully`);
    this.emit('stopped', this.status);
  }

  // Public API methods

  async processTask(task: Task): Promise<{
    taskId: string;
    nodeId: string;
    status: 'accepted' | 'rejected' | 'completed';
    result?: any;
    reasoning?: string;
  }> {
    console.log(`📋 Processing task ${task.id} on node ${this.config.id}`);

    try {
      // Create decision context for this specific task
      const context = {
        tasks: [task],
        nodes: [{
          id: this.config.id,
          capabilities: this.status.capabilities.device || {
            cpu: 80,
            memory: 2048,
            battery: 75,
            network: 60
          },
          role: this.config.role,
          location: this.config.location
        }],
        swarmState: {
          nodes: [],
          tasks: [task],
          networkLatency: 50,
          swarmHealth: this.status.swarmHealth
        },
        complexity: 1,
        hasUnusualConstraints: false,
        requiresExplanation: false
      };

      // Make decision about task
      const decision = await this.aiManager.makeDecision(context);

      if (decision.confidence > 0.5 && decision.allocation && decision.allocation.length > 0) {
        // Task accepted
        this.status.tasksProcessed++;
        
        // Simulate task processing
        await new Promise(resolve => setTimeout(resolve, Math.random() * 2000 + 500));

        const result = {
          taskId: task.id,
          nodeId: this.config.id,
          status: 'completed' as const,
          result: {
            output: `Task ${task.id} processed successfully`,
            processingTime: Math.random() * 1500 + 500,
            confidence: decision.confidence
          },
          reasoning: decision.reasoning
        };

        // Learn from experience
        await this.aiManager.learnFromExperience({
          state: context,
          action: decision,
          reward: 0.9, // Good outcome
          nextState: context
        });

        console.log(`✅ Task ${task.id} completed successfully`);
        this.emit('taskCompleted', result);
        
        return result;
      } else {
        // Task rejected
        const result = {
          taskId: task.id,
          nodeId: this.config.id,
          status: 'rejected' as const,
          reasoning: decision.reasoning || 'Insufficient confidence or resources'
        };

        console.log(`❌ Task ${task.id} rejected: ${result.reasoning}`);
        this.emit('taskRejected', result);
        
        return result;
      }
    } catch (error) {
      console.error(`❌ Error processing task ${task.id}:`, error);
      
      const result = {
        taskId: task.id,
        nodeId: this.config.id,
        status: 'rejected' as const,
        reasoning: `Processing error: ${error.message}`
      };

      this.emit('taskError', result);
      return result;
    }
  }

  async optimizeSwarm(swarmState: SwarmState): Promise<{
    routing: { [sourceId: string]: string };
    behavior: { [nodeId: string]: { dx: number; dy: number } };
    health: any;
    anomalies: { [nodeId: string]: number };
  }> {
    console.log(`🔧 Optimizing swarm from node ${this.config.id}`);
    
    try {
      const optimization = await this.aiManager.optimizeSwarm(swarmState);
      
      console.log(`✅ Swarm optimization completed:`, {
        routingRules: Object.keys(optimization.routing).length,
        behaviorUpdates: Object.keys(optimization.behavior).length,
        health: optimization.health.overall.toFixed(1) + '%',
        anomalies: Object.keys(optimization.anomalies).filter(id => optimization.anomalies[id] > 0.7).length
      });

      this.emit('swarmOptimized', optimization);
      return optimization;
    } catch (error) {
      console.error(`❌ Swarm optimization failed:`, error);
      throw error;
    }
  }

  async solveProblem(
    objective: (x: number[]) => number,
    dimensions: number = 3,
    options?: { swarmSize?: number; maxIterations?: number }
  ): Promise<{ bestSolution: number[]; bestFitness: number }> {
    console.log(`🔍 Solving optimization problem (${dimensions}D) from node ${this.config.id}`);
    
    try {
      const result = await this.aiManager.solveOptimizationProblem(objective, dimensions, options);
      
      console.log(`✅ Problem solved:`, {
        bestSolution: result.bestSolution.map(v => v.toFixed(3)),
        bestFitness: result.bestFitness.toFixed(6)
      });

      this.emit('problemSolved', result);
      return result;
    } catch (error) {
      console.error(`❌ Problem solving failed:`, error);
      throw error;
    }
  }

  // Status and monitoring
  getStatus(): SwarmStatus {
    return { ...this.status };
  }

  async getDetailedStatus(): Promise<any> {
    return await this.aiManager.getDetailedStatus();
  }

  async runBenchmark(iterations: number = 10): Promise<any> {
    console.log(`🏃 Running benchmark on node ${this.config.id} (${iterations} iterations)`);
    
    try {
      const results = await this.aiManager.runBenchmark(iterations);
      
      console.log(`📊 Benchmark results for node ${this.config.id}:`, {
        overall: `${results.overall.score} (${results.overall.grade})`,
        decisionMaking: `${results.decisionMaking.avgTime.toFixed(1)}ms avg, ${(results.decisionMaking.avgConfidence * 100).toFixed(1)}% confidence`,
        optimization: `${results.optimization.avgTime.toFixed(1)}ms avg`
      });

      this.emit('benchmarkCompleted', results);
      return results;
    } catch (error) {
      console.error(`❌ Benchmark failed:`, error);
      throw error;
    }
  }

  // Configuration
  async updateConfig(config: Partial<NodeConfig>): Promise<void> {
    console.log(`⚙️ Updating configuration for node ${this.config.id}`);
    
    const oldConfig = { ...this.config };
    this.config = { ...this.config, ...config };
    
    // Update AI configuration if role changed
    if (oldConfig.role !== config.role) {
      const newAIConfig = this.getAIConfigForRole(this.config.role);
      await this.aiManager.updateConfig(newAIConfig);
    }

    // Update decision interval if changed
    if (oldConfig.aiInterval !== config.aiInterval && this.isRunning) {
      this.startDecisionMaking();
    }

    this.status.role = this.config.role;
    console.log(`✅ Configuration updated for node ${this.config.id}`);
    this.emit('configUpdated', this.config);
  }

  // Cleanup
  async dispose(): Promise<void> {
    console.log(`🧹 Disposing Emergent Intelligence Node: ${this.config.id}`);
    
    await this.stop();
    await this.aiManager.dispose();
    
    this.removeAllListeners();
    console.log(`✅ Node ${this.config.id} disposed`);
  }
}

export default EmergentIntelligence;

export interface NetworkNode {
  id: string;
  ip: string;
  role: string;
  status: 'online' | 'offline' | 'busy';
  lastSeen: Date;
  battery?: number;
  cpu?: number;
  memory?: number;
}

export interface AIState {
  mode: 'normal' | 'energy-saving' | 'performance';
  decisionThreshold: number;
  collaborationWeight: number;
  lastDecision: Date;
  confidence: number;
}

export interface SwarmMessage {
  type: 'health' | 'task' | 'decision' | 'coordination' | 'emergency';
  from: string;
  to?: string;
  timestamp: Date;
  payload: any;
  priority: 'low' | 'medium' | 'high' | 'critical';
}

export interface TaskDistribution {
  taskId: string;
  type: 'mind-git-compile' | 'computation' | 'sensing' | 'coordination';
  assignedNodes: string[];
  status: 'pending' | 'running' | 'completed' | 'failed';
  progress: number;
  result?: any;
  payload?: any;
}

export interface EmergentSystem {
  config: NodeConfig;
  networkNodes: Map<string, NetworkNode>;
  aiState: AIState;
  activeTasks: Map<string, TaskDistribution>;
  messageHistory: SwarmMessage[];
}

export class EmergentIntelligence {
  private system: EmergentSystem;
  private mqttClient: any;
  private webSocketServer: any;
  private aiInterval: NodeJS.Timeout | null = null;
  public messageHistory: SwarmMessage[] = [];

  constructor(config: NodeConfig) {
    this.system = {
      config,
      networkNodes: new Map(),
      aiState: {
        mode: 'normal',
        decisionThreshold: 0.7,
        collaborationWeight: 0.8,
        lastDecision: new Date(),
        confidence: 0.5
      },
      activeTasks: new Map(),
      messageHistory: []
    };
  }

  async initialize(): Promise<void> {
    console.log(`🧠 Initializing Emergent Intelligence Node: ${this.system.config.id}`);
    
    await this.initializeMQTT();
    await this.initializeWebSocket();
    await this.initializeAI();
    await this.startHealthMonitoring();
    
    console.log(`✅ Emergent Intelligence Node ${this.system.config.id} ready`);
  }

  private async initializeMQTT(): Promise<void> {
    const mqtt = require('mqtt');
    const { mqttBroker, mqttPort } = this.system.config;
    
    this.mqttClient = mqtt.connect(`mqtt://${mqttBroker}:${mqttPort}`, {
      clientId: this.system.config.id,
      keepalive: 60
    });

    this.mqttClient.on('connect', () => {
      console.log(`📡 Connected to MQTT broker at ${mqttBroker}:${mqttPort}`);
      this.setupMQTTSubscriptions();
    });

    this.mqttClient.on('message', (topic: string, message: Buffer) => {
      this.handleMQTTMessage(topic, message);
    });
  }

  private setupMQTTSubscriptions(): void {
    const topics = [
      'swarm/health',
      'swarm/tasks',
      'swarm/decisions',
      'swarm/emergency',
      `nodes/${this.system.config.id}/#`
    ];

    topics.forEach(topic => {
      this.mqttClient.subscribe(topic);
    });
  }

  private handleMQTTMessage(topic: string, message: Buffer): void {
    try {
      const swarmMessage: SwarmMessage = JSON.parse(message.toString());
      this.system.messageHistory.push(swarmMessage);
      
      switch (swarmMessage.type) {
        case 'health':
          this.handleHealthUpdate(swarmMessage);
          break;
        case 'task':
          this.handleTaskDistribution(swarmMessage);
          break;
        case 'decision':
          this.handleDecisionMessage(swarmMessage);
          break;
        case 'emergency':
          this.handleEmergencyMessage(swarmMessage);
          break;
      }
    } catch (error) {
      console.error(`❌ Error processing MQTT message: ${error}`);
    }
  }

  private handleHealthUpdate(message: SwarmMessage): void {
    const nodeData = message.payload;
    this.system.networkNodes.set(message.from, {
      ...nodeData,
      lastSeen: new Date()
    });
  }

  private handleTaskDistribution(message: SwarmMessage): void {
    const task = message.payload as TaskDistribution;
    this.system.activeTasks.set(task.taskId, task);
    
    if (task.assignedNodes.includes(this.system.config.id)) {
      this.executeTask(task);
    }
  }

  private handleDecisionMessage(message: SwarmMessage): void {
    // Process decisions from other nodes
    this.updateAIState(message.payload);
  }

  private handleEmergencyMessage(message: SwarmMessage): void {
    console.log(`🚨 EMERGENCY: ${message.payload.message}`);
    this.activateEmergencyProtocol(message.payload);
  }

  private async executeTask(task: TaskDistribution): Promise<void> {
    console.log(`🔧 Executing task: ${task.taskId}`);
    
    try {
      switch (task.type) {
        case 'mind-git-compile':
          await this.executeMindGitCompile(task);
          break;
        case 'computation':
          await this.executeComputation(task);
          break;
        case 'sensing':
          await this.executeSensing(task);
          break;
        case 'coordination':
          await this.executeCoordination(task);
          break;
      }
    } catch (error) {
      console.error(`❌ Task execution failed: ${error}`);
      task.status = 'failed';
    }
  }

  private async executeMindGitCompile(task: TaskDistribution): Promise<void> {
    const { spawn } = require('child_process');
    
    return new Promise((resolve, reject) => {
      const process = spawn('mind-git', ['compile', task.payload.canvasFile]);
      
      process.stdout.on('data', (data: Buffer) => {
        console.log(`📝 mind-git output: ${data.toString()}`);
      });
      
      process.on('close', (code: number) => {
        if (code === 0) {
          task.status = 'completed';
          task.progress = 100;
          resolve();
        } else {
          reject(new Error(`mind-git compilation failed with code ${code}`));
        }
      });
    });
  }

  private async executeComputation(task: TaskDistribution): Promise<void> {
    // Simulate computational work
    await new Promise(resolve => setTimeout(resolve, 2000));
    task.status = 'completed';
    task.progress = 100;
    task.result = { computationResult: Math.random() * 1000 };
  }

  private async executeSensing(task: TaskDistribution): Promise<void> {
    // Simulate sensor data collection
    task.result = {
      timestamp: new Date(),
      battery: Math.random() * 100,
      cpu: Math.random() * 100,
      memory: Math.random() * 100,
      location: {
        lat: 37.7749 + (Math.random() - 0.5) * 0.01,
        lng: -122.4194 + (Math.random() - 0.5) * 0.01
      }
    };
    task.status = 'completed';
    task.progress = 100;
  }

  private async executeCoordination(task: TaskDistribution): Promise<void> {
    // Handle coordination tasks
    const decision = await this.makeAIDecision(task.payload);
    task.result = { decision };
    task.status = 'completed';
    task.progress = 100;
  }

  private async initializeWebSocket(): Promise<void> {
    const WebSocket = require('ws');
    const { webrtcPort } = this.system.config;
    
    this.webSocketServer = new WebSocket.Server({ port: webrtcPort });
    
    this.webSocketServer.on('connection', (ws: any) => {
      console.log(`🔗 WebSocket connection established`);
      
      ws.on('message', (message: Buffer) => {
        this.handleWebSocketMessage(ws, message);
      });
    });
  }

  private handleWebSocketMessage(ws: any, message: Buffer): void {
    try {
      const data = JSON.parse(message.toString());
      
      switch (data.type) {
        case 'status':
          ws.send(JSON.stringify({
            type: 'status-response',
            payload: this.getSystemStatus()
          }));
          break;
        case 'task':
          this.distributeTask(data.payload);
          break;
      }
    } catch (error) {
      console.error(`❌ WebSocket message error: ${error}`);
    }
  }

  private async initializeAI(): Promise<void> {
    const { aiInterval } = this.system.config;
    
    this.aiInterval = setInterval(async () => {
      await this.makeAIDecision();
    }, aiInterval * 1000);
  }

  private async makeAIDecision(context?: any): Promise<any> {
    const decision = {
      nodeId: this.system.config.id,
      timestamp: new Date(),
      mode: this.system.aiState.mode,
      action: 'continue',
      confidence: this.system.aiState.confidence,
      reasoning: 'Emergent intelligence decision based on network state'
    };

    // Publish decision to swarm
    this.publishMessage('swarm/decisions', {
      type: 'decision',
      from: this.system.config.id,
      timestamp: new Date(),
      payload: decision,
      priority: 'medium'
    } as SwarmMessage);

    return decision;
  }

  private updateAIState(newData: any): void {
    // Adapt AI state based on network feedback
    this.system.aiState.confidence = Math.min(1.0, this.system.aiState.confidence + 0.01);
    this.system.aiState.lastDecision = new Date();
  }

  private async startHealthMonitoring(): Promise<void> {
    setInterval(() => {
      this.broadcastHealth();
    }, 15000); // Every 15 seconds
  }

  private broadcastHealth(): void {
    const healthData = {
      id: this.system.config.id,
      ip: 'localhost',
      role: this.system.config.role,
      status: 'online',
      battery: Math.random() * 100,
      cpu: Math.random() * 100,
      memory: Math.random() * 100,
      timestamp: new Date()
    };

    this.publishMessage('swarm/health', {
      type: 'health',
      from: this.system.config.id,
      timestamp: new Date(),
      payload: healthData,
      priority: 'low'
    } as SwarmMessage);
  }

  private publishMessage(topic: string, message: SwarmMessage): void {
    if (this.mqttClient && this.mqttClient.connected) {
      this.mqttClient.publish(topic, JSON.stringify(message));
    }
  }

  private distributeTask(task: any): void {
    const taskDistribution: TaskDistribution = {
      taskId: `task-${Date.now()}`,
      type: task.type || 'computation',
      assignedNodes: this.selectOptimalNodes(task.requirements || {}),
      status: 'pending',
      progress: 0
    };

    this.publishMessage('swarm/tasks', {
      type: 'task',
      from: this.system.config.id,
      timestamp: new Date(),
      payload: taskDistribution,
      priority: 'medium'
    } as SwarmMessage);
  }

  private selectOptimalNodes(requirements: any): string[] {
    const availableNodes = Array.from(this.system.networkNodes.values())
      .filter(node => node.status === 'online')
      .sort((a, b) => (b.battery || 0) - (a.battery || 0));

    return availableNodes.slice(0, Math.min(3, availableNodes.length)).map(node => node.id);
  }

  private activateEmergencyProtocol(emergencyData: any): void {
    this.system.aiState.mode = 'energy-saving';
    console.log(`🚨 Emergency protocol activated: ${emergencyData.type}`);
  }

  private getSystemStatus(): any {
    return {
      nodeId: this.system.config.id,
      role: this.system.config.role,
      networkNodes: Array.from(this.system.networkNodes.values()),
      aiState: this.system.aiState,
      activeTasks: Array.from(this.system.activeTasks.values()),
      uptime: process.uptime()
    };
  }

  async shutdown(): Promise<void> {
    console.log(`🛑 Shutting down Emergent Intelligence Node: ${this.system.config.id}`);
    
    if (this.aiInterval) {
      clearInterval(this.aiInterval);
    }
    
    if (this.mqttClient) {
      this.mqttClient.end();
    }
    
    if (this.webSocketServer) {
      this.webSocketServer.close();
    }
  }
}