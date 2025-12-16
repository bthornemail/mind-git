export interface NodeConfig {
  id: string;
  role: 'coordinator' | 'worker' | 'hybrid';
  mqttBroker: string;
  mqttPort: number;
  webrtcPort: number;
  webPort: number;
  aiInterval: number;
}

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