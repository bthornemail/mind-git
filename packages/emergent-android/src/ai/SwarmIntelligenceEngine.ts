import * as tf from '@tensorflow/tfjs';
import '@tensorflow/tfjs-backend-cpu';
import '@tensorflow/tfjs-backend-webgl';
import { EventEmitter } from 'events';

export interface SwarmNode {
  id: string;
  capabilities: {
    cpu: number;
    memory: number;
    battery: number;
    network: number;
  };
  role: 'coordinator' | 'worker' | 'hybrid';
  location?: { x: number; y: number };
}

export interface Task {
  id: string;
  type: 'computation' | 'sensing' | 'coordination' | 'mind-git-compile';
  requirements: {
    cpu: number;
    memory: number;
    battery: number;
    network: number;
  };
  payload: any;
  priority: number;
}

export interface ResourcePrediction {
  battery: number;
  memory: number;
  cpu: number;
  network: number;
  confidence: number;
}

export interface AllocationDecision {
  taskId: string;
  nodeId: string;
  confidence: number;
  expectedCompletion: number;
  reasoning: string;
}

export interface SwarmState {
  nodes: SwarmNode[];
  tasks: Task[];
  networkLatency: number;
  swarmHealth: number;
}

export class SwarmIntelligenceEngine extends EventEmitter {
  private models: Map<string, tf.LayersModel> = new Map();
  private isInitialized = false;
  private learningRate = 0.001;
  private federatedLearningRound = 0;
  
  constructor() {
    super();
  }

  async initialize(): Promise<void> {
    console.log('🧠 Initializing TensorFlow Swarm Intelligence Engine...');
    
    try {
      // Set up TensorFlow backend
      await tf.setBackend('webgl');
      console.log('✅ WebGL backend enabled');
    } catch (error) {
      console.log('⚠️ WebGL not available, falling back to CPU');
      await tf.setBackend('cpu');
    }

    // Initialize core models
    await this.initializeModels();
    
    this.isInitialized = true;
    console.log('✅ Swarm Intelligence Engine initialized');
    this.emit('initialized');
  }

  private async initializeModels(): Promise<void> {
    // Resource Prediction Model
    await this.loadModel('resource_predictor', this.createResourceModel());
    
    // Task Allocation Model  
    await this.loadModel('task_allocator', this.createAllocationModel());
    
    // Network Optimization Model
    await this.loadModel('network_optimizer', this.createNetworkModel());
    
    // Swarm Behavior Model (Boids)
    await this.loadModel('swarm_behavior', this.createSwarmBehaviorModel());
    
    // Anomaly Detection Model
    await this.loadModel('anomaly_detector', this.createAnomalyModel());
  }

  private createResourceModel(): tf.Sequential {
    return tf.sequential({
      layers: [
        tf.layers.dense({ 
          units: 16, 
          inputShape: [8], 
          activation: 'relu',
          kernelInitializer: 'heNormal'
        }),
        tf.layers.dropout({ rate: 0.2 }),
        tf.layers.dense({ units: 8, activation: 'relu' }),
        tf.layers.dense({ units: 4, activation: 'sigmoid' }) // battery, memory, cpu, network
      ]
    });
  }

  private createAllocationModel(): tf.Sequential {
    return tf.sequential({
      layers: [
        tf.layers.dense({ 
          units: 32, 
          inputShape: [20], 
          activation: 'relu',
          kernelInitializer: 'heNormal'
        }),
        tf.layers.dropout({ rate: 0.3 }),
        tf.layers.dense({ units: 16, activation: 'relu' }),
        tf.layers.dense({ units: 8, activation: 'relu' }),
        tf.layers.dense({ units: 1, activation: 'sigmoid' }) // allocation confidence
      ]
    });
  }

  private createNetworkModel(): tf.Sequential {
    return tf.sequential({
      layers: [
        tf.layers.dense({ 
          units: 24, 
          inputShape: [12], 
          activation: 'relu',
          kernelInitializer: 'heNormal'
        }),
        tf.layers.dense({ units: 12, activation: 'relu' }),
        tf.layers.dense({ units: 6, activation: 'relu' }),
        tf.layers.dense({ units: 3, activation: 'sigmoid' }) // routing decisions
      ]
    });
  }

  private createSwarmBehaviorModel(): tf.Sequential {
    return tf.sequential({
      layers: [
        tf.layers.dense({ 
          units: 16, 
          inputShape: [6], 
          activation: 'relu',
          kernelInitializer: 'heNormal'
        }),
        tf.layers.dense({ units: 8, activation: 'tanh' }), // Use tanh for bounded outputs
        tf.layers.dense({ units: 2, activation: 'tanh' }) // velocity changes (dx, dy)
      ]
    });
  }

  private createAnomalyModel(): tf.Sequential {
    return tf.sequential({
      layers: [
        tf.layers.dense({ 
          units: 32, 
          inputShape: [10], 
          activation: 'relu',
          kernelInitializer: 'heNormal'
        }),
        tf.layers.dense({ units: 16, activation: 'relu' }),
        tf.layers.dense({ units: 8, activation: 'relu' }),
        tf.layers.dense({ units: 1, activation: 'sigmoid' }) // anomaly probability
      ]
    });
  }

  private async loadModel(name: string, model: tf.LayersModel): Promise<void> {
    try {
      // Compile model
      const optimizer = tf.train.adam(this.learningRate);
      
      if (name === 'resource_predictor') {
        model.compile({
          optimizer,
          loss: 'meanSquaredError',
          metrics: ['mae']
        });
      } else if (name === 'task_allocator') {
        model.compile({
          optimizer,
          loss: 'binaryCrossentropy',
          metrics: ['accuracy']
        });
      } else if (name === 'anomaly_detector') {
        model.compile({
          optimizer,
          loss: 'binaryCrossentropy',
          metrics: ['precision', 'recall']
        });
      } else {
        model.compile({
          optimizer,
          loss: 'meanSquaredError'
        });
      }

      this.models.set(name, model);
      console.log(`✅ Model '${name}' loaded and compiled`);
    } catch (error) {
      console.error(`❌ Failed to load model '${name}':`, error);
      throw error;
    }
  }

  // Resource Prediction
  async predictResourceUsage(node: SwarmNode, historicalData?: number[]): Promise<ResourcePrediction> {
    const model = this.models.get('resource_predictor');
    if (!model) throw new Error('Resource predictor model not loaded');

    // Create feature vector: [cpu, memory, battery, network, role, location_x, location_y, time]
    const features = [
      node.capabilities.cpu / 100,
      node.capabilities.memory / 4096,
      node.capabilities.battery / 100,
      node.capabilities.network / 100,
      node.role === 'coordinator' ? 1 : node.role === 'hybrid' ? 0.5 : 0,
      node.location?.x || 0,
      node.location?.y || 0,
      new Date().getHours() / 24
    ];

    const input = tf.tensor2d([features]);
    const prediction = model.predict(input) as tf.Tensor;
    const values = await prediction.data();

    // Clean up tensors
    input.dispose();
    prediction.dispose();

    return {
      battery: Math.max(0, Math.min(100, values[0] * 100)),
      memory: Math.max(0, Math.min(4096, values[1] * 4096)),
      cpu: Math.max(0, Math.min(100, values[2] * 100)),
      network: Math.max(0, Math.min(100, values[3] * 100)),
      confidence: 0.85 // Base confidence, can be improved with ensemble
    };
  }

  // Task Allocation Optimization
  async optimizeTaskAllocation(tasks: Task[], nodes: SwarmNode[]): Promise<AllocationDecision[]> {
    const model = this.models.get('task_allocator');
    if (!model) throw new Error('Task allocator model not loaded');

    const decisions: AllocationDecision[] = [];

    for (const task of tasks) {
      let bestNode: SwarmNode | null = null;
      let bestConfidence = 0;

      for (const node of nodes) {
        // Create feature vector for this task-node pair
        const features = this.encodeTaskNodeFeatures(task, node);
        const input = tf.tensor2d([features]);
        const prediction = model.predict(input) as tf.Tensor;
        const confidence = (await prediction.data())[0];

        input.dispose();
        prediction.dispose();

        if (confidence > bestConfidence && this.canNodeHandleTask(node, task)) {
          bestConfidence = confidence;
          bestNode = node;
        }
      }

      if (bestNode) {
        decisions.push({
          taskId: task.id,
          nodeId: bestNode.id,
          confidence: bestConfidence,
          expectedCompletion: this.estimateCompletionTime(task, bestNode),
          reasoning: this.generateAllocationReasoning(task, bestNode, bestConfidence)
        });
      }
    }

    return decisions.sort((a, b) => b.confidence - a.confidence);
  }

  private encodeTaskNodeFeatures(task: Task, node: SwarmNode): number[] {
    return [
      // Task requirements (normalized)
      task.requirements.cpu / 100,
      task.requirements.memory / 4096,
      task.requirements.battery / 100,
      task.requirements.network / 100,
      task.priority / 10,
      
      // Node capabilities (normalized)
      node.capabilities.cpu / 100,
      node.capabilities.memory / 4096,
      node.capabilities.battery / 100,
      node.capabilities.network / 100,
      
      // Node role (encoded)
      node.role === 'coordinator' ? 1 : node.role === 'hybrid' ? 0.5 : 0,
      
      // Compatibility score
      this.calculateCompatibility(task, node),
      
      // Load factor
      this.calculateLoadFactor(node),
      
      // Network distance (if location available)
      node.location ? 0.5 : 1, // Placeholder
      new Date().getHours() / 24
    ];
  }

  private canNodeHandleTask(node: SwarmNode, task: Task): boolean {
    return (
      node.capabilities.cpu >= task.requirements.cpu &&
      node.capabilities.memory >= task.requirements.memory &&
      node.capabilities.battery >= task.requirements.battery &&
      node.capabilities.network >= task.requirements.network
    );
  }

  private calculateCompatibility(task: Task, node: SwarmNode): number {
    // Simple compatibility calculation
    const cpuScore = Math.min(1, node.capabilities.cpu / task.requirements.cpu);
    const memoryScore = Math.min(1, node.capabilities.memory / task.requirements.memory);
    const batteryScore = Math.min(1, node.capabilities.battery / task.requirements.battery);
    const networkScore = Math.min(1, node.capabilities.network / task.requirements.network);
    
    return (cpuScore + memoryScore + batteryScore + networkScore) / 4;
  }

  private calculateLoadFactor(node: SwarmNode): number {
    // Placeholder for actual load calculation
    return Math.random() * 0.5; // Simulated load
  }

  private estimateCompletionTime(task: Task, node: SwarmNode): number {
    // Simple estimation based on task complexity and node capabilities
    const complexity = task.requirements.cpu + task.requirements.memory / 100;
    const capability = node.capabilities.cpu + node.capabilities.memory / 100;
    return Math.max(1, (complexity / capability) * 60); // minutes
  }

  private generateAllocationReasoning(task: Task, node: SwarmNode, confidence: number): string {
    const reasons = [];
    
    if (node.capabilities.cpu > task.requirements.cpu * 1.5) {
      reasons.push('strong CPU capability');
    }
    if (node.capabilities.memory > task.requirements.memory * 1.5) {
      reasons.push('sufficient memory');
    }
    if (node.capabilities.battery > 50) {
      reasons.push('good battery level');
    }
    if (node.role === 'coordinator') {
      reasons.push('coordinator priority');
    }
    
    return `Allocated based on: ${reasons.join(', ')} (confidence: ${(confidence * 100).toFixed(1)}%)`;
  }

  // Swarm Behavior (Boids Algorithm)
  async calculateSwarmBehavior(nodes: SwarmNode[]): Promise<{ [nodeId: string]: { dx: number; dy: number } }> {
    const model = this.models.get('swarm_behavior');
    if (!model) throw new Error('Swarm behavior model not loaded');

    const movements: { [nodeId: string]: { dx: number; dy: number } } = {};

    for (const node of nodes) {
      if (!node.location) continue;

      // Calculate local neighborhood
      const neighbors = nodes.filter(n => 
        n.id !== node.id && 
        n.location && 
        this.calculateDistance(node.location, n.location) < 100
      );

      if (neighbors.length === 0) {
        movements[node.id] = { dx: 0, dy: 0 };
        continue;
      }

      // Create feature vector: [pos_x, pos_y, vel_x, vel_y, neighbor_count, avg_distance]
      const features = [
        node.location.x / 1000,
        node.location.y / 1000,
        0, // velocity_x (placeholder)
        0, // velocity_y (placeholder)
        neighbors.length / 10,
        this.calculateAverageDistance(node.location, neighbors) / 100
      ];

      const input = tf.tensor2d([features]);
      const prediction = model.predict(input) as tf.Tensor;
      const values = await prediction.data();

      input.dispose();
      prediction.dispose();

      movements[node.id] = {
        dx: values[0] * 10, // Scale movement
        dy: values[1] * 10
      };
    }

    return movements;
  }

  private calculateDistance(pos1: { x: number; y: number }, pos2: { x: number; y: number }): number {
    return Math.sqrt(Math.pow(pos2.x - pos1.x, 2) + Math.pow(pos2.y - pos1.y, 2));
  }

  private calculateAverageDistance(position: { x: number; y: number }, neighbors: SwarmNode[]): number {
    if (neighbors.length === 0) return 0;
    
    const totalDistance = neighbors.reduce((sum, neighbor) => {
      return sum + this.calculateDistance(position, neighbor.location!);
    }, 0);
    
    return totalDistance / neighbors.length;
  }

  // Network Optimization
  async optimizeNetworkRouting(swarmState: SwarmState): Promise<{ [sourceId: string]: string }> {
    const model = this.models.get('network_optimizer');
    if (!model) throw new Error('Network optimizer model not loaded');

    const routing: { [sourceId: string]: string } = {};

    for (const sourceNode of swarmState.nodes) {
      // Create feature vector for routing decision
      const features = [
        sourceNode.capabilities.network / 100,
        sourceNode.capabilities.cpu / 100,
        swarmState.networkLatency / 1000,
        swarmState.swarmHealth,
        swarmState.nodes.length / 10,
        swarmState.tasks.length / 20,
        sourceNode.role === 'coordinator' ? 1 : 0,
        new Date().getHours() / 24,
        Math.random(), // Network congestion (placeholder)
        Math.random(), // Packet loss rate (placeholder)
        Math.random(), // Bandwidth availability (placeholder)
        Math.random()  // Signal strength (placeholder)
      ];

      const input = tf.tensor2d([features]);
      const prediction = model.predict(input) as tf.Tensor;
      const values = await prediction.data();

      input.dispose();
      prediction.dispose();

      // Find best next hop based on prediction
      const candidates = swarmState.nodes
        .filter(n => n.id !== sourceNode.id)
        .sort((a, b) => {
          const scoreA = this.calculateRoutingScore(sourceNode, a, values);
          const scoreB = this.calculateRoutingScore(sourceNode, b, values);
          return scoreB - scoreA;
        });

      if (candidates.length > 0) {
        routing[sourceNode.id] = candidates[0].id;
      }
    }

    return routing;
  }

  private calculateRoutingScore(source: SwarmNode, target: SwarmNode, prediction: Float32Array): number {
    // Simple scoring based on network capability and distance
    const networkScore = target.capabilities.network / 100;
    const distanceScore = target.location ? 
      1 - (this.calculateDistance(source.location || { x: 0, y: 0 }, target.location) / 1000) : 0.5;
    
    return (networkScore + distanceScore) / 2;
  }

  // Anomaly Detection
  async detectAnomalies(swarmState: SwarmState): Promise<{ [nodeId: string]: number }> {
    const model = this.models.get('anomaly_detector');
    if (!model) throw new Error('Anomaly detector model not loaded');

    const anomalies: { [nodeId: string]: number } = {};

    for (const node of swarmState.nodes) {
      // Create feature vector for anomaly detection
      const features = [
        node.capabilities.cpu / 100,
        node.capabilities.memory / 4096,
        node.capabilities.battery / 100,
        node.capabilities.network / 100,
        swarmState.networkLatency / 1000,
        swarmState.swarmHealth,
        swarmState.tasks.length / 20,
        swarmState.nodes.length / 10,
        node.role === 'coordinator' ? 1 : 0,
        new Date().getHours() / 24
      ];

      const input = tf.tensor2d([features]);
      const prediction = model.predict(input) as tf.Tensor;
      const anomalyScore = (await prediction.data())[0];

      input.dispose();
      prediction.dispose();

      anomalies[node.id] = anomalyScore;
    }

    return anomalies;
  }

  // Federated Learning
  async learnFromExperience(experience: {
    state: any;
    action: any;
    reward: number;
    nextState: any;
  }): Promise<void> {
    const model = this.models.get('task_allocator');
    if (!model) return;

    // Convert experience to training data
    const stateTensor = tf.tensor2d([this.encodeExperienceState(experience.state)]);
    const rewardTensor = tf.tensor2d([[experience.reward]]);

    // Perform gradient descent step
    const optimizer = tf.train.adam(this.learningRate);
    
    optimizer.minimize(() => {
      const prediction = model.predict(stateTensor) as tf.Tensor;
      return tf.losses.meanSquaredError(rewardTensor, prediction);
    });

    // Clean up tensors
    stateTensor.dispose();
    rewardTensor.dispose();

    // Increment federated learning round
    this.federatedLearningRound++;
    
    // Share model updates periodically
    if (this.federatedLearningRound % 10 === 0) {
      await this.shareModelUpdate();
    }

    this.emit('learning', { round: this.federatedLearningRound, reward: experience.reward });
  }

  private encodeExperienceState(state: any): number[] {
    // Encode state for training (simplified)
    return [
      state.cpuUsage || 0,
      state.memoryUsage || 0,
      state.batteryLevel || 0,
      state.networkLatency || 0,
      state.taskCount || 0,
      state.nodeCount || 0,
      state.swarmHealth || 0,
      Math.random() // Additional features
    ];
  }

  private async shareModelUpdate(): Promise<void> {
    const model = this.models.get('task_allocator');
    if (!model) return;

    try {
      // Get model weights
      const weights = model.getWeights();
      
      // Convert to compact format for transmission
      const compressedWeights = await this.compressWeights(weights);
      
      // Emit update event for MQTT transmission
      this.emit('modelUpdate', {
        model: 'task_allocator',
        weights: compressedWeights,
        round: this.federatedLearningRound,
        timestamp: Date.now()
      });
      
      console.log(`📡 Shared model update for round ${this.federatedLearningRound}`);
    } catch (error) {
      console.error('❌ Failed to share model update:', error);
    }
  }

  private async compressWeights(weights: tf.Tensor[]): Promise<number[]> {
    // Simple compression: flatten and quantize
    const allWeights: number[] = [];
    
    for (const weight of weights) {
      const values = await weight.data();
      // Quantize to 8-bit precision
      for (let i = 0; i < values.length; i += 4) {
        allWeights.push(Math.round(values[i] * 127));
      }
    }
    
    return allWeights;
  }

  // Particle Swarm Optimization for complex problems
  async particleSwarmOptimization(
    objective: (x: number[]) => number,
    dimensions: number = 3,
    swarmSize: number = 20,
    maxIterations: number = 100
  ): Promise<{ bestSolution: number[]; bestFitness: number; iterations: number }> {
    console.log(`🔍 Starting PSO: ${swarmSize} particles, ${dimensions}D, ${maxIterations} iterations`);

    // Initialize particles
    const particles: Array<{ position: number[]; velocity: number[]; bestPosition: number[]; bestFitness: number }> = [];
    
    for (let i = 0; i < swarmSize; i++) {
      const position = Array(dimensions).fill(0).map(() => Math.random() * 10 - 5);
      const velocity = Array(dimensions).fill(0).map(() => Math.random() * 0.2 - 0.1);
      const fitness = objective(position);
      
      particles.push({
        position,
        velocity,
        bestPosition: [...position],
        bestFitness: fitness
      });
    }

    // Global best
    let globalBestPosition = particles[0].bestPosition;
    let globalBestFitness = particles[0].bestFitness;

    for (const particle of particles) {
      if (particle.bestFitness < globalBestFitness) {
        globalBestFitness = particle.bestFitness;
        globalBestPosition = [...particle.bestPosition];
      }
    }

    // PSO parameters
    const w = 0.7; // Inertia weight
    const c1 = 1.5; // Cognitive coefficient
    const c2 = 1.5; // Social coefficient

    // Optimization loop
    for (let iter = 0; iter < maxIterations; iter++) {
      for (const particle of particles) {
        for (let d = 0; d < dimensions; d++) {
          // Update velocity
          const r1 = Math.random();
          const r2 = Math.random();
          
          particle.velocity[d] = 
            w * particle.velocity[d] +
            c1 * r1 * (particle.bestPosition[d] - particle.position[d]) +
            c2 * r2 * (globalBestPosition[d] - particle.position[d]);
          
          // Update position
          particle.position[d] += particle.velocity[d];
          
          // Clamp position
          particle.position[d] = Math.max(-10, Math.min(10, particle.position[d]));
        }

        // Evaluate fitness
        const fitness = objective(particle.position);
        
        // Update personal best
        if (fitness < particle.bestFitness) {
          particle.bestFitness = fitness;
          particle.bestPosition = [...particle.position];
          
          // Update global best
          if (fitness < globalBestFitness) {
            globalBestFitness = fitness;
            globalBestPosition = [...particle.position];
          }
        }
      }

      // Emit progress
      if (iter % 10 === 0) {
        this.emit('psoProgress', { 
          iteration: iter, 
          bestFitness: globalBestFitness,
          bestPosition: globalBestPosition
        });
      }
    }

    console.log(`✅ PSO Complete: Best fitness = ${globalBestFitness.toFixed(6)}`);

    return {
      bestSolution: globalBestPosition,
      bestFitness: globalBestFitness,
      iterations: maxIterations
    };
  }

  // Health monitoring
  async getSwarmHealth(swarmState: SwarmState): Promise<{
    overall: number;
    cpu: number;
    memory: number;
    battery: number;
    network: number;
    anomalies: number;
  }> {
    const anomalies = await this.detectAnomalies(swarmState);
    const anomalyCount = Object.values(anomalies).filter(score => score > 0.7).length;

    // Calculate average resource levels
    const avgCpu = swarmState.nodes.reduce((sum, n) => sum + n.capabilities.cpu, 0) / swarmState.nodes.length;
    const avgMemory = swarmState.nodes.reduce((sum, n) => sum + n.capabilities.memory, 0) / swarmState.nodes.length;
    const avgBattery = swarmState.nodes.reduce((sum, n) => sum + n.capabilities.battery, 0) / swarmState.nodes.length;
    const avgNetwork = swarmState.nodes.reduce((sum, n) => sum + n.capabilities.network, 0) / swarmState.nodes.length;

    // Calculate overall health (0-100)
    const resourceHealth = (avgCpu + avgMemory / 40.96 + avgBattery + avgNetwork) / 4;
    const anomalyPenalty = (anomalyCount / swarmState.nodes.length) * 20;
    const overall = Math.max(0, Math.min(100, resourceHealth - anomalyPenalty));

    return {
      overall,
      cpu: avgCpu,
      memory: avgMemory,
      battery: avgBattery,
      network: avgNetwork,
      anomalies: anomalyCount
    };
  }

  // Cleanup
  dispose(): void {
    console.log('🧹 Disposing TensorFlow models...');
    
    for (const [name, model] of this.models) {
      model.dispose();
      console.log(`✅ Disposed model: ${name}`);
    }
    
    this.models.clear();
    this.isInitialized = false;
  }

  // Get model info for debugging
  getModelInfo(): { [name: string]: any } {
    const info: { [name: string]: any } = {};
    
    for (const [name, model] of this.models) {
      info[name] = {
        layers: model.layers.length,
        params: model.countParams(),
        inputShape: model.inputs[0].shape,
        outputShape: model.outputs[0].shape
      };
    }
    
    return info;
  }
}