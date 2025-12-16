import { EventEmitter } from 'events';

export interface DeviceCapabilities {
  cpu: number;
  memory: number;
  storage: number;
  battery: number;
  network: number;
  gpu: boolean;
  llmCapable: boolean;
  tensorFlowCapable: boolean;
}

export interface IntelligenceLevel {
  level: 'basic' | 'enhanced' | 'advanced' | 'hybrid';
  features: string[];
  models: string[];
  performance: {
    inferenceTime: number;
    memoryUsage: number;
    accuracy: number;
  };
}

export class DeviceIntelligenceManager extends EventEmitter {
  private capabilities: DeviceCapabilities;
  private currentLevel: IntelligenceLevel;
  private isInitialized = false;

  constructor() {
    super();
    this.capabilities = this.getDefaultCapabilities();
    this.currentLevel = this.getBasicLevel();
  }

  async initialize(): Promise<void> {
    console.log('🔧 Initializing Device Intelligence Manager...');
    
    // Detect device capabilities
    await this.detectCapabilities();
    
    // Determine optimal intelligence level
    await this.determineIntelligenceLevel();
    
    this.isInitialized = true;
    console.log(`✅ Intelligence level set to: ${this.currentLevel.level}`);
    this.emit('initialized', this.currentLevel);
  }

  private getDefaultCapabilities(): DeviceCapabilities {
    return {
      cpu: 50,
      memory: 2048,
      storage: 8000,
      battery: 100,
      network: 50,
      gpu: false,
      llmCapable: false,
      tensorFlowCapable: true
    };
  }

  private getBasicLevel(): IntelligenceLevel {
    return {
      level: 'basic',
      features: ['resource_monitoring', 'basic_optimization'],
      models: ['resource_predictor'],
      performance: {
        inferenceTime: 50,
        memoryUsage: 100,
        accuracy: 0.75
      }
    };
  }

  private async detectCapabilities(): Promise<void> {
    console.log('🔍 Detecting device capabilities...');

    // CPU detection
    this.capabilities.cpu = await this.detectCPUCapability();
    
    // Memory detection
    this.capabilities.memory = await this.detectMemoryCapability();
    
    // Storage detection
    this.capabilities.storage = await this.detectStorageCapability();
    
    // Battery detection
    this.capabilities.battery = await this.detectBatteryLevel();
    
    // Network detection
    this.capabilities.network = await this.detectNetworkCapability();
    
    // GPU detection
    this.capabilities.gpu = await this.detectGPUCapability();
    
    // TensorFlow capability
    this.capabilities.tensorFlowCapable = await this.checkTensorFlowCapability();
    
    // LLM capability
    this.capabilities.llmCapable = await this.checkLLMCapability();

    console.log('📊 Device capabilities detected:', this.capabilities);
    this.emit('capabilitiesDetected', this.capabilities);
  }

  private async detectCPUCapability(): Promise<number> {
    try {
      // Simple CPU benchmark
      const start = performance.now();
      let result = 0;
      for (let i = 0; i < 1000000; i++) {
        result += Math.sqrt(i);
      }
      const time = performance.now() - start;
      
      // Map execution time to capability score (0-100)
      if (time < 100) return 90; // Very fast
      if (time < 200) return 75; // Fast
      if (time < 500) return 50; // Medium
      if (time < 1000) return 25; // Slow
      return 10; // Very slow
    } catch (error) {
      console.warn('CPU detection failed:', error);
      return 30; // Conservative estimate
    }
  }

  private async detectMemoryCapability(): Promise<number> {
    try {
      if (typeof performance !== 'undefined' && performance.memory) {
        const memoryInfo = performance.memory;
        const totalMemory = memoryInfo.jsHeapSizeLimit / (1024 * 1024); // MB
        
        // Map memory to capability score
        if (totalMemory >= 4096) return 100; // 4GB+
        if (totalMemory >= 2048) return 80;  // 2GB+
        if (totalMemory >= 1024) return 60;  // 1GB+
        if (totalMemory >= 512) return 40;   // 512MB+
        return 20; // Less than 512MB
      }
      
      // Fallback: estimate based on device type
      const userAgent = navigator.userAgent;
      if (userAgent.includes('Mobile')) {
        return 30; // Mobile device
      } else {
        return 70; // Desktop
      }
    } catch (error) {
      console.warn('Memory detection failed:', error);
      return 50; // Conservative estimate
    }
  }

  private async detectStorageCapability(): Promise<number> {
    try {
      if ('storage' in navigator && 'estimate' in navigator.storage) {
        const estimate = await navigator.storage.estimate();
        const availableStorage = (estimate.quota || 0) / (1024 * 1024); // MB
        
        // Map storage to capability score
        if (availableStorage >= 32768) return 100; // 32GB+
        if (availableStorage >= 16384) return 80;  // 16GB+
        if (availableStorage >= 8192) return 60;   // 8GB+
        if (availableStorage >= 4096) return 40;   // 4GB+
        return 20; // Less than 4GB
      }
      
      return 60; // Default estimate
    } catch (error) {
      console.warn('Storage detection failed:', error);
      return 40; // Conservative estimate
    }
  }

  private async detectBatteryLevel(): Promise<number> {
    try {
      if ('getBattery' in navigator) {
        const battery = await (navigator as any).getBattery();
        return Math.round(battery.level * 100);
      }
      
      return 80; // Default assumption
    } catch (error) {
      console.warn('Battery detection failed:', error);
      return 75; // Conservative estimate
    }
  }

  private async detectNetworkCapability(): Promise<number> {
    try {
      if ('connection' in navigator) {
        const connection = (navigator as any).connection;
        
        if (connection.effectiveType) {
          switch (connection.effectiveType) {
            case '4g': return 90;
            case '3g': return 70;
            case '2g': return 40;
            case 'slow-2g': return 20;
            default: return 50;
          }
        }
        
        if (connection.downlink) {
          return Math.min(100, connection.downlink * 10); // Mbps to score
        }
      }
      
      // Simple network speed test
      const start = performance.now();
      const response = await fetch('https://httpbin.org/json', { 
        method: 'GET',
        cache: 'no-cache'
      });
      await response.text();
      const time = performance.now() - start;
      
      if (time < 500) return 80; // Fast
      if (time < 1500) return 60; // Medium
      if (time < 3000) return 40; // Slow
      return 20; // Very slow
    } catch (error) {
      console.warn('Network detection failed:', error);
      return 50; // Conservative estimate
    }
  }

  private async detectGPUCapability(): Promise<boolean> {
    try {
      // Check for WebGL support
      const canvas = document.createElement('canvas');
      const gl = canvas.getContext('webgl') || canvas.getContext('experimental-webgl');
      
      if (!gl) return false;
      
      // Check for WebGL2 support
      const gl2 = canvas.getContext('webgl2');
      if (gl2) return true;
      
      // Check for basic GPU capabilities
      const debugInfo = gl.getExtension('WEBGL_debug_renderer_info');
      if (debugInfo) {
        const renderer = gl.getParameter(debugInfo.UNMASKED_RENDERER_WEBGL);
        // Check if it's a software renderer
        return !renderer.toLowerCase().includes('software');
      }
      
      return true; // Assume hardware acceleration if WebGL is available
    } catch (error) {
      console.warn('GPU detection failed:', error);
      return false;
    }
  }

  private async checkTensorFlowCapability(): Promise<boolean> {
    try {
      // Check if we can load TensorFlow.js
      const hasWebGL = this.capabilities.gpu;
      const hasEnoughMemory = this.capabilities.memory >= 512;
      const hasEnoughCPU = this.capabilities.cpu >= 20;
      
      return hasWebGL && hasEnoughMemory && hasEnoughCPU;
    } catch (error) {
      console.warn('TensorFlow capability check failed:', error);
      return false;
    }
  }

  private async checkLLMCapability(): Promise<boolean> {
    try {
      // LLMs typically need more resources
      const hasEnoughMemory = this.capabilities.memory >= 2048; // 2GB minimum
      const hasEnoughStorage = this.capabilities.storage >= 3000; // 3GB minimum
      const hasEnoughCPU = this.capabilities.cpu >= 50;
      const hasGoodNetwork = this.capabilities.network >= 40;
      
      return hasEnoughMemory && hasEnoughStorage && hasEnoughCPU && hasGoodNetwork;
    } catch (error) {
      console.warn('LLM capability check failed:', error);
      return false;
    }
  }

  private async determineIntelligenceLevel(): Promise<void> {
    const { cpu, memory, storage, battery, gpu, llmCapable, tensorFlowCapable } = this.capabilities;
    
    // Determine intelligence level based on capabilities
    if (llmCapable && tensorFlowCapable && gpu && memory >= 4096 && cpu >= 70) {
      this.currentLevel = this.getHybridLevel();
    } else if (tensorFlowCapable && gpu && memory >= 2048 && cpu >= 50) {
      this.currentLevel = this.getAdvancedLevel();
    } else if (tensorFlowCapable && memory >= 1024 && cpu >= 30) {
      this.currentLevel = this.getEnhancedLevel();
    } else {
      this.currentLevel = this.getBasicLevel();
    }
    
    console.log(`🧠 Intelligence level determined: ${this.currentLevel.level}`);
    this.emit('levelDetermined', this.currentLevel);
  }

  private getEnhancedLevel(): IntelligenceLevel {
    return {
      level: 'enhanced',
      features: [
        'resource_monitoring',
        'basic_optimization',
        'task_allocation',
        'network_optimization',
        'swarm_behavior'
      ],
      models: [
        'resource_predictor',
        'task_allocator',
        'network_optimizer',
        'swarm_behavior'
      ],
      performance: {
        inferenceTime: 100,
        memoryUsage: 300,
        accuracy: 0.85
      }
    };
  }

  private getAdvancedLevel(): IntelligenceLevel {
    return {
      level: 'advanced',
      features: [
        'resource_monitoring',
        'basic_optimization',
        'task_allocation',
        'network_optimization',
        'swarm_behavior',
        'anomaly_detection',
        'federated_learning',
        'particle_swarm_optimization'
      ],
      models: [
        'resource_predictor',
        'task_allocator',
        'network_optimizer',
        'swarm_behavior',
        'anomaly_detector'
      ],
      performance: {
        inferenceTime: 150,
        memoryUsage: 600,
        accuracy: 0.92
      }
    };
  }

  private getHybridLevel(): IntelligenceLevel {
    return {
      level: 'hybrid',
      features: [
        'resource_monitoring',
        'basic_optimization',
        'task_allocation',
        'network_optimization',
        'swarm_behavior',
        'anomaly_detection',
        'federated_learning',
        'particle_swarm_optimization',
        'llm_reasoning',
        'natural_language_interface',
        'complex_planning'
      ],
      models: [
        'resource_predictor',
        'task_allocator',
        'network_optimizer',
        'swarm_behavior',
        'anomaly_detector',
        'llm_interface'
      ],
      performance: {
        inferenceTime: 200,
        memoryUsage: 1200,
        accuracy: 0.95
      }
    };
  }

  // Public API methods
  getCapabilities(): DeviceCapabilities {
    return { ...this.capabilities };
  }

  getCurrentLevel(): IntelligenceLevel {
    return { ...this.currentLevel };
  }

  async updateCapabilities(): Promise<void> {
    console.log('🔄 Updating device capabilities...');
    await this.detectCapabilities();
    await this.determineIntelligenceLevel();
    this.emit('capabilitiesUpdated', this.capabilities);
  }

  canRunModel(modelName: string): boolean {
    return this.currentLevel.models.includes(modelName);
  }

  canRunFeature(featureName: string): boolean {
    return this.currentLevel.features.includes(featureName);
  }

  getRecommendedConfig(): any {
    const config: any = {
      intelligenceLevel: this.currentLevel.level,
      models: {},
      features: this.currentLevel.features,
      performance: this.currentLevel.performance
    };

    // Model-specific configurations
    if (this.canRunModel('resource_predictor')) {
      config.models.resource_predictor = {
        enabled: true,
        updateInterval: 30000, // 30 seconds
        historySize: 100
      };
    }

    if (this.canRunModel('task_allocator')) {
      config.models.task_allocator = {
        enabled: true,
        optimizationLevel: this.currentLevel.level === 'hybrid' ? 'advanced' : 'basic',
        federatedLearning: this.canRunFeature('federated_learning')
      };
    }

    if (this.canRunModel('anomaly_detector')) {
      config.models.anomaly_detector = {
        enabled: true,
        sensitivity: this.currentLevel.level === 'hybrid' ? 'high' : 'medium',
        alertThreshold: 0.7
      };
    }

    if (this.canRunFeature('llm_reasoning')) {
      config.llm = {
        enabled: true,
        endpoint: 'auto-detect',
        fallbackToTensorFlow: true,
        cacheSize: 50
      };
    }

    return config;
  }

  // Performance monitoring
  async benchmarkPerformance(): Promise<{
    cpu: { score: number; time: number };
    memory: { available: number; used: number };
    gpu: { available: boolean; score: number };
    overall: { level: string; score: number };
  }> {
    const cpuScore = await this.detectCPUCapability();
    const cpuTime = performance.now();
    
    // CPU benchmark
    let result = 0;
    for (let i = 0; i < 500000; i++) {
      result += Math.sqrt(i);
    }
    const cpuBenchmarkTime = performance.now() - cpuTime;

    // Memory benchmark
    let memoryUsed = 0;
    if (typeof performance !== 'undefined' && performance.memory) {
      memoryUsed = performance.memory.usedJSHeapSize / (1024 * 1024); // MB
    }

    // GPU benchmark
    const gpuScore = this.capabilities.gpu ? await this.benchmarkGPU() : 0;

    // Overall score
    const overallScore = (cpuScore + (this.capabilities.memory / 40) + gpuScore) / 3;

    return {
      cpu: { score: cpuScore, time: cpuBenchmarkTime },
      memory: { available: this.capabilities.memory, used: memoryUsed },
      gpu: { available: this.capabilities.gpu, score: gpuScore },
      overall: { 
        level: this.currentLevel.level, 
        score: Math.round(overallScore) 
      }
    };
  }

  private async benchmarkGPU(): Promise<number> {
    try {
      const canvas = document.createElement('canvas');
      const gl = canvas.getContext('webgl');
      
      if (!gl) return 0;

      // Simple GPU benchmark
      const start = performance.now();
      
      // Create and render many triangles
      for (let i = 0; i < 1000; i++) {
        gl.clear(gl.COLOR_BUFFER_BIT);
      }
      
      const time = performance.now() - start;
      
      // Map time to score (lower time = higher score)
      if (time < 10) return 100;
      if (time < 50) return 80;
      if (time < 100) return 60;
      if (time < 200) return 40;
      return 20;
    } catch (error) {
      console.warn('GPU benchmark failed:', error);
      return 0;
    }
  }

  // Health monitoring
  async getHealthStatus(): Promise<{
    overall: 'healthy' | 'warning' | 'critical';
    battery: number;
    memory: number;
    cpu: number;
    network: number;
    recommendations: string[];
  }> {
    const { battery, memory, cpu, network } = this.capabilities;
    
    let overall: 'healthy' | 'warning' | 'critical' = 'healthy';
    const recommendations: string[] = [];

    // Battery health
    if (battery < 20) {
      overall = 'critical';
      recommendations.push('Critical battery level - charge immediately');
    } else if (battery < 50) {
      overall = 'warning';
      recommendations.push('Low battery - consider charging soon');
    }

    // Memory health
    if (memory < 512) {
      overall = overall === 'critical' ? 'critical' : 'warning';
      recommendations.push('Low memory - close unnecessary applications');
    }

    // CPU health
    if (cpu < 30) {
      overall = overall === 'critical' ? 'critical' : 'warning';
      recommendations.push('High CPU usage - reduce computational load');
    }

    // Network health
    if (network < 30) {
      overall = overall === 'critical' ? 'critical' : 'warning';
      recommendations.push('Poor network connection - check connectivity');
    }

    return {
      overall,
      battery,
      memory,
      cpu,
      network,
      recommendations
    };
  }

  dispose(): void {
    this.removeAllListeners();
    this.isInitialized = false;
    console.log('🧹 Device Intelligence Manager disposed');
  }
}