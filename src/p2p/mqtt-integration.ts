// @domain DIGITAL - Digital systems, software, compilers, algorithms
import { P2PNetworkManager } from './network-manager.js';

export interface MQTTIntegrationConfig {
  broker: {
    host: string;
    port: number;
    username?: string;
    password?: string;
  };
  repositories: string[];
  features: {
    realTimeCollaboration: boolean;
    autoSync: boolean;
    discovery: boolean;
    encryption: boolean;
  };
  performance: {
    maxMessageSize: number; // bytes
    maxConnections: number;
    heartbeatInterval: number; // seconds
  };
}

export class MQTTIntegrationService {
  private networkManager: P2PNetworkManager;
  private config: MQTTIntegrationConfig;
  private isInitialized: boolean = false;

  constructor(config: MQTTIntegrationConfig) {
    this.config = config;
    this.networkManager = new P2PNetworkManager({
      broker: config.broker.host,
      port: config.broker.port,
      username: config.broker.username,
      password: config.broker.password,
      repositories: config.repositories,
      enableDiscovery: config.features.discovery,
      syncInterval: 30 // Default 30 seconds
    });
  }

  async initialize(): Promise<void> {
    console.log('Initializing MQTT Integration Service...');
    
    try {
      await this.networkManager.initialize();
      this.isInitialized = true;
      
      console.log('MQTT Integration Service initialized successfully');
      console.log(`Connected to broker: ${this.config.broker.host}:${this.config.broker.port}`);
      console.log(`Managing repositories: ${this.config.repositories.join(', ')}`);
      
      // Log feature status
      this.logFeatureStatus();
      
    } catch (error) {
      console.error('Failed to initialize MQTT Integration Service:', error);
      throw error;
    }
  }

  private logFeatureStatus(): void {
    console.log('=== MQTT Integration Features ===');
    console.log(`Real-time collaboration: ${this.config.features.realTimeCollaboration ? 'ENABLED' : 'DISABLED'}`);
    console.log(`Auto-sync: ${this.config.features.autoSync ? 'ENABLED' : 'DISABLED'}`);
    console.log(`Peer discovery: ${this.config.features.discovery ? 'ENABLED' : 'DISABLED'}`);
    console.log(`Encryption: ${this.config.features.encryption ? 'ENABLED' : 'DISABLED'}`);
    console.log('================================');
  }

  async createCanvas(repository: string, canvasId: string, canvasData: any, author: string): Promise<void> {
    this.ensureInitialized();
    await this.networkManager.createCanvas(repository, canvasId, canvasData, author);
    console.log(`Canvas created: ${canvasId} in repository ${repository}`);
  }

  async updateCanvas(repository: string, canvasId: string, updates: any, author: string): Promise<void> {
    this.ensureInitialized();
    await this.networkManager.updateCanvas(repository, canvasId, updates, author);
    console.log(`Canvas updated: ${canvasId} in repository ${repository}`);
  }

  async deleteCanvas(repository: string, canvasId: string, author: string): Promise<void> {
    this.ensureInitialized();
    await this.networkManager.deleteCanvas(repository, canvasId, author);
    console.log(`Canvas deleted: ${canvasId} in repository ${repository}`);
  }

  async shareCanvas(repository: string, canvasId: string, targetRepository?: string): Promise<void> {
    this.ensureInitialized();
    await this.networkManager.shareCanvas(repository, canvasId, targetRepository);
    console.log(`Canvas shared: ${canvasId} from ${repository}${targetRepository ? ` to ${targetRepository}` : ' (broadcast)'}`);
  }

  async syncCanvas(repository: string, canvasId: string): Promise<void> {
    this.ensureInitialized();
    await this.networkManager.syncCanvas(repository, canvasId);
    console.log(`Canvas sync initiated: ${canvasId} in repository ${repository}`);
  }

  async syncRepository(repository: string): Promise<void> {
    this.ensureInitialized();
    await this.networkManager.syncRepository(repository);
    console.log(`Repository sync initiated: ${repository}`);
  }

  async enableRealTimeCollaboration(repository: string, canvasId: string): Promise<void> {
    if (!this.config.features.realTimeCollaboration) {
      throw new Error('Real-time collaboration is disabled in configuration');
    }

    await this.networkManager.enableRealTimeCollaboration(repository, canvasId);
    console.log(`Real-time collaboration enabled for canvas ${canvasId} in repository ${repository}`);
  }

  async disableRealTimeCollaboration(repository: string, canvasId: string): Promise<void> {
    await this.networkManager.disableRealTimeCollaboration(repository, canvasId);
    console.log(`Real-time collaboration disabled for canvas ${canvasId} in repository ${repository}`);
  }

  async discoverPeers(): Promise<any[]> {
    this.ensureInitialized();
    const peers = await this.networkManager.discoverPeers();
    console.log(`Discovered ${peers.length} peers`);
    return peers;
  }

  getNetworkStatus(): any {
    this.ensureInitialized();
    return this.networkManager.getNetworkStats();
  }

  getRepositoryStatus(repository: string): any {
    this.ensureInitialized();
    return this.networkManager.getRepositoryStatus(repository);
  }

  getAllRepositoryStatuses(): Record<string, any> {
    this.ensureInitialized();
    return this.networkManager.getAllRepositoryStatuses();
  }

  async broadcastMessage(message: any): Promise<void> {
    this.ensureInitialized();
    await this.networkManager.broadcastMessage(message);
    console.log('Broadcast message sent:', message.type || 'unknown');
  }

  async testConnection(): Promise<boolean> {
    try {
      const status = this.getNetworkStatus();
      return status.connectedPeers > 0;
    } catch (error) {
      console.error('Connection test failed:', error);
      return false;
    }
  }

  async performanceTest(): Promise<any> {
    const startTime = Date.now();
    const testMessage = {
      type: 'performance-test',
      timestamp: startTime,
      payload: new Array(1024).fill(0).map(() => Math.random()) // 1KB test data
    };

    await this.broadcastMessage(testMessage);
    
    const endTime = Date.now();
    const latency = endTime - startTime;
    
    return {
      latency,
      messageSize: testMessage.payload.length,
      timestamp: endTime,
      success: true
    };
  }

  private ensureInitialized(): void {
    if (!this.isInitialized) {
      throw new Error('MQTT Integration Service not initialized. Call initialize() first.');
    }
  }

  async disconnect(): Promise<void> {
    console.log('Disconnecting MQTT Integration Service...');
    
    if (this.isInitialized) {
      await this.networkManager.disconnect();
      this.isInitialized = false;
      console.log('MQTT Integration Service disconnected');
    }
  }

  // Configuration validation
  validateConfig(config: MQTTIntegrationConfig): { valid: boolean; errors: string[] } {
    const errors: string[] = [];

    if (!config.broker?.host || !config.broker?.port) {
      errors.push('Broker configuration is required (host and port)');
    }

    if (!config.repositories || config.repositories.length === 0) {
      errors.push('At least one repository must be specified');
    }

    if (config.performance?.maxMessageSize && config.performance.maxMessageSize > 1024 * 1024) {
      errors.push('Maximum message size should not exceed 1MB');
    }

    if (config.performance?.maxConnections && config.performance.maxConnections > 1000) {
      errors.push('Maximum connections should not exceed 1000');
    }

    return {
      valid: errors.length === 0,
      errors
    };
  }

  // Health check
  async healthCheck(): Promise<{ healthy: boolean; issues: string[]; connectedPeers?: number; activeCanvases?: number }> {
    const issues: string[] = [];
    let totalPeers = 0;
    let totalCanvases = 0;

    try {
      // Check network connection
      const isConnected = await this.testConnection();
      if (!isConnected) {
        issues.push('Not connected to MQTT broker');
      }

      // Check repository sync status
      const statuses = this.getAllRepositoryStatuses();
      for (const [repo, status] of Object.entries(statuses)) {
        if (status.error) {
          issues.push(`Repository ${repo}: ${status.error}`);
        }
      }

      // Calculate totals
      totalPeers = Object.values(statuses).reduce((sum: number, status: any) => sum + (status.synchronizer?.connectedPeers || 0), 0);
      totalCanvases = Object.values(statuses).reduce((sum: number, status: any) => sum + (status.synchronizer?.localCanvases || 0), 0);

      // Check message queue
      const networkStats = this.getNetworkStatus();
      if (networkStats.messagesPerSecond > 100) {
        issues.push('High message rate detected');
      }

    } catch (error) {
      issues.push(`Health check error: ${error}`);
    }

    return {
      healthy: issues.length === 0,
      issues,
      connectedPeers: totalPeers,
      activeCanvases: totalCanvases
    };
  }
}

// Default configuration for development
export const DEFAULT_MQTT_INTEGRATION_CONFIG: MQTTIntegrationConfig = {
  broker: {
    host: 'localhost',
    port: 1883
  },
  repositories: ['default'],
  features: {
    realTimeCollaboration: true,
    autoSync: true,
    discovery: true,
    encryption: false
  },
  performance: {
    maxMessageSize: 64 * 1024, // 64KB
    maxConnections: 100,
    heartbeatInterval: 60
  }
};