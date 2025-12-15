// @domain DIGITAL - Digital systems, software, compilers, algorithms
import { CanvasMQTTBroker, DEFAULT_MQTT_CONFIG } from './mqtt-broker.js';
import { CanvasP2PSynchronizer } from './canvas-sync.js';
import { CanvasMQTTProtocol } from './mqtt-protocol.js';

export interface MQTTNetworkConfig {
  broker: string;
  port: number;
  username?: string;
  password?: string;
  repositories: string[];
  enableDiscovery: boolean;
  syncInterval: number; // in seconds
}

export interface NetworkStats {
  connectedPeers: number;
  activeCanvases: number;
  messagesPerSecond: number;
  totalMessages: number;
  uptime: number;
}

export class P2PNetworkManager {
  private broker: CanvasMQTTBroker;
  private synchronizers: Map<string, CanvasP2PSynchronizer> = new Map();
  private protocols: Map<string, CanvasMQTTProtocol> = new Map();
  private config: MQTTNetworkConfig;
  private stats: NetworkStats;
  private startTime: number;
  private messageCount: number = 0;
  private lastStatsUpdate: number = 0;

  constructor(config: MQTTNetworkConfig) {
    this.config = config;
    this.broker = new CanvasMQTTBroker({
      broker: config.broker,
      port: config.port,
      username: config.username,
      password: config.password,
      clientId: `network-manager-${Math.random().toString(36).substr(2, 9)}`,
      topics: {
        canvas: 'mind-git/canvas',
        sync: 'mind-git/sync',
        discovery: 'mind-git/discovery'
      }
    });

    this.stats = {
      connectedPeers: 0,
      activeCanvases: 0,
      messagesPerSecond: 0,
      totalMessages: 0,
      uptime: 0
    };
    this.startTime = Date.now();
  }

  async initialize(): Promise<void> {
    console.log('Initializing P2P Network Manager...');
    
    // Connect to MQTT broker
    await this.broker.connect();
    
    // Initialize synchronizers for each repository
    for (const repository of this.config.repositories) {
      const synchronizer = new CanvasP2PSynchronizer(repository, {
        broker: this.config.broker,
        port: this.config.port,
        username: this.config.username,
        password: this.config.password,
        clientId: `sync-${repository}-${Math.random().toString(36).substr(2, 6)}`,
        topics: {
          canvas: 'mind-git/canvas',
          sync: 'mind-git/sync',
          discovery: 'mind-git/discovery'
        }
      });

      const protocol = new CanvasMQTTProtocol(repository);
      
      this.synchronizers.set(repository, synchronizer);
      this.protocols.set(repository, protocol);
      
      await synchronizer.connect();
    }

    // Setup network monitoring
    this.setupNetworkMonitoring();
    
    console.log(`P2P Network initialized with ${this.config.repositories.length} repositories`);
  }

  private setupNetworkMonitoring(): void {
    // Update stats every 10 seconds
    setInterval(() => {
      this.updateStats();
    }, 10000);

    // Monitor broker events
    this.broker.on('client-discovered', (client) => {
      console.log(`New client discovered: ${client.peerId}`);
      this.stats.connectedPeers++;
    });

    this.broker.on('canvas-created', (message) => {
      this.stats.activeCanvases++;
      this.messageCount++;
    });

    this.broker.on('canvas-updated', (message) => {
      this.messageCount++;
    });

    this.broker.on('canvas-deleted', (message) => {
      this.stats.activeCanvases--;
      this.messageCount++;
    });
  }

  private updateStats(): void {
    const now = Date.now();
    const uptime = now - this.startTime;
    const timeDiff = (now - this.lastStatsUpdate) / 1000; // seconds
    
    this.stats.messagesPerSecond = timeDiff > 0 ? this.messageCount / timeDiff : 0;
    this.stats.uptime = uptime;
    this.lastStatsUpdate = now;
    this.messageCount = 0; // Reset counter for next interval
  }

  async createCanvas(repository: string, canvasId: string, canvasData: any, author: string): Promise<void> {
    const protocol = this.protocols.get(repository);
    if (!protocol) {
      throw new Error(`No protocol found for repository: ${repository}`);
    }

    await protocol.createCanvas(canvasId, canvasData, author);
  }

  async updateCanvas(repository: string, canvasId: string, updates: any, author: string): Promise<void> {
    const protocol = this.protocols.get(repository);
    if (!protocol) {
      throw new Error(`No protocol found for repository: ${repository}`);
    }

    await protocol.updateCanvas(canvasId, updates, author);
  }

  async deleteCanvas(repository: string, canvasId: string, author: string): Promise<void> {
    const protocol = this.protocols.get(repository);
    if (!protocol) {
      throw new Error(`No protocol found for repository: ${repository}`);
    }

    await protocol.deleteCanvas(canvasId, author);
  }

  async shareCanvas(repository: string, canvasId: string, targetRepository?: string): Promise<void> {
    const protocol = this.protocols.get(repository);
    if (!protocol) {
      throw new Error(`No protocol found for repository: ${repository}`);
    }

    await protocol.shareCanvas(canvasId, targetRepository);
  }

  async syncCanvas(repository: string, canvasId: string): Promise<void> {
    const protocol = this.protocols.get(repository);
    if (!protocol) {
      throw new Error(`No protocol found for repository: ${repository}`);
    }

    await protocol.syncCanvas(canvasId);
  }

  async syncRepository(repository: string): Promise<void> {
    const synchronizer = this.synchronizers.get(repository);
    if (!synchronizer) {
      throw new Error(`No synchronizer found for repository: ${repository}`);
    }

    // Request full repository sync
    await synchronizer.requestInitialSync();
  }

  async discoverPeers(): Promise<any[]> {
    return new Promise((resolve) => {
      const peers: any[] = [];
      
      // Listen for peer announcements for 5 seconds
      const timeout = setTimeout(() => {
        resolve(peers);
      }, 5000);

      this.broker.on('client-discovered', (client) => {
        if (this.config.repositories.includes(client.repository)) {
          peers.push(client);
        }
      });
    });
  }

  getNetworkStats(): NetworkStats {
    this.updateStats();
    return { ...this.stats };
  }

  getRepositoryStatus(repository: string): any {
    const synchronizer = this.synchronizers.get(repository);
    const protocol = this.protocols.get(repository);
    
    if (!synchronizer || !protocol) {
      return { error: `Repository ${repository} not found` };
    }

    return {
      synchronizer: synchronizer.getSyncStatus(),
      protocol: protocol.getProtocolStatus(),
      connected: synchronizer.getSyncStatus().connectedPeers > 0
    };
  }

  getAllRepositoryStatuses(): Record<string, any> {
    const statuses: Record<string, any> = {};
    
    for (const repository of this.config.repositories) {
      statuses[repository] = this.getRepositoryStatus(repository);
    }
    
    return statuses;
  }

  async broadcastMessage(message: any, topic?: string): Promise<void> {
    const broadcastTopic = topic || 'mind-git/broadcast';
    await this.broker.publish(broadcastTopic, message);
  }

  async enableRealTimeCollaboration(repository: string, canvasId: string): Promise<void> {
    const protocol = this.protocols.get(repository);
    if (!protocol) {
      throw new Error(`No protocol found for repository: ${repository}`);
    }

    // Enable real-time mode for specific canvas
    console.log(`Enabling real-time collaboration for canvas ${canvasId} in repository ${repository}`);
    
    // This would enable WebSocket-like real-time updates over MQTT
    const realTimeMessage = {
      type: 'enable-real-time',
      canvasId,
      repository,
      timestamp: Date.now()
    };

    await this.broker.publish(this.broker.config.topics.sync, realTimeMessage);
  }

  async disableRealTimeCollaboration(repository: string, canvasId: string): Promise<void> {
    const protocol = this.protocols.get(repository);
    if (!protocol) {
      throw new Error(`No protocol found for repository: ${repository}`);
    }

    const realTimeMessage = {
      type: 'disable-real-time',
      canvasId,
      repository,
      timestamp: Date.now()
    };

    await this.broker.publish(this.broker.config.topics.sync, realTimeMessage);
  }

  async disconnect(): Promise<void> {
    console.log('Disconnecting P2P Network Manager...');
    
    // Disconnect all synchronizers
    for (const [repository, synchronizer] of this.synchronizers) {
      await synchronizer.disconnect();
    }
    
    // Disconnect broker
    await this.broker.disconnect();
    
    console.log('P2P Network Manager disconnected');
  }
}

// Factory function for easy setup
export function createP2PNetwork(config: Partial<MQTTNetworkConfig> = {}): P2PNetworkManager {
  const defaultConfig: MQTTNetworkConfig = {
    broker: 'localhost',
    port: 1883,
    repositories: ['default'],
    enableDiscovery: true,
    syncInterval: 30,
    ...config
  };

  return new P2PNetworkManager(defaultConfig);
}