// @domain DIGITAL - Digital systems, software, compilers, algorithms
import * as mqtt from 'mqtt';
import { EventEmitter } from 'events';

export interface CanvasMessage {
  type: 'canvas-update' | 'canvas-create' | 'canvas-delete' | 'canvas-sync';
  canvasId: string;
  repository: string;
  data: any;
  timestamp: number;
  author: string;
}

export interface MQTTConfig {
  broker: string;
  port: number;
  username?: string;
  password?: string;
  clientId: string;
  topics: {
    canvas: string;
    sync: string;
    discovery: string;
  };
}

export class CanvasMQTTBroker extends EventEmitter {
  private client: mqtt.MqttClient | null = null;
  public config: MQTTConfig;
  private connectedClients: Map<string, any> = new Map();
  private canvasSubscriptions: Map<string, Set<string>> = new Map();

  constructor(config: MQTTConfig) {
    super();
    this.config = config;
  }

  async connect(): Promise<void> {
    return new Promise((resolve, reject) => {
      this.client = mqtt.connect({
        host: this.config.broker,
        port: this.config.port,
        username: this.config.username,
        password: this.config.password,
        clientId: this.config.clientId,
        clean: true,
        keepalive: 60,
        reconnectPeriod: 1000,
        connectTimeout: 30 * 1000,
      });

      this.client.on('connect', () => {
        console.log(`MQTT Broker connected to ${this.config.broker}:${this.config.port}`);
        this.setupSubscriptions();
        this.emit('connected');
        resolve();
      });

      this.client.on('error', (error) => {
        console.error('MQTT connection error:', error);
        this.emit('error', error);
        reject(error);
      });

      this.client.on('message', (topic, message) => {
        this.handleMessage(topic, message);
      });

      this.client.on('close', () => {
        console.log('MQTT connection closed');
        this.emit('disconnected');
      });
    });
  }

  private setupSubscriptions(): void {
    if (!this.client) return;

    // Subscribe to canvas topics
    this.client.subscribe(this.config.topics.canvas, { qos: 1 });
    this.client.subscribe(this.config.topics.sync, { qos: 1 });
    this.client.subscribe(this.config.topics.discovery, { qos: 1 });

    console.log(`Subscribed to topics: ${Object.values(this.config.topics).join(', ')}`);
  }

  private async handleMessage(topic: string, message: Buffer): Promise<void> {
    try {
      const data = JSON.parse(message.toString());
      
      switch (topic) {
        case this.config.topics.canvas:
          await this.handleCanvasMessage(data);
          break;
        case this.config.topics.sync:
          await this.handleSyncMessage(data);
          break;
        case this.config.topics.discovery:
          await this.handleDiscoveryMessage(data);
          break;
      }
    } catch (error) {
      console.error('Error handling MQTT message:', error);
    }
  }

  private async handleCanvasMessage(message: CanvasMessage): Promise<void> {
    console.log(`Canvas operation: ${message.type} for ${message.canvasId}`);
    
    switch (message.type) {
      case 'canvas-create':
        this.emit('canvas-created', message);
        break;
      case 'canvas-update':
        this.emit('canvas-updated', message);
        break;
      case 'canvas-delete':
        this.emit('canvas-deleted', message);
        break;
    }
  }

  private async handleSyncMessage(message: any): Promise<void> {
    console.log('Sync request received:', message);
    this.emit('sync-request', message);
  }

  private async handleDiscoveryMessage(message: any): Promise<void> {
    console.log('Discovery message:', message);
    this.emit('client-discovered', message);
  }

  async publishCanvasUpdate(canvasId: string, repository: string, data: any, author: string): Promise<void> {
    const message: CanvasMessage = {
      type: 'canvas-update',
      canvasId,
      repository,
      data,
      timestamp: Date.now(),
      author
    };

    await this.publish(this.config.topics.canvas, message);
  }

  async publishCanvasCreate(canvasId: string, repository: string, data: any, author: string): Promise<void> {
    const message: CanvasMessage = {
      type: 'canvas-create',
      canvasId,
      repository,
      data,
      timestamp: Date.now(),
      author
    };

    await this.publish(this.config.topics.canvas, message);
  }

  async publishSyncRequest(repository: string, canvasIds: string[]): Promise<void> {
    const message = {
      type: 'sync-request',
      repository,
      canvasIds,
      timestamp: Date.now()
    };

    await this.publish(this.config.topics.sync, message);
  }

  public async publish(topic: string, message: any): Promise<void> {
    if (!this.client) {
      throw new Error('MQTT client not connected');
    }

    return new Promise((resolve, reject) => {
      this.client!.publish(topic, JSON.stringify(message), { qos: 1 }, (error) => {
        if (error) {
          reject(error);
        } else {
          resolve();
        }
      });
    });
  }

  async disconnect(): Promise<void> {
    if (this.client) {
      this.client.end();
      this.client = null;
    }
  }

  isConnected(): boolean {
    return this.client !== null && this.client.connected;
  }

  getConnectedClients(): string[] {
    return Array.from(this.connectedClients.keys());
  }

  getCanvasSubscriptions(canvasId: string): string[] {
    return Array.from(this.canvasSubscriptions.get(canvasId) || []);
  }
}

// Default configuration for development
export const DEFAULT_MQTT_CONFIG: MQTTConfig = {
  broker: 'localhost',
  port: 1883,
  clientId: `mind-git-${Math.random().toString(36).substr(2, 9)}`,
  topics: {
    canvas: 'mind-git/canvas',
    sync: 'mind-git/sync',
    discovery: 'mind-git/discovery'
  }
};