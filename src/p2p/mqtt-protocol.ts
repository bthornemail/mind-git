// @domain DIGITAL - Digital systems, software, compilers, algorithms
import { CanvasP2PSynchronizer } from './canvas-sync.js';
import { readFileSync, writeFileSync } from 'fs';
import { join } from 'path';

export interface CanvasOperation {
  type: 'create' | 'update' | 'delete' | 'share' | 'sync';
  canvasId: string;
  data?: any;
  timestamp: number;
  author: string;
}

export interface MQTTMessageProtocol {
  version: string;
  messageType: string;
  payload: any;
  metadata: {
    source: string;
    target?: string;
    priority: 'low' | 'medium' | 'high' | 'critical';
    requiresAck: boolean;
  };
}

export class CanvasMQTTProtocol {
  private synchronizer: CanvasP2PSynchronizer;
  private messageQueue: CanvasOperation[] = [];
  private processingQueue: boolean = false;

  constructor(repository: string, brokerConfig?: any) {
    this.synchronizer = new CanvasP2PSynchronizer(repository, brokerConfig);
  }

  async initialize(): Promise<void> {
    await this.synchronizer.connect();
    this.setupMessageProcessing();
  }

  private setupMessageProcessing(): void {
    // Process message queue every 5 seconds
    setInterval(() => {
      this.processMessageQueue();
    }, 5000);
  }

  async createCanvas(canvasId: string, canvasData: any, author: string): Promise<void> {
    const operation: CanvasOperation = {
      type: 'create',
      canvasId,
      data: canvasData,
      timestamp: Date.now(),
      author
    };

    await this.queueOperation(operation);
    await this.synchronizer.registerLocalCanvas(canvasId);
  }

  async updateCanvas(canvasId: string, updates: any, author: string): Promise<void> {
    const operation: CanvasOperation = {
      type: 'update',
      canvasId,
      data: updates,
      timestamp: Date.now(),
      author
    };

    await this.queueOperation(operation);
    await this.synchronizer.updateLocalCanvas(canvasId);
  }

  async deleteCanvas(canvasId: string, author: string): Promise<void> {
    const operation: CanvasOperation = {
      type: 'delete',
      canvasId,
      timestamp: Date.now(),
      author
    };

    await this.queueOperation(operation);
  }

  async shareCanvas(canvasId: string, targetRepository?: string): Promise<void> {
    const operation: CanvasOperation = {
      type: 'share',
      canvasId,
      timestamp: Date.now(),
      author: 'system'
    };

    await this.queueOperation(operation);
    
    // Publish share request to specific target or broadcast
    if (targetRepository) {
      await this.publishToRepository(targetRepository, operation);
    } else {
      await this.broadcastOperation(operation);
    }
  }

  async syncCanvas(canvasId: string): Promise<void> {
    const operation: CanvasOperation = {
      type: 'sync',
      canvasId,
      timestamp: Date.now(),
      author: 'system'
    };

    await this.queueOperation(operation);
    await this.synchronizer.requestCanvasSync(canvasId, 'unknown');
  }

  private async queueOperation(operation: CanvasOperation): Promise<void> {
    this.messageQueue.push(operation);
    
    // Process immediately for critical operations
    if (this.isCriticalOperation(operation)) {
      await this.processMessageQueue();
    }
  }

  private isCriticalOperation(operation: CanvasOperation): boolean {
    return operation.type === 'delete' || 
           (operation.type === 'update' && this.isHighPriorityUpdate(operation.data));
  }

  private isHighPriorityUpdate(data: any): boolean {
    // Check if update affects core canvas structure
    return data && (
      data.nodesChanged || 
      data.edgesChanged || 
      data.metadataChanged
    );
  }

  private async processMessageQueue(): Promise<void> {
    if (this.processingQueue || this.messageQueue.length === 0) {
      return;
    }

    this.processingQueue = true;
    
    try {
      // Process messages in order
      const operations = [...this.messageQueue];
      this.messageQueue = [];

      for (const operation of operations) {
        await this.processOperation(operation);
      }
    } catch (error) {
      console.error('Error processing message queue:', error);
    } finally {
      this.processingQueue = false;
    }
  }

  private async processOperation(operation: CanvasOperation): Promise<void> {
    const message = this.createMQTTMessage(operation);
    
    switch (operation.type) {
      case 'create':
      case 'update':
      case 'delete':
        await this.broadcastOperation(operation);
        break;
      case 'share':
        await this.handleShareOperation(operation, message);
        break;
      case 'sync':
        await this.handleSyncOperation(operation, message);
        break;
    }
  }

  private createMQTTMessage(operation: CanvasOperation): MQTTMessageProtocol {
    return {
      version: '1.0.0',
      messageType: `canvas-${operation.type}`,
      payload: operation,
      metadata: {
        source: 'mind-git',
        target: operation.type === 'share' ? operation.data?.targetRepository : undefined,
        priority: this.getOperationPriority(operation),
        requiresAck: operation.type === 'delete' || operation.type === 'share'
      }
    };
  }

  private getOperationPriority(operation: CanvasOperation): 'low' | 'medium' | 'high' | 'critical' {
    switch (operation.type) {
      case 'delete': return 'critical';
      case 'create': return 'high';
      case 'update': return this.isHighPriorityUpdate(operation.data) ? 'high' : 'medium';
      case 'share': return 'medium';
      case 'sync': return 'low';
      default: return 'low';
    }
  }

  private async broadcastOperation(operation: CanvasOperation): Promise<void> {
    const message = this.createMQTTMessage(operation);
    
    // Broadcast to all canvas topic subscribers
    await this.synchronizer.broker.publish(
      this.synchronizer.broker.config.topics.canvas,
      message
    );
  }

  private async handleShareOperation(operation: CanvasOperation, message: MQTTMessageProtocol): Promise<void> {
    if (operation.data?.targetRepository) {
      await this.publishToRepository(operation.data.targetRepository, operation);
    } else {
      await this.broadcastOperation(operation);
    }
  }

  private async handleSyncOperation(operation: CanvasOperation, message: MQTTMessageProtocol): Promise<void> {
    // Send sync request to specific repository or broadcast
    await this.synchronizer.broker.publishSyncRequest(
      operation.data?.targetRepository || 'all',
      [operation.canvasId]
    );
  }

  private async publishToRepository(repository: string, operation: CanvasOperation): Promise<void> {
    const message = this.createMQTTMessage(operation);
    
    // Publish to repository-specific topic
    const topic = `mind-git/${repository}/canvas`;
    await this.synchronizer.broker.publish(topic, message);
  }

  async requestCanvasList(repository: string): Promise<void> {
    const message: MQTTMessageProtocol = {
      version: '1.0.0',
      messageType: 'canvas-list-request',
      payload: {
        repository,
        timestamp: Date.now()
      },
      metadata: {
        source: 'mind-git',
        priority: 'medium',
        requiresAck: true
      }
    };

    const topic = `mind-git/${repository}/sync`;
    await this.synchronizer.broker.publish(topic, message);
  }

  getProtocolStatus(): {
    queuedMessages: number;
    processing: boolean;
    connectedPeers: number;
  } {
    const syncStatus = this.synchronizer.getSyncStatus();
    
    return {
      queuedMessages: this.messageQueue.length,
      processing: this.processingQueue,
      connectedPeers: syncStatus.connectedPeers
    };
  }

  async disconnect(): Promise<void> {
    // Process remaining messages
    await this.processMessageQueue();
    await this.synchronizer.disconnect();
  }
}