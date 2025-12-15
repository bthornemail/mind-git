// @domain DIGITAL - Digital systems, software, compilers, algorithms
import { CanvasMQTTBroker, CanvasMessage, DEFAULT_MQTT_CONFIG } from './mqtt-broker.js';
import { readFileSync, writeFileSync } from 'fs';
import { join } from 'path';

export interface CanvasSyncState {
  canvasId: string;
  repository: string;
  lastModified: number;
  checksum: string;
  version: number;
}

export interface SyncPeer {
  id: string;
  repository: string;
  lastSeen: number;
  capabilities: string[];
}

export class CanvasP2PSynchronizer {
  public broker: CanvasMQTTBroker;
  private localState: Map<string, CanvasSyncState> = new Map();
  private peers: Map<string, SyncPeer> = new Map();
  private repository: string;
  private syncInterval: NodeJS.Timeout | null = null;

  constructor(repository: string, brokerConfig = DEFAULT_MQTT_CONFIG) {
    this.repository = repository;
    this.broker = new CanvasMQTTBroker(brokerConfig);
    this.setupEventHandlers();
  }

  private setupEventHandlers(): void {
    this.broker.on('connected', () => {
      console.log('P2P synchronizer connected to MQTT broker');
      this.startSyncProcess();
    });

    this.broker.on('canvas-created', (message: CanvasMessage) => {
      this.handleRemoteCanvasCreated(message);
    });

    this.broker.on('canvas-updated', (message: CanvasMessage) => {
      this.handleRemoteCanvasUpdate(message);
    });

    this.broker.on('sync-request', (message: any) => {
      this.handleSyncRequest(message);
    });

    this.broker.on('client-discovered', (message: any) => {
      this.handlePeerDiscovery(message);
    });
  }

  async connect(): Promise<void> {
    await this.broker.connect();
    
    // Announce presence to network
    await this.announcePresence();
    
    // Request initial sync
    await this.requestInitialSync();
  }

  private async announcePresence(): Promise<void> {
    const announcement = {
      type: 'peer-announcement',
      peerId: this.broker.config.clientId,
      repository: this.repository,
      capabilities: ['canvas-sync', 'real-time-collaboration'],
      timestamp: Date.now()
    };

    await this.broker.publish(this.broker.config.topics.discovery, announcement);
  }

  public async requestInitialSync(): Promise<void> {
    const syncRequest = {
      type: 'initial-sync-request',
      repository: this.repository,
      timestamp: Date.now()
    };

    await this.broker.publish(this.broker.config.topics.sync, syncRequest);
  }

  private async handleRemoteCanvasCreated(message: CanvasMessage): Promise<void> {
    console.log(`Remote canvas created: ${message.canvasId} in ${message.repository}`);
    
    // If we don't have this canvas locally, request it
    if (!this.localState.has(message.canvasId)) {
      await this.requestCanvasSync(message.canvasId, message.repository);
    }
  }

  private async handleRemoteCanvasUpdate(message: CanvasMessage): Promise<void> {
    console.log(`Remote canvas update: ${message.canvasId} from ${message.repository}`);
    
    const localCanvas = this.localState.get(message.canvasId);
    if (localCanvas && message.timestamp > localCanvas.lastModified) {
      // Remote version is newer, request sync
      await this.requestCanvasSync(message.canvasId, message.repository);
    }
  }

  private async handleSyncRequest(message: any): Promise<void> {
    if (message.type === 'initial-sync-request' && message.repository === this.repository) {
      // Respond with our canvas list
      await this.shareCanvasList();
    } else if (message.type === 'canvas-sync-request') {
      // Handle specific canvas sync request
      await this.handleCanvasSyncRequest(message);
    }
  }

  private async handlePeerDiscovery(message: any): Promise<void> {
    console.log(`Peer discovered: ${message.peerId} from ${message.repository}`);
    
    const peer: SyncPeer = {
      id: message.peerId,
      repository: message.repository,
      lastSeen: message.timestamp,
      capabilities: message.capabilities
    };

    this.peers.set(message.peerId, peer);
  }

  public async requestCanvasSync(canvasId: string, repository: string): Promise<void> {
    const syncRequest = {
      type: 'canvas-sync-request',
      canvasId,
      repository,
      timestamp: Date.now()
    };

    await this.broker.publish(this.broker.config.topics.sync, syncRequest);
  }

  private async handleCanvasSyncRequest(message: any): Promise<void> {
    if (message.canvasId && this.localState.has(message.canvasId)) {
      const canvasState = this.localState.get(message.canvasId)!;
      
      // Share canvas data
      const canvasData = {
        type: 'canvas-data',
        canvasId: message.canvasId,
        repository: this.repository,
        data: canvasState,
        timestamp: Date.now()
      };

      await this.broker.publish(this.broker.config.topics.sync, canvasData);
    }
  }

  private async shareCanvasList(): Promise<void> {
    const canvasList = Array.from(this.localState.values()).map(state => ({
      canvasId: state.canvasId,
      repository: state.repository,
      lastModified: state.lastModified,
      checksum: state.checksum
    }));

    const listMessage = {
      type: 'canvas-list-response',
      repository: this.repository,
      canvases: canvasList,
      timestamp: Date.now()
    };

    await this.broker.publish(this.broker.config.topics.sync, listMessage);
  }

  private startSyncProcess(): void {
    // Periodic sync every 30 seconds
    this.syncInterval = setInterval(async () => {
      await this.performPeriodicSync();
    }, 30000);
  }

  private async performPeriodicSync(): Promise<void> {
    // Check for local changes and publish updates
    for (const [canvasId, state] of this.localState) {
      const currentChecksum = await this.calculateCanvasChecksum(canvasId);
      
      if (currentChecksum !== state.checksum) {
        // Canvas has changed, publish update
        const updatedState = {
          ...state,
          lastModified: Date.now(),
          checksum: currentChecksum,
          version: state.version + 1
        };

        this.localState.set(canvasId, updatedState);
        
        await this.broker.publishCanvasUpdate(
          canvasId,
          this.repository,
          updatedState,
          this.broker.config.clientId
        );
      }
    }
  }

  private async calculateCanvasChecksum(canvasId: string): Promise<string> {
    try {
      const canvasPath = join(process.cwd(), 'examples', `${canvasId}.canvas`);
      const canvasData = readFileSync(canvasPath, 'utf-8');
      
      // Simple checksum calculation
      let hash = 0;
      for (let i = 0; i < canvasData.length; i++) {
        const char = canvasData.charCodeAt(i);
        hash = ((hash << 5) - hash) + char;
        hash = hash & hash; // Convert to 32-bit integer
      }
      
      return hash.toString(16);
    } catch (error) {
      console.error(`Error calculating checksum for ${canvasId}:`, error);
      return '';
    }
  }

  async registerLocalCanvas(canvasId: string): Promise<void> {
    const checksum = await this.calculateCanvasChecksum(canvasId);
    
    const state: CanvasSyncState = {
      canvasId,
      repository: this.repository,
      lastModified: Date.now(),
      checksum,
      version: 1
    };

    this.localState.set(canvasId, state);
    
    // Publish canvas creation event
    await this.broker.publishCanvasCreate(
      canvasId,
      this.repository,
      state,
      this.broker.config.clientId
    );
  }

  async updateLocalCanvas(canvasId: string): Promise<void> {
    const state = this.localState.get(canvasId);
    if (state) {
      const checksum = await this.calculateCanvasChecksum(canvasId);
      
      const updatedState = {
        ...state,
        lastModified: Date.now(),
        checksum,
        version: state.version + 1
      };

      this.localState.set(canvasId, updatedState);
      
      // Publish update
      await this.broker.publishCanvasUpdate(
        canvasId,
        this.repository,
        updatedState,
        this.broker.config.clientId
      );
    }
  }

  getSyncStatus(): {
    localCanvases: number;
    connectedPeers: number;
    lastSync: number;
  } {
    return {
      localCanvases: this.localState.size,
      connectedPeers: this.peers.size,
      lastSync: Date.now()
    };
  }

  async disconnect(): Promise<void> {
    if (this.syncInterval) {
      clearInterval(this.syncInterval);
      this.syncInterval = null;
    }
    
    await this.broker.disconnect();
  }
}