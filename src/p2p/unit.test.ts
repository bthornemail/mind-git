# @domain DIGITAL - Digital systems, software, compilers, algorithms
import { describe, it, expect } from '@jest/globals';

describe('MQTT P2P System - Unit Tests', () => {
  describe('CanvasMQTTBroker', () => {
    it('should create broker with default config', () => {
      const { CanvasMQTTBroker } = require('../mqtt-broker.js');
      const broker = new CanvasMQTTBroker({
        broker: 'localhost',
        port: 1883,
        clientId: 'test-broker'
      });

      expect(broker).toBeDefined();
      expect(broker.config.broker).toBe('localhost');
      expect(broker.config.port).toBe(1883);
    });

    it('should handle connection events', async () => {
      const { CanvasMQTTBroker } = require('../mqtt-broker.js');
      const broker = new CanvasMQTTBroker({
        broker: 'localhost',
        port: 1883,
        clientId: 'test-broker'
      });

      let connectCalled = false;
      broker.on('connected', () => {
        connectCalled = true;
      });

      await broker.connect();
      expect(connectCalled).toBe(true);
    });

    it('should publish messages', async () => {
      const { CanvasMQTTBroker } = require('../mqtt-broker.js');
      const broker = new CanvasMQTTBroker({
        broker: 'localhost',
        port: 1883,
        clientId: 'test-broker'
      });

      let publishedMessage = null;
      broker.on('message', (topic, message) => {
        if (topic === 'test-topic') {
          publishedMessage = message;
        }
      });

      await broker.connect();
      await broker.publish('test-topic', 'test-message');

      expect(publishedMessage).toBe('test-message');
    });
  });

  describe('CanvasP2PSynchronizer', () => {
    it('should manage local canvas state', () => {
      const { CanvasP2PSynchronizer } = require('../canvas-sync.js');
      const sync = new CanvasP2PSynchronizer('test-repo');

      expect(sync).toBeDefined();
      expect(sync.getSyncStatus().localCanvases).toBe(0);
    });

    it('should register local canvas', async () => {
      const { CanvasP2PSynchronizer } = require('../canvas-sync.js');
      const sync = new CanvasP2PSynchronizer('test-repo');

      await sync.registerLocalCanvas('test-canvas');
      const status = sync.getSyncStatus();

      expect(status.localCanvases).toBe(1);
      expect(status.localCanvases).toHaveProperty('test-canvas');
    });
  });

  describe('P2PNetworkManager', () => {
    it('should initialize with multiple repositories', () => {
      const { P2PNetworkManager } = require('../network-manager.js');
      const network = new P2PNetworkManager({
        broker: { host: 'localhost', port: 1883 },
        repositories: ['repo1', 'repo2'],
        enableDiscovery: true,
        syncInterval: 30
      });

      expect(network).toBeDefined();
      expect(network.config.repositories).toEqual(['repo1', 'repo2']);
    });

    it('should track network statistics', () => {
      const { P2PNetworkManager } = require('../network-manager.js');
      const network = new P2PNetworkManager({
        broker: { host: 'localhost', port: 1883 },
        repositories: ['repo1'],
        enableDiscovery: true,
        syncInterval: 30
      });

      const stats = network.getNetworkStats();

      expect(stats).toHaveProperty('connectedPeers');
      expect(stats).toHaveProperty('activeCanvases');
      expect(stats).toHaveProperty('messagesPerSecond');
      expect(stats).toHaveProperty('uptime');
    });
  });

  describe('MQTTIntegrationService', () => {
    it('should validate configuration', () => {
      const { MQTTIntegrationService } = require('../mqtt-integration.js');
      const service = new MQTTIntegrationService({
        broker: { host: 'localhost', port: 1883 },
        repositories: ['test-repo'],
        features: {
          realTimeCollaboration: true,
          autoSync: true,
          discovery: true,
          encryption: false
        }
      });

      const validConfig = {
        broker: { host: 'localhost', port: 1883 },
        repositories: ['test-repo'],
        features: {
          realTimeCollaboration: true,
          autoSync: true,
          discovery: true,
          encryption: false
        }
      };

      const validation = service.validateConfig(validConfig);

      expect(validation.valid).toBe(true);
      expect(validation.errors).toHaveLength(0);
    });

    it('should handle health checks', async () => {
      const { MQTTIntegrationService } = require('../mqtt-integration.js');
      const service = new MQTTIntegrationService({
        broker: { host: 'localhost', port: 1883 },
        repositories: ['test-repo'],
        features: {
          realTimeCollaboration: true,
          autoSync: true,
          discovery: true,
          encryption: false
        }
      });

      // Mock successful health check
      service.testConnection = jest.fn().mockResolvedValue(true);
      service.getNetworkStats = jest.fn().mockReturnValue({
        connectedPeers: 5,
        activeCanvases: 3,
        messagesPerSecond: 25,
        uptime: 300
      });

      const health = await service.healthCheck();

      expect(health.healthy).toBe(true);
      expect(health.issues).toHaveLength(0);
    });
  });

  describe('Message Protocol', () => {
    it('should create standardized messages', () => {
      const { CanvasMQTTProtocol } = require('../mqtt-protocol.js');
      const protocol = new CanvasMQTTProtocol('test-repo');

      const message = protocol.createMQTTMessage({
        type: 'create',
        canvasId: 'test-canvas',
        data: { test: 'data' },
        author: 'test-author'
      });

      expect(message).toHaveProperty('version');
      expect(message).toHaveProperty('messageType');
      expect(message).toHaveProperty('payload');
      expect(message).toHaveProperty('metadata');
      expect(message.version).toBe('1.0.0');
      expect(message.messageType).toBe('canvas-create');
      expect(message.metadata.source).toBe('mind-git');
      expect(message.metadata.priority).toBe('high');
      expect(message.metadata.requiresAck).toBe(true);
    });

    it('should handle message prioritization', () => {
      const { CanvasMQTTProtocol } = require('../mqtt-protocol.js');
      const protocol = new CanvasMQTTProtocol('test-repo');

      const criticalMessage = protocol.createMQTTMessage({
        type: 'delete',
        canvasId: 'test-canvas',
        author: 'test-author'
      });

      const normalMessage = protocol.createMQTTMessage({
        type: 'update',
        canvasId: 'test-canvas',
        data: { minor: 'update' },
        author: 'test-author'
      });

      expect(criticalMessage.metadata.priority).toBe('critical');
      expect(normalMessage.metadata.priority).toBe('medium');
    });
  });

  describe('Error Handling', () => {
    it('should handle missing configuration', () => {
      const { MQTTIntegrationService } = require('../mqtt-integration.js');
      const service = new MQTTIntegrationService({
        broker: { host: '', port: 0 }, // Invalid
        repositories: [], // Invalid
        features: {
          realTimeCollaboration: true,
          autoSync: true,
          discovery: true,
          encryption: false
        }
      });

      const validation = service.validateConfig(service.config);

      expect(validation.valid).toBe(false);
      expect(validation.errors.length).toBeGreaterThan(0);
      expect(validation.errors.some(e => e.includes('Broker configuration is required'))).toBe(true);
      expect(validation.errors.some(e => e.includes('At least one repository must be specified'))).toBe(true);
    });

    it('should handle network failures', () => {
      const { MQTTIntegrationService } = require('../mqtt-integration.js');
      const service = new MQTTIntegrationService({
        broker: { host: 'localhost', port: 1883 },
        repositories: ['test-repo'],
        features: {
          realTimeCollaboration: true,
          autoSync: true,
          discovery: true,
          encryption: false
        }
      });

      // Mock connection failure
      service.testConnection = jest.fn().mockResolvedValue(false);

      const health = await service.healthCheck();

      expect(health.healthy).toBe(false);
      expect(health.issues.length).toBeGreaterThan(0);
      expect(health.issues.some(e => e.includes('Not connected to MQTT broker'))).toBe(true);
    });
  });

  describe('Performance', () => {
    it('should handle large message sizes', () => {
      const { MQTTIntegrationService } = require('../mqtt-integration.js');
      const service = new MQTTIntegrationService({
        broker: { host: 'localhost', port: 1883 },
        repositories: ['test-repo'],
        features: {
          realTimeCollaboration: true,
          autoSync: true,
          discovery: true,
          encryption: false
        },
        performance: {
          maxMessageSize: 1024, // 1KB
          maxConnections: 100,
          heartbeatInterval: 60
        }
      });

      // Test with message at size limit
      const largeMessage = new Array(1024).fill(0).map(() => Math.random());
      
      // This should not throw an error
      expect(() => {
        service.broadcastMessage({
          type: 'test',
          data: largeMessage
        });
      }).not.toThrow();
    });

    it('should reject oversized messages', () => {
      const { MQTTIntegrationService } = require('../mqtt-integration.js');
      const service = new MQTTIntegrationService({
        broker: { host: 'localhost', port: 1883 },
        repositories: ['test-repo'],
        features: {
          realTimeCollaboration: true,
          autoSync: true,
          discovery: true,
          encryption: false
        },
        performance: {
          maxMessageSize: 1024, // 1KB
          maxConnections: 100,
          heartbeatInterval: 60
        }
      });

      // Test with oversized message
      const oversizedMessage = new Array(2048).fill(0).map(() => Math.random()); // 2KB
      
      expect(() => {
        service.broadcastMessage({
          type: 'test',
          data: oversizedMessage
        });
      }).toThrow('Message size exceeds maximum allowed size');
    });
  });
});