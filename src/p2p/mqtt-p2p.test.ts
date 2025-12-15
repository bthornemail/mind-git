// @domain DIGITAL - Digital systems, software, compilers, algorithms
import { describe, it, expect, beforeEach, afterEach } from '@jest/globals';

import { CanvasMQTTBroker } from '../mqtt-broker.js';
import { CanvasP2PSynchronizer } from '../canvas-sync.js';
import { P2PNetworkManager } from '../network-manager.js';
import { MQTTIntegrationService } from '../mqtt-integration.js';
import { MQTTIntegrationTester } from '../mqtt-tester.js';
import { createMQTTDemo } from '../mqtt-demo.js';

describe('MQTT P2P Canvas System', () => {
  let broker: CanvasMQTTBroker;
  let network: P2PNetworkManager;
  let integration: MQTTIntegrationService;
  let tester: MQTTIntegrationTester;

  beforeEach(() => {
    // Reset all components
    broker = new CanvasMQTTBroker({
      broker: 'localhost',
      port: 1883,
      clientId: 'test-broker'
    });

    network = new P2PNetworkManager({
      broker: 'localhost',
      port: 1883,
      repositories: ['test-repo-1', 'test-repo-2']
    });

    integration = new MQTTIntegrationService({
      broker: { host: 'localhost', port: 1883 },
      repositories: ['test-repo-1', 'test-repo-2'],
      features: {
        realTimeCollaboration: true,
        autoSync: true,
        discovery: true,
        encryption: false
      }
    });

    tester = new MQTTIntegrationTester({
      brokerUrl: 'mqtt://localhost:1883',
      testRepositories: ['test-repo-1', 'test-repo-2'],
      testMessageSize: 1024,
      testDuration: 60
    });
  });

  afterEach(async () => {
    // Clean up all components
    try {
      if (tester) await tester.cleanup();
      if (integration) await integration.disconnect();
      if (network) await network.disconnect();
      if (broker) await broker.disconnect();
    } catch (error) {
      console.error('Cleanup error:', error);
    }
  });

  describe('CanvasMQTTBroker', () => {
    it('should connect to MQTT broker', async () => {
      await expect(broker.connect()).resolves.toBeUndefined();
      expect(broker.isConnected()).toBe(true);
    });

    it('should publish and receive messages', async () => {
      let messageReceived = false;
      
      broker.on('canvas-updated', () => {
        messageReceived = true;
      });

      await broker.connect();
      await broker.publishCanvasUpdate('test-canvas', 'test-repo', { test: 'data' }, 'test-author');
      
      // Wait for message processing
      await new Promise(resolve => setTimeout(resolve, 100));
      
      expect(messageReceived).toBe(true);
    });

    it('should handle disconnection', async () => {
      await broker.connect();
      expect(broker.isConnected()).toBe(true);
      
      await broker.disconnect();
      expect(broker.isConnected()).toBe(false);
    });
  });

  describe('CanvasP2PSynchronizer', () => {
    it('should synchronize canvas state', async () => {
      const sync = new CanvasP2PSynchronizer('test-repo');
      
      await sync.connect();
      await sync.registerLocalCanvas('test-canvas');
      
      const status = sync.getSyncStatus();
      expect(status.localCanvases).toBe(1);
      
      await sync.disconnect();
    });

    it('should handle remote updates', async () => {
      const sync = new CanvasP2PSynchronizer('test-repo');
      
      let updateReceived = false;
      sync.on('canvas-updated', () => {
        updateReceived = true;
      });
      
      await sync.connect();
      
      // Simulate remote update
      const broker = new CanvasMQTTBroker({
        broker: 'localhost',
        port: 1884, // Different port to avoid conflicts
        clientId: 'remote-simulator'
      });
      
      await broker.connect();
      await broker.publishCanvasUpdate('test-canvas', 'test-repo', { updated: true }, 'remote-author');
      
      // Wait for message processing
      await new Promise(resolve => setTimeout(resolve, 200));
      
      expect(updateReceived).toBe(true);
      
      await broker.disconnect();
      await sync.disconnect();
    });
  });

  describe('P2PNetworkManager', () => {
    it('should initialize multiple repositories', async () => {
      await network.initialize();
      
      const status = network.getAllRepositoryStatuses();
      expect(Object.keys(status)).toHaveLength(2);
      expect(status['test-repo-1']).toBeDefined();
      expect(status['test-repo-2']).toBeDefined();
    });

    it('should discover peers', async () => {
      await network.initialize();
      
      const peers = await network.discoverPeers();
      expect(Array.isArray(peers)).toBe(true);
    });

    it('should provide network statistics', async () => {
      await network.initialize();
      
      const stats = network.getNetworkStats();
      expect(stats).toHaveProperty('connectedPeers');
      expect(stats).toHaveProperty('activeCanvases');
      expect(stats).toHaveProperty('messagesPerSecond');
      expect(stats).toHaveProperty('uptime');
    });
  });

  describe('MQTTIntegrationService', () => {
    it('should initialize with configuration', async () => {
      await integration.initialize();
      
      const status = integration.getRepositoryStatus('test-repo-1');
      expect(status.connected).toBe(true);
    });

    it('should create and update canvases', async () => {
      await integration.initialize();
      
      await integration.createCanvas('test-repo-1', 'new-canvas', { nodes: [] }, 'test-author');
      await integration.updateCanvas('test-repo-1', 'new-canvas', { nodes: [{ id: '1' }] }, 'test-author');
      
      // Verify operations completed without errors
      expect(true).toBe(true); // If we get here, no exceptions were thrown
    });

    it('should handle canvas sharing', async () => {
      await integration.initialize();
      
      await integration.shareCanvas('test-repo-1', 'new-canvas', 'test-repo-2');
      
      // Verify share operation completed
      expect(true).toBe(true);
    });

    it('should provide health checks', async () => {
      await integration.initialize();
      
      const health = await integration.healthCheck();
      expect(health.healthy).toBe(true);
      expect(health.issues).toHaveLength(0);
    });
  });

  describe('MQTTIntegrationTester', () => {
    it('should run comprehensive tests', async () => {
      const result = await tester.runFullTest();
      
      expect(result.success).toBe(true);
      expect(result.connectionLatency).toBeLessThan(1000); // Less than 1 second
      expect(result.messageLatency).toBeLessThan(500); // Less than 500ms
      expect(result.throughput).toBeGreaterThan(0);
      expect(result.errorCount).toBe(0);
    });

    it('should validate configuration', () => {
      const validConfig = {
        broker: { host: 'localhost', port: 1883 },
        repositories: ['test-repo'],
        features: {
          realTimeCollaboration: true,
          autoSync: true,
          discovery: true,
          encryption: false
        },
        performance: {
          maxMessageSize: 64 * 1024,
          maxConnections: 100,
          heartbeatInterval: 60
        }
      };

      const validation = integration.validateConfig(validConfig);
      expect(validation.valid).toBe(true);
      expect(validation.errors).toHaveLength(0);
    });
  });

  describe('Integration Tests', () => {
    it('should demonstrate full workflow', async () => {
      // Initialize all components
      await broker.connect();
      await network.initialize();
      await integration.initialize();
      
      // Create canvas through integration service
      await integration.createCanvas('test-repo-1', 'integration-test', { nodes: [] }, 'integration-test');
      
      // Verify canvas appears in network
      await new Promise(resolve => setTimeout(resolve, 500)); // Wait for propagation
      
      const networkStatus = network.getNetworkStats();
      expect(networkStatus.activeCanvases).toBeGreaterThan(0);
      
      // Test real-time collaboration
      await integration.enableRealTimeCollaboration('test-repo-1', 'integration-test');
      
      // Update canvas
      await integration.updateCanvas('test-repo-1', 'integration-test', { nodes: [{ id: '1' }] }, 'integration-test');
      
      // Test performance
      const perfResult = await integration.performanceTest();
      expect(perfResult.success).toBe(true);
      
      // Clean up
      await integration.disconnect();
      await network.disconnect();
      await broker.disconnect();
    });

    it('should handle connection failures gracefully', async () => {
      // Test with invalid broker
      const invalidIntegration = new MQTTIntegrationService({
        broker: { host: 'invalid-host', port: 9999 },
        repositories: ['test-repo'],
        features: { realTimeCollaboration: true, autoSync: true, discovery: true, encryption: false }
      });

      await expect(invalidIntegration.initialize()).rejects.toThrow();
    });
  });

  describe('Performance Tests', () => {
    it('should handle high message volume', async () => {
      await broker.connect();
      
      const startTime = Date.now();
      const messageCount = 100;
      
      // Send many messages rapidly
      for (let i = 0; i < messageCount; i++) {
        await broker.publishCanvasUpdate(`test-canvas-${i}`, 'test-repo', { index: i }, 'perf-test');
      }
      
      const endTime = Date.now();
      const duration = endTime - startTime;
      const messagesPerSecond = messageCount / (duration / 1000);
      
      expect(messagesPerSecond).toBeGreaterThan(50); // Should handle at least 50 msg/sec
      expect(duration).toBeLessThan(5000); // Should complete within 5 seconds
      
      await broker.disconnect();
    });

    it('should maintain connection stability', async () => {
      await broker.connect();
      
      // Test connection stability over time
      const stableDuration = 10000; // 10 seconds
      
      await new Promise(resolve => setTimeout(resolve, stableDuration));
      
      expect(broker.isConnected()).toBe(true);
      
      await broker.disconnect();
    });
  });

  describe('Error Handling', () => {
    it('should handle network disconnections', async () => {
      await broker.connect();
      
      // Simulate network failure
      await broker.disconnect();
      
      expect(broker.isConnected()).toBe(false);
      
      // Should handle reconnection gracefully
      await expect(broker.connect()).resolves.toBeUndefined();
    });

    it('should handle malformed messages', async () => {
      let errorCount = 0;
      
      broker.on('error', () => {
        errorCount++;
      });
      
      await broker.connect();
      
      // Send malformed message
      const originalPublish = broker.publish.bind(broker);
      broker.publish = () => Promise.reject(new Error('Malformed message'));
      
      await expect(originalPublish('test-canvas', 'test-repo', {}, 'test')).rejects.toThrow();
      
      // Should not crash the broker
      expect(broker.isConnected()).toBe(true);
      expect(errorCount).toBeGreaterThan(0);
    });
  });
});