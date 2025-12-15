# @domain DIGITAL - Digital systems, software, compilers, algorithms
import { describe, it, expect } from '@jest/globals';

describe('MQTT P2P System - Integration Tests', () => {
  describe('End-to-End Workflow', () => {
    it('should complete full canvas collaboration workflow', async () => {
      // This test simulates the complete workflow from canvas creation to sharing
      
      // Step 1: Initialize all components
      const { createP2PNetwork } = await import('../network-manager.js');
      const network = createP2PNetwork({
        broker: { host: 'localhost', port: 1883 },
        repositories: ['workflow-test-repo'],
        enableDiscovery: true,
        syncInterval: 30
      });

      const { createMQTTDemo } = await import('../mqtt-demo.js');
      const demo = createMQTTDemo({
        brokerUrl: 'mqtt://localhost:1883',
        repositories: ['workflow-test-repo'],
        demoCanvases: ['workflow-canvas-1', 'workflow-canvas-2'],
        duration: 5 // 5 minutes
      });

      await network.initialize();
      await demo.initialize();

      // Step 2: Create two canvases
      await demo.createCanvas('workflow-canvas-1', {
        id: 'workflow-canvas-1',
        name: 'Workflow Canvas 1',
        nodes: [
          { id: '1', type: 'activate', x: 100, y: 100 },
          { id: '2', type: 'integrate', x: 200, y: 100 }
        ],
        edges: [
          { from: '1', to: '2', type: 'data' }
        ]
      });

      await demo.createCanvas('workflow-canvas-2', {
        id: 'workflow-canvas-2',
        name: 'Workflow Canvas 2',
        nodes: [
          { id: '3', type: 'transform', x: 300, y: 100 },
          { id: '4', type: 'store', x: 400, y: 100 }
        ],
        edges: [
          { from: '2', to: '3', type: 'transform' },
          { from: '3', to: '4', type: 'data' }
        ]
      });

      // Step 3: Enable real-time collaboration on first canvas
      await demo.enableRealTimeCollaboration('workflow-test-repo', 'workflow-canvas-1');

      // Step 4: Share first canvas with second repository
      await demo.shareCanvas('workflow-test-repo', 'workflow-canvas-1', 'workflow-repo-2');

      // Step 5: Simulate real-time updates on first canvas
      for (let i = 0; i < 10; i++) {
        await new Promise(resolve => setTimeout(resolve, 1000));
        
        // Simulate remote update
        await demo.updateCanvas('workflow-test-repo', 'workflow-canvas-1', {
          nodes: [{ id: '1', type: 'integrate', x: 100 + i * 10, y: 100 + i * 5 }],
          author: 'collaborator-1'
        });
      }

      // Step 6: Sync second repository
      await demo.syncCanvas('workflow-repo-2', 'workflow-canvas-2');

      // Step 7: Verify final state
      const finalStatus = demo.getFinalStatus();
      
      expect(finalStatus.totalCanvases).toBe(2);
      expect(finalStatus.sharedCanvases).toBe(1);
      expect(finalStatus.realTimeSessions).toBe(1);
      expect(finalStatus.syncEvents).toBeGreaterThan(0);
    }, 30000); // 30 second timeout
  });

  describe('Multi-Repository Scenarios', () => {
    it('should handle canvas sharing across repositories', async () => {
      const { createP2PNetwork } = await import('../network-manager.js');
      const network = createP2PNetwork({
        broker: { host: 'localhost', port: 1883 },
        repositories: ['repo-a', 'repo-b', 'repo-c'],
        enableDiscovery: true,
        syncInterval: 30
      });

      await network.initialize();

      // Create canvas in repo-a
      const canvasA = {
        id: 'shared-canvas',
        name: 'Shared Canvas',
        nodes: [
          { id: '1', type: 'activate', x: 100, y: 100 }
        ],
        edges: []
      };

      await network.createCanvas('repo-a', 'shared-canvas', canvasA, 'creator-a');

      // Share with repo-b
      await network.shareCanvas('repo-a', 'shared-canvas', 'repo-b');

      // Verify repo-b receives the canvas
      await new Promise(resolve => setTimeout(resolve, 2000)); // Wait for propagation

      const repoBStatus = network.getRepositoryStatus('repo-b');
      expect(repoBStatus.localCanvases).toBe(1);
      expect(repoBStatus.localCanvases).toHaveProperty('shared-canvas');
    }, 15000); // 15 second timeout
  });

  describe('Error Recovery', () => {
    it('should recover from broker disconnection', async () => {
      const { createP2PNetwork } = await import('../network-manager.js');
      const network = createP2PNetwork({
        broker: { host: 'localhost', port: 1883 },
        repositories: ['recovery-test-repo'],
        enableDiscovery: true,
        syncInterval: 30
      });

      await network.initialize();

      // Simulate broker disconnection
      let disconnectCount = 0;
      network.on('disconnected', () => {
        disconnectCount++;
      });

      // Create canvas
      await network.createCanvas('recovery-test-repo', 'recovery-canvas', {
        id: 'recovery-canvas',
        nodes: [{ id: '1', type: 'activate', x: 100, y: 100 }]
      }, 'recovery-test');

      // Should handle disconnection gracefully
      await new Promise(resolve => setTimeout(resolve, 5000)); // 5 seconds

      expect(disconnectCount).toBeGreaterThan(0);
      
      // Should reconnect automatically
      await new Promise(resolve => setTimeout(resolve, 1000)); // 1 second

      // Should be reconnected
      const status = network.getRepositoryStatus('recovery-test-repo');
      expect(status.connected).toBe(true);
    }, 10000); // 10 second timeout
  });

  describe('Performance Under Load', () => {
    it('should maintain performance with 100 concurrent operations', async () => {
      const { createP2PNetwork } = await import('../network-manager.js');
      const network = createP2PNetwork({
        broker: { host: 'localhost', port: 1883 },
        repositories: ['load-test-repo'],
        enableDiscovery: true,
        syncInterval: 30,
        performance: {
          maxMessageSize: 64 * 1024,
          maxConnections: 1000 // High limit for load test
        }
      });

      await network.initialize();

      const startTime = Date.now();
      const operations = [];

      // Create 100 concurrent operations
      for (let i = 0; i < 100; i++) {
        const operation = network.createCanvas('load-test-repo', `load-canvas-${i}`, {
          id: `load-canvas-${i}`,
          nodes: [{ id: '1', type: 'activate', x: 100, y: 100 }]
        }, 'load-test');

        operations.push(operation);
      }

      // Wait for all operations to complete
      await Promise.all(operations);

      const endTime = Date.now();
      const duration = endTime - startTime;
      const operationsPerSecond = 100 / (duration / 1000);

      // Performance should remain acceptable under load
      expect(operationsPerSecond).toBeGreaterThan(50); // At least 50 ops/sec
      expect(duration).toBeLessThan(30000); // Complete within 30 seconds
      expect(operations.length).toBe(100); // All operations completed
    }, 60000); // 60 second timeout
  });
});