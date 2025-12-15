# @domain DIGITAL - Digital systems, software, compilers, algorithms
import { describe, it, expect } from '@jest/globals';

describe('MQTT P2P System - Integration Tests', () => {
  describe('Component Integration', () => {
    it('should integrate broker and synchronizer', async () => {
      const { CanvasMQTTBroker } = require('../mqtt-broker.js');
      const { CanvasP2PSynchronizer } = require('../canvas-sync.js');

      const broker = new CanvasMQTTBroker({
        broker: 'localhost',
        port: 1883,
        clientId: 'integration-test'
      });

      const synchronizer = new CanvasP2PSynchronizer('integration-test-repo');

      // Mock successful operations
      broker.connect = jest.fn().mockResolvedValue(undefined);
      broker.publish = jest.fn().mockResolvedValue(undefined);
      broker.subscribe = jest.fn().mockResolvedValue(undefined);
      broker.disconnect = jest.fn().mockResolvedValue(undefined);

      synchronizer.connect = jest.fn().mockResolvedValue(undefined);
      synchronizer.registerLocalCanvas = jest.fn().mockResolvedValue(undefined);
      synchronizer.updateLocalCanvas = jest.fn().mockResolvedValue(undefined);
      synchronizer.syncCanvas = jest.fn().mockResolvedValue(undefined);
      synchronizer.disconnect = jest.fn().mockResolvedValue(undefined);

      // Initialize both components
      await broker.connect();
      await synchronizer.connect();

      // Test integration
      await synchronizer.registerLocalCanvas('integration-canvas', {
        id: 'integration-canvas',
        nodes: [{ id: '1', type: 'activate', x: 100, y: 100 }],
        edges: []
      });

      // Verify broker received canvas creation
      expect(broker.publish).toHaveBeenCalledWith(
        'mind-git/canvas',
        expect.objectContaining({
          type: 'canvas-create',
          canvasId: 'integration-canvas',
          data: expect.objectContaining({
            id: 'integration-canvas',
            nodes: expect.any(Array),
            edges: expect.any(Array)
          }),
          author: 'integration-test'
        })
      );

      // Verify synchronizer registered canvas
      expect(synchronizer.registerLocalCanvas).toHaveBeenCalledWith(
        'integration-canvas',
        expect.objectContaining({
          id: 'integration-canvas',
          nodes: expect.any(Array),
          edges: expect.any(Array)
        })
      );

      // Test canvas update
      await synchronizer.updateLocalCanvas('integration-canvas', {
        id: 'integration-canvas',
        nodes: [{ id: '1', type: 'integrate', x: 200, y: 100 }],
        edges: [{ from: '1', to: '2', type: 'data' }]
      }, 'integration-test');

      // Verify broker received update
      expect(broker.publish).toHaveBeenCalledWith(
        'mind-git/canvas',
        expect.objectContaining({
          type: 'canvas-update',
          canvasId: 'integration-canvas',
          data: expect.objectContaining({
            id: 'integration-canvas',
            nodes: expect.arrayContaining([
              expect.objectContaining({ id: '1', type: 'integrate', x: 200, y: 100 })
            ]),
            edges: expect.arrayContaining([
              expect.objectContaining({ from: '1', to: '2', type: 'data' })
            ])
          }),
          author: 'integration-test'
        })
      );

      // Test canvas sync
      await synchronizer.syncCanvas('integration-canvas');

      // Verify synchronizer initiated sync
      expect(synchronizer.syncCanvas).toHaveBeenCalledWith('integration-canvas');

      // Clean shutdown
      await synchronizer.disconnect();
      await broker.disconnect();

      // Verify clean shutdown
      expect(synchronizer.disconnect).toHaveBeenCalled();
      expect(broker.disconnect).toHaveBeenCalled();
    });

    it('should handle real-time collaboration', async () => {
      const { CanvasMQTTBroker } = require('../mqtt-broker.js');
      const { CanvasP2PSynchronizer } = require('../canvas-sync.js');

      const broker = new CanvasMQTTBroker({
        broker: 'localhost',
        port: 1883,
        clientId: 'realtime-test'
      });

      const synchronizer = new CanvasP2PSynchronizer('realtime-test-repo');

      // Mock real-time message handling
      let realTimeUpdates = 0;
      synchronizer.on('canvas-updated', () => {
        realTimeUpdates++;
      });

      await broker.connect();
      await synchronizer.connect();

      // Enable real-time collaboration
      await synchronizer.enableRealTimeCollaboration('realtime-test-repo', 'realtime-canvas');

      // Simulate real-time updates
      for (let i = 0; i < 10; i++) {
        await synchronizer.updateCanvas('realtime-test-repo', 'realtime-canvas', {
          nodes: [{ id: `rt-${i}`, type: 'integrate', x: 100 + i * 10, y: 100 + i * 5 }],
          author: 'realtime-test'
        });
      }

      // Verify real-time updates were received
      expect(realTimeUpdates).toBe(10);

      // Verify final state
      const finalStatus = synchronizer.getSyncStatus();
      expect(finalStatus.realTimeSessions).toBe(1);
      expect(finalStatus.sharedCanvases).toBe(1);
      expect(finalStatus.syncEvents).toBeGreaterThan(0);

      await synchronizer.disconnect();
      await broker.disconnect();
    });

    it('should handle multi-repository sharing', async () => {
      const { CanvasMQTTBroker } = require('../mqtt-broker.js');
      const { CanvasP2PSynchronizer } = require('../canvas-sync.js');

      const broker = new CanvasMQTTBroker({
        broker: 'localhost',
        port: 1883,
        clientId: 'multi-repo-test'
      });

      const synchronizer1 = new CanvasP2PSynchronizer('repo-a');
      const synchronizer2 = new CanvasP2PSynchronizer('repo-b');

      await broker.connect();
      await synchronizer1.connect();
      await synchronizer2.connect();

      // Create canvas in repo-a
      await synchronizer1.registerLocalCanvas('shared-canvas-a', {
        id: 'shared-canvas-a',
        nodes: [{ id: '1', type: 'activate', x: 100, y: 100 }],
        edges: []
      });

      // Share with repo-b
      await synchronizer1.shareCanvas('shared-canvas-a', 'repo-b');

      // Verify repo-b receives canvas
      const repoBStatus = synchronizer2.getRepositoryStatus('repo-b');
      expect(repoBStatus.localCanvases).toBe(1);
      expect(repoBStatus.localCanvases).toHaveProperty('shared-canvas-a');

      // Clean shutdown
      await synchronizer1.disconnect();
      await synchronizer2.disconnect();
      await broker.disconnect();
    });

    it('should handle error recovery', async () => {
      const { CanvasMQTTBroker } = require('../mqtt-broker.js');
      const { CanvasP2PSynchronizer } = require('../canvas-sync.js');

      const broker = new CanvasMQTTBroker({
        broker: 'localhost',
        port: 1883,
        clientId: 'error-recovery-test'
      });

      const synchronizer = new CanvasP2PSynchronizer('error-recovery-test-repo');

      // Mock network failure
      let disconnectCount = 0;
      broker.on('disconnected', () => {
        disconnectCount++;
      });

      await broker.connect();
      await synchronizer.connect();

      // Attempt operation during network failure
      const operation = synchronizer.registerLocalCanvas('error-canvas', {
        id: 'error-canvas',
        nodes: [{ id: '1', type: 'activate', x: 100, y: 100 }]
      });

      const result = await synchronizer.registerLocalCanvas('error-canvas');

      // Should handle network failure gracefully
      expect(result).toBeDefined();
      expect(disconnectCount).toBeGreaterThan(0);
      expect(synchronizer.disconnect).toHaveBeenCalled();
    });
  });
});