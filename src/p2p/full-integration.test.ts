# @domain DIGITAL - Digital systems, software, compilers, algorithms
import { describe, it, expect } from '@jest/globals';

describe('MQTT P2P System - Final Integration', () => {
  describe('Complete System Integration', () => {
    it('should demonstrate full workflow', async () => {
      // This test demonstrates the complete MQTT P2P system working together
      const { createP2PNetwork } = require('../network-manager.js');
      const { createMQTTDemo } = require('../mqtt-demo.js');
      const { createMQTTTester } = require('../mqtt-tester.js');

      // Initialize all components
      const network = createP2PNetwork({
        broker: { host: 'localhost', port: 1883 },
        repositories: ['integration-test-repo'],
        enableDiscovery: true,
        syncInterval: 30
      });

      const demo = createMQTTDemo({
        brokerUrl: 'mqtt://localhost:1883',
        repositories: ['integration-test-repo'],
        demoCanvases: ['integration-canvas-1', 'integration-canvas-2'],
        duration: 10
      });

      const tester = createMQTTTester({
        brokerUrl: 'mqtt://localhost:1883',
        testRepositories: ['integration-test-repo'],
        testMessageSize: 1024,
        testDuration: 60
      });

      // Initialize system
      await network.initialize();
      await demo.initialize();

      // Run comprehensive test suite
      const testResults = await tester.runFullTest();

      // Verify all components work together
      expect(testResults.success).toBe(true);
      expect(testResults.performance.avgLatency).toBeLessThan(1000);
      expect(testResults.performance.throughput).toBeGreaterThan(100);
      expect(testResults.performance.memoryUsage.heapUsed).toBeLessThan(512 * 1024 * 1024);

      // Verify demo functionality
      const demoResults = await demo.runDemo();
      expect(demoResults.success).toBe(true);
      expect(demoResults.operationsCompleted).toBeGreaterThan(0);
      expect(demoResults.collaboration.realTimeSessions).toBeGreaterThan(0);
      expect(demoResults.sharedCanvases).toBeGreaterThan(0);

      // Clean shutdown
      await network.disconnect();
      await demo.disconnect();
    });
  });
});