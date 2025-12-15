// @domain DIGITAL - Digital systems, software, compilers, algorithms
import { createMQTTTester } from './mqtt-tester.js';
import { DEFAULT_MQTT_INTEGRATION_CONFIG } from './mqtt-integration.js';
import { createP2PNetwork } from './network-manager.js';

export interface MQTTDemoConfig {
  brokerUrl: string;
  repositories: string[];
  demoCanvases: string[];
  duration: number; // in minutes
}

export interface DemoResult {
  success: boolean;
  operationsCompleted: number;
  errors: string[];
  performance: {
    avgLatency: number;
    throughput: number;
    uptime: number;
  };
  collaboration: {
    realTimeSessions: number;
    sharedCanvases: number;
    syncEvents: number;
  };
}

export class MQTTDemo {
  private network: any;
  private tester: any;
  private config: MQTTDemoConfig;
  private startTime: number = 0;
  private operations: number = 0;
  private errors: string[] = [];

  constructor(config: MQTTDemoConfig) {
    this.config = config;
    this.network = createP2PNetwork({
      broker: new URL(config.brokerUrl).hostname || 'localhost',
      port: parseInt(new URL(config.brokerUrl).port) || 1883,
      repositories: config.repositories,
      enableDiscovery: true,
      syncInterval: 30
    });

    this.tester = createMQTTTester({
      brokerUrl: config.brokerUrl,
      testRepositories: config.repositories,
      testMessageSize: 1024,
      testDuration: 60
    });
  }

  async runDemo(): Promise<DemoResult> {
    console.log('Starting MQTT Demo...');
    this.startTime = Date.now();

    try {
      // Step 1: Initialize and test MQTT integration
      console.log('Step 1: Testing MQTT Integration...');
      const testResult = await this.tester.runFullTest();
      
      if (!testResult.success) {
        throw new Error('MQTT integration tests failed');
      }

      console.log('✅ MQTT integration tests passed');

      // Step 2: Initialize P2P network
      console.log('Step 2: Initializing P2P Network...');
      await this.network.initialize();

      // Step 3: Create demo canvases
      console.log('Step 3: Creating demo canvases...');
      await this.createDemoCanvases();

      // Step 4: Demonstrate real-time collaboration
      console.log('Step 4: Demonstrating real-time collaboration...');
      await this.demonstrateRealTimeCollaboration();

      // Step 5: Demonstrate canvas sharing
      console.log('Step 5: Demonstrating canvas sharing...');
      await this.demonstrateCanvasSharing();

      // Step 6: Demonstrate synchronization
      console.log('Step 6: Demonstrating synchronization...');
      await this.demonstrateSynchronization();

      const endTime = Date.now();
      const duration = (endTime - this.startTime) / 1000 / 60; // minutes

      const result: DemoResult = {
        success: this.errors.length === 0,
        operationsCompleted: this.operations,
        errors: this.errors,
        performance: {
          avgLatency: testResult.messageLatency,
          throughput: testResult.throughput,
          uptime: duration
        },
        collaboration: {
          realTimeSessions: this.config.demoCanvases.length,
          sharedCanvases: this.config.demoCanvases.length,
          syncEvents: this.operations
        }
      };

      console.log('✅ MQTT Demo completed successfully');
      this.logDemoResults(result);

      return result;

    } catch (error) {
      this.errors.push(`Demo execution error: ${error}`);
      
      const result: DemoResult = {
        success: false,
        operationsCompleted: this.operations,
        errors: this.errors,
        performance: { avgLatency: 0, throughput: 0, uptime: 0 },
        collaboration: { realTimeSessions: 0, sharedCanvases: 0, syncEvents: 0 }
      };

      console.log('❌ MQTT Demo failed');
      this.logDemoResults(result);

      return result;
    } finally {
      await this.cleanup();
    }
  }

  private async createDemoCanvases(): Promise<void> {
    for (const canvasId of this.config.demoCanvases) {
      try {
        const canvasData = {
          id: canvasId,
          name: `Demo Canvas ${canvasId}`,
          nodes: [
            { id: '1', type: 'activate', x: 100, y: 100 },
            { id: '2', type: 'integrate', x: 200, y: 100 },
            { id: '3', type: 'transform', x: 300, y: 100 }
          ],
          edges: [
            { from: '1', to: '2', type: 'data' },
            { from: '2', to: '3', type: 'transform' }
          ],
          metadata: {
            created: Date.now(),
            author: 'mqtt-demo',
            version: '1.0.0'
          }
        };

        await this.network.createCanvas(
          this.config.repositories[0], 
          canvasId, 
          canvasData, 
          'mqtt-demo'
        );

        this.operations++;
        console.log(`Created demo canvas: ${canvasId}`);

      } catch (error) {
        this.errors.push(`Failed to create canvas ${canvasId}: ${error}`);
      }
    }
  }

  private async demonstrateRealTimeCollaboration(): Promise<void> {
    for (const canvasId of this.config.demoCanvases) {
      try {
        // Enable real-time collaboration
        await this.network.enableRealTimeCollaboration(
          this.config.repositories[0], 
          canvasId
        );

        // Simulate real-time updates
        for (let i = 0; i < 3; i++) {
          const update = {
            nodes: [
              { id: `update-${i}`, type: 'integrate', x: 150 + i * 20, y: 120 }
            ],
            edges: [
              { from: '1', to: `update-${i}`, type: 'data' }
            ]
          };

          await this.network.updateCanvas(
            this.config.repositories[0], 
            canvasId, 
            update, 
            'mqtt-demo'
          );

          this.operations++;
          await new Promise(resolve => setTimeout(resolve, 1000)); // 1 second between updates
        }

        console.log(`Real-time collaboration demonstrated for canvas: ${canvasId}`);

      } catch (error) {
        this.errors.push(`Real-time collaboration failed for ${canvasId}: ${error}`);
      }
    }
  }

  private async demonstrateCanvasSharing(): Promise<void> {
    const sourceRepo = this.config.repositories[0];
    const targetRepo = this.config.repositories[1] || this.config.repositories[0];

    for (const canvasId of this.config.demoCanvases) {
      try {
        // Share canvas with another repository
        await this.network.shareCanvas(sourceRepo, canvasId, targetRepo);
        this.operations++;
        console.log(`Shared canvas ${canvasId} from ${sourceRepo} to ${targetRepo}`);

      } catch (error) {
        this.errors.push(`Canvas sharing failed for ${canvasId}: ${error}`);
      }
    }
  }

  private async demonstrateSynchronization(): Promise<void> {
    for (const repository of this.config.repositories) {
      try {
        // Trigger repository synchronization
        await this.network.syncRepository(repository);
        this.operations++;
        console.log(`Synchronization triggered for repository: ${repository}`);

      } catch (error) {
        this.errors.push(`Synchronization failed for ${repository}: ${error}`);
      }
    }
  }

  private logDemoResults(result: DemoResult): void {
    console.log('\n=== MQTT Demo Results ===');
    console.log(`Success: ${result.success ? '✅ PASS' : '❌ FAIL'}`);
    console.log(`Duration: ${result.performance.uptime.toFixed(1)} minutes`);
    console.log(`Operations Completed: ${result.operationsCompleted}`);
    console.log(`Errors: ${result.errors.length}`);

    console.log('\nPerformance Metrics:');
    console.log(`Average Latency: ${result.performance.avgLatency}ms`);
    console.log(`Throughput: ${result.performance.throughput.toFixed(2)} msg/s`);

    console.log('\nCollaboration Metrics:');
    console.log(`Real-time Sessions: ${result.collaboration.realTimeSessions}`);
    console.log(`Shared Canvases: ${result.collaboration.sharedCanvases}`);
    console.log(`Sync Events: ${result.collaboration.syncEvents}`);

    if (result.errors.length > 0) {
      console.log('\nErrors:');
      result.errors.forEach((error, index) => {
        console.log(`${index + 1}. ${error}`);
      });
    }

    console.log('\nRecommendations:');
    if (result.success) {
      console.log('✅ MQTT integration is ready for production use');
      console.log('✅ Consider enabling encryption for sensitive data');
      console.log('✅ Monitor network performance in production');
    } else {
      console.log('❌ Address errors before production deployment');
      console.log('❌ Review network configuration');
      console.log('❌ Check broker connectivity and performance');
    }

    console.log('==============================');
  }

  private async cleanup(): Promise<void> {
    console.log('Cleaning up MQTT Demo...');
    
    try {
      await this.network.disconnect();
      await this.tester.cleanup();
      console.log('✅ Cleanup completed');
    } catch (error) {
      console.error('Cleanup error:', error);
    }
  }
}

// Factory function for easy demo setup
export function createMQTTDemo(config: Partial<MQTTDemoConfig> = {}): MQTTDemo {
  const defaultConfig: MQTTDemoConfig = {
    brokerUrl: 'mqtt://localhost:1883',
    repositories: ['demo-repo-1', 'demo-repo-2'],
    demoCanvases: ['demo-canvas-1', 'demo-canvas-2', 'demo-canvas-3'],
    duration: 10, // 10 minutes
    ...config
  };

  return new MQTTDemo(defaultConfig);
}