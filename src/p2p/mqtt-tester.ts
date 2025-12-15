// @domain DIGITAL - Digital systems, software, compilers, algorithms
import { MQTTIntegrationService, DEFAULT_MQTT_INTEGRATION_CONFIG } from './mqtt-integration.js';

export interface MQTTTestConfig {
  brokerUrl: string;
  testRepositories: string[];
  testMessageSize: number;
  testDuration: number; // in seconds
}

export interface MQTTTestResult {
  success: boolean;
  connectionLatency: number;
  messageLatency: number;
  throughput: number; // messages per second
  errorCount: number;
  errors: string[];
  duration: number; // actual test duration
}

export class MQTTIntegrationTester {
  private service: MQTTIntegrationService;
  private config: MQTTTestConfig;
  private testResults: MQTTTestResult;

  constructor(config: MQTTTestConfig) {
    this.config = config;
    this.service = new MQTTIntegrationService({
      broker: {
        host: new URL(config.brokerUrl).hostname || 'localhost',
        port: parseInt(new URL(config.brokerUrl).port) || 1883
      },
      repositories: config.testRepositories,
      features: {
        realTimeCollaboration: true,
        autoSync: true,
        discovery: true,
        encryption: false
      },
      performance: {
        maxMessageSize: config.testMessageSize,
        maxConnections: 100,
        heartbeatInterval: 30
      }
    });

    this.testResults = {
      success: false,
      connectionLatency: 0,
      messageLatency: 0,
      throughput: 0,
      errorCount: 0,
      errors: [],
      duration: 0
    };
  }

  async runFullTest(): Promise<MQTTTestResult> {
    console.log('Starting MQTT Integration Test...');
    const startTime = Date.now();

    try {
      // Test 1: Connection Test
      await this.testConnection();
      
      // Test 2: Canvas Operations Test
      await this.testCanvasOperations();
      
      // Test 3: Sync Test
      await this.testSynchronization();
      
      // Test 4: Performance Test
      await this.testPerformance();
      
      // Test 5: Discovery Test
      await this.testPeerDiscovery();
      
      this.testResults.duration = Date.now() - startTime;
      this.testResults.success = this.testResults.errorCount === 0;
      
      console.log('MQTT Integration Test completed');
      this.logTestResults();
      
    } catch (error) {
      this.testResults.errors.push(`Test execution error: ${error}`);
      this.testResults.errorCount++;
      this.testResults.duration = Date.now() - startTime;
    }

    return this.testResults;
  }

  private async testConnection(): Promise<void> {
    console.log('Testing MQTT connection...');
    
    const connectStart = Date.now();
    try {
      await this.service.initialize();
      this.testResults.connectionLatency = Date.now() - connectStart;
      console.log(`✅ Connection established in ${this.testResults.connectionLatency}ms`);
    } catch (error) {
      this.testResults.errors.push(`Connection failed: ${error}`);
      this.testResults.errorCount++;
      throw error;
    }
  }

  private async testCanvasOperations(): Promise<void> {
    console.log('Testing canvas operations...');
    
    const testCanvasId = 'test-canvas-' + Date.now();
    const testAuthor = 'mqtt-test';
    
    try {
      // Test canvas creation
      const createStart = Date.now();
      await this.service.createCanvas(
        this.config.testRepositories[0], 
        testCanvasId, 
        { nodes: [], edges: [] }, 
        testAuthor
      );
      this.testResults.messageLatency = Date.now() - createStart;
      console.log(`✅ Canvas creation: ${this.testResults.messageLatency}ms`);
      
      // Test canvas update
      await this.service.updateCanvas(
        this.config.testRepositories[0], 
        testCanvasId, 
        { nodes: [{ id: '1' }], edges: [] }, 
        testAuthor
      );
      console.log('✅ Canvas update successful');
      
      // Test canvas sharing
      await this.service.shareCanvas(
        this.config.testRepositories[0], 
        testCanvasId, 
        this.config.testRepositories[1] || 'target-repo'
      );
      console.log('✅ Canvas share successful');
      
      // Test canvas deletion
      await this.service.deleteCanvas(
        this.config.testRepositories[0], 
        testCanvasId, 
        testAuthor
      );
      console.log('✅ Canvas deletion successful');
      
    } catch (error) {
      this.testResults.errors.push(`Canvas operations failed: ${error}`);
      this.testResults.errorCount++;
    }
  }

  private async testSynchronization(): Promise<void> {
    console.log('Testing synchronization...');
    
    try {
      // Test repository sync
      await this.service.syncRepository(this.config.testRepositories[0]);
      console.log('✅ Repository sync successful');
      
      // Test canvas sync
      const testCanvasId = 'sync-test-canvas';
      await this.service.syncCanvas(this.config.testRepositories[0], testCanvasId);
      console.log('✅ Canvas sync successful');
      
    } catch (error) {
      this.testResults.errors.push(`Synchronization failed: ${error}`);
      this.testResults.errorCount++;
    }
  }

  private async testPerformance(): Promise<void> {
    console.log('Testing performance...');
    
    try {
      const perfResult = await this.service.performanceTest();
      
      if (perfResult.success) {
        this.testResults.messageLatency = perfResult.latency;
        console.log(`✅ Performance test: ${perfResult.latency}ms latency, ${perfResult.messageSize} bytes`);
      } else {
        this.testResults.errors.push('Performance test failed');
        this.testResults.errorCount++;
      }
      
    } catch (error) {
      this.testResults.errors.push(`Performance test error: ${error}`);
      this.testResults.errorCount++;
    }
  }

  private async testPeerDiscovery(): Promise<void> {
    console.log('Testing peer discovery...');
    
    try {
      const peers = await this.service.discoverPeers();
      console.log(`✅ Discovered ${peers.length} peers`);
      
      if (peers.length === 0) {
        this.testResults.errors.push('No peers discovered - discovery may not be working');
        this.testResults.errorCount++;
      }
      
    } catch (error) {
      this.testResults.errors.push(`Peer discovery failed: ${error}`);
      this.testResults.errorCount++;
    }
  }

  private async measureThroughput(): Promise<number> {
    const messageCount = 100;
    const startTime = Date.now();
    
    for (let i = 0; i < messageCount; i++) {
      await this.service.broadcastMessage({
        type: 'throughput-test',
        timestamp: Date.now(),
        data: new Array(100).fill(0).map(() => Math.random())
      });
    }
    
    const endTime = Date.now();
    const duration = (endTime - startTime) / 1000; // seconds
    this.testResults.throughput = messageCount / duration;
    
    return this.testResults.throughput;
  }

  private logTestResults(): void {
    console.log('\n=== MQTT Integration Test Results ===');
    console.log(`Success: ${this.testResults.success ? '✅ PASS' : '❌ FAIL'}`);
    console.log(`Duration: ${this.testResults.duration}ms`);
    console.log(`Connection Latency: ${this.testResults.connectionLatency}ms`);
    console.log(`Message Latency: ${this.testResults.messageLatency}ms`);
    console.log(`Throughput: ${this.testResults.throughput.toFixed(2)} msg/s`);
    console.log(`Errors: ${this.testResults.errorCount}`);
    
    if (this.testResults.errors.length > 0) {
      console.log('\nErrors:');
      this.testResults.errors.forEach((error, index) => {
        console.log(`${index + 1}. ${error}`);
      });
    }
    
    console.log('\n=== Detailed Metrics ===');
    const networkStats = this.service.getNetworkStatus();
    console.log(`Connected Peers: ${networkStats.connectedPeers}`);
    console.log(`Active Canvases: ${networkStats.activeCanvases}`);
    console.log(`Messages/Second: ${networkStats.messagesPerSecond.toFixed(2)}`);
    console.log('==============================');
  }

  async generateTestReport(): Promise<string> {
    const report = {
      timestamp: new Date().toISOString(),
      configuration: this.config,
      results: this.testResults,
      networkStats: this.service.getNetworkStatus(),
      recommendations: this.generateRecommendations()
    };

    return JSON.stringify(report, null, 2);
  }

  private generateRecommendations(): string[] {
    const recommendations: string[] = [];

    if (this.testResults.connectionLatency > 1000) {
      recommendations.push('Consider optimizing broker connection or network configuration');
    }

    if (this.testResults.messageLatency > 500) {
      recommendations.push('Message latency is high - consider reducing message size or optimizing broker');
    }

    if (this.testResults.throughput < 10) {
      recommendations.push('Low throughput detected - check broker capacity and network bandwidth');
    }

    if (this.testResults.errorCount > 0) {
      recommendations.push('Address test failures before production deployment');
    }

    const networkStats = this.service.getNetworkStatus();
    if (networkStats.connectedPeers < 2) {
      recommendations.push('Consider enabling peer discovery or checking network configuration');
    }

    if (recommendations.length === 0) {
      recommendations.push('All tests passed - system ready for production');
    }

    return recommendations;
  }

  async cleanup(): Promise<void> {
    console.log('Cleaning up MQTT Integration Test...');
    await this.service.disconnect();
  }
}

// Factory function for easy testing
export function createMQTTTester(config: Partial<MQTTTestConfig> = {}): MQTTIntegrationTester {
  const defaultConfig: MQTTTestConfig = {
    brokerUrl: 'mqtt://localhost:1883',
    testRepositories: ['test-repo-1', 'test-repo-2'],
    testMessageSize: 1024, // 1KB
    testDuration: 60, // 1 minute
    ...config
  };

  return new MQTTIntegrationTester(defaultConfig);
}