import { program } from 'commander';
import { createMQTTDemo } from './mqtt-demo.js';
import { createMQTTTester } from './mqtt-tester.js';
import { createP2PNetwork } from './network-manager.js';
import { MQTTIntegrationService } from './mqtt-integration.js';

// @domain ORGANIZATIONAL - Project role and responsibilities
program
  .name('mqtt-p2p')
  .description('MQTT P2P Canvas System')
  .version('1.0.0')
  .command('demo')
  .option('--broker <url>', 'MQTT broker URL')
  .option('--repositories <list>', 'Comma-separated repository list')
  .option('--duration <minutes>', 'Demo duration in minutes')
  .action(async (options) => {
    console.log('🎭 Starting MQTT P2P Demo...');
    
    try {
      const demo = createMQTTDemo({
        brokerUrl: options.broker || 'mqtt://localhost:1883',
        repositories: options.repositories ? options.repositories.split(',') : ['demo-repo-1', 'demo-repo-2'],
        duration: parseInt(options.duration) || 10
      });

      const result = await demo.runDemo();
      
      if (result.success) {
        console.log('✅ Demo completed successfully!');
        console.log(`📊 Performance: ${result.performance.avgLatency}ms latency, ${result.performance.throughput} msg/s`);
        console.log(`🤝 Collaboration: ${result.collaboration.realTimeSessions} sessions, ${result.collaboration.sharedCanvases} shared canvases`);
      } else {
        console.log('❌ Demo failed');
        console.log(`🚨 Errors: ${result.errors.length}`);
        result.errors.forEach((error, index) => {
          console.log(`   ${index + 1}. ${error}`);
        });
      }
      
    } catch (error) {
      console.error('❌ Demo error:', error instanceof Error ? error.message : String(error));
      process.exit(1);
    }
  });

program
  .command('test')
  .description('Run MQTT integration tests')
  .option('--broker <url>', 'MQTT broker URL')
  .option('--repositories <list>', 'Test repositories')
  .option('--duration <minutes>', 'Test duration')
  .action(async (options) => {
    console.log('🧪 Running MQTT Integration Tests...');
    
    try {
      const tester = createMQTTTester({
        brokerUrl: options.broker || 'mqtt://localhost:1883',
        testRepositories: options.repositories ? options.repositories.split(',') : ['test-repo-1', 'test-repo-2'],
        testMessageSize: 1024,
        testDuration: parseInt(options.duration) || 5
      });

      const result = await tester.runFullTest();
      
      if (result.success) {
        console.log('✅ All tests passed!');
        console.log(`📈 Connection: ${result.connectionLatency}ms`);
        console.log(`📈 Message Latency: ${result.messageLatency}ms`);
        console.log(`📈 Throughput: ${result.throughput} msg/s`);
      } else {
        console.log('❌ Tests failed');
        console.log(`🚨 Errors: ${result.errors.length}`);
        result.errors.forEach((error, index) => {
          console.log(`   ${index + 1}. ${error}`);
        });
      }
      
    } catch (error) {
      console.error('❌ Test error:', error instanceof Error ? error.message : String(error));
      process.exit(1);
    }
  });

program
  .command('server')
  .description('Start MQTT broker server')
  .option('--repositories <list>', 'Repository list')
  .action(async (options) => {
    console.log('🖥 Starting MQTT Broker Server...');
    
    try {
      const network = createP2PNetwork({
        broker: 'localhost',
        port: 1883,
        repositories: options.repositories ? options.repositories.split(',') : ['default-repo'],
        enableDiscovery: true,
        syncInterval: 30
      });

      await network.initialize();
      
      console.log('✅ MQTT Broker started!');
      console.log(`📡 Listening on: localhost:1883`);
      console.log(`📁 Repositories: ${options.repositories || 'default-repo'}`);
      
      // Keep server running
      process.on('SIGINT', async () => {
        console.log('\n🛑 Shutting down MQTT Broker...');
        await network.disconnect();
        process.exit(0);
      });
      
    } catch (error) {
      console.error('❌ Server error:', error instanceof Error ? error.message : String(error));
      process.exit(1);
    }
  });

program
  .command('client')
  .description('Start MQTT client demonstration')
  .option('--repositories <list>', 'Repository list')
  .action(async (options) => {
    console.log('📱 Starting MQTT Client Demo...');
    
    try {
      const client = new MQTTIntegrationService({
        broker: {
          host: 'localhost',
          port: 1883
        },
        repositories: options.repositories ? options.repositories.split(',') : ['demo-repo'],
        features: {
          realTimeCollaboration: true,
          autoSync: true,
          discovery: true,
          encryption: false
        },
        performance: {
          maxMessageSize: 1024 * 1024, // 1MB
          maxConnections: 100,
          heartbeatInterval: 30
        }
      });

      await client.initialize();
      
      console.log('✅ MQTT Client connected!');
      console.log(`📡 Connected to: localhost:1883`);
      console.log(`📁 Repositories: ${options.repositories || 'demo-repo'}`);
      
      // Demonstrate client operations
      await client.createCanvas(
        options.repositories?.[0] || 'demo-repo', 
        'client-demo-canvas', 
        { nodes: [], edges: [] }, 
        'mqtt-client'
      );
      
      await client.updateCanvas(
        options.repositories?.[0] || 'demo-repo', 
        'client-demo-canvas', 
        { nodes: [{ id: '1' }] }, 
        'mqtt-client'
      );
      
      await client.shareCanvas(
        options.repositories?.[0] || 'demo-repo', 
        'client-demo-canvas'
      );
      
      await client.syncCanvas(
        options.repositories?.[0] || 'demo-repo', 
        'client-demo-canvas'
      );
      
      console.log('✅ Client operations completed');
      
      await client.disconnect();
      
    } catch (error) {
      console.error('❌ Client error:', error instanceof Error ? error.message : String(error));
      process.exit(1);
    }
  });

program
  .command('health')
  .description('Check MQTT system health')
  .option('--broker <url>', 'MQTT broker URL')
  .action(async (options) => {
    console.log('🏥 Checking MQTT System Health...');
    
    try {
      const integration = new MQTTIntegrationService({
        broker: {
          host: new URL(options.broker || 'mqtt://localhost:1883').hostname || 'localhost',
          port: parseInt(new URL(options.broker || 'mqtt://localhost:1883').port) || 1883
        },
        repositories: ['health-check-repo'],
        features: {
          realTimeCollaboration: true,
          autoSync: true,
          discovery: true,
          encryption: false
        },
        performance: {
          maxMessageSize: 1024 * 1024, // 1MB
          maxConnections: 100,
          heartbeatInterval: 30
        }
      });

      await integration.initialize();
      
      const health = await integration.healthCheck();
      
      if (health.healthy) {
        console.log('✅ System is healthy');
        console.log(`📊 Connected Peers: ${health.connectedPeers}`);
        console.log(`📊 Active Canvases: ${health.activeCanvases}`);
      } else {
        console.log('❌ System has issues');
        console.log(`🚨 Health Problems: ${health.issues.length}`);
        health.issues.forEach((issue, index) => {
          console.log(`   ${index + 1}. ${issue}`);
        });
      }
      
      await integration.disconnect();
      
    } catch (error) {
      console.error('❌ Health check error:', error instanceof Error ? error.message : String(error));
      process.exit(1);
    }
  });

program
  .command('monitor')
  .description('Monitor MQTT system performance')
  .option('--broker <url>', 'MQTT broker URL')
  .option('--interval <seconds>', 'Monitoring interval')
  .action(async (options) => {
    console.log('📊 Starting MQTT System Monitor...');
    
    try {
      const integration = new MQTTIntegrationService({
        broker: {
          host: new URL(options.broker || 'mqtt://localhost:1883').hostname || 'localhost',
          port: parseInt(new URL(options.broker || 'mqtt://localhost:1883').port) || 1883
        },
        repositories: ['monitor-repo'],
        features: {
          realTimeCollaboration: true,
          autoSync: true,
          discovery: true,
          encryption: false
        },
        performance: {
          maxMessageSize: 1024 * 1024, // 1MB
          maxConnections: 100,
          heartbeatInterval: 30
        }
      });

      await integration.initialize();
      
      const interval = parseInt(options.interval) || 10;
      
      console.log(`📈 Monitoring every ${interval} seconds...`);
      console.log('Press Ctrl+C to stop');
      
      const monitor = setInterval(async () => {
        const stats = integration.getNetworkStatus();
        const timestamp = new Date().toISOString();
        
        console.clear();
        console.log(`📊 MQTT System Status - ${timestamp}`);
        console.log('=====================================');
        console.log(`📡 Connected Peers: ${stats.connectedPeers}`);
        console.log(`📁 Active Canvases: ${stats.activeCanvases}`);
        console.log(`📈 Messages/Second: ${stats.messagesPerSecond.toFixed(2)}`);
        console.log(`⏱️ Uptime: ${Math.floor(stats.uptime / 1000)}s`);
        
      }, interval * 1000);
      
      process.on('SIGINT', async () => {
        console.log('\n🛑 Stopping monitor...');
        clearInterval(monitor);
        await integration.disconnect();
        process.exit(0);
      });
      
    } catch (error) {
      console.error('❌ Monitor error:', error instanceof Error ? error.message : String(error));
      process.exit(1);
    }
  });

program.parse();