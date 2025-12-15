#!/usr/bin/env node

// Simple MQTT P2P Demo - Showcasing Real-time Collaboration
import { createP2PNetwork } from './dist/network-manager.js';
import { DEFAULT_MQTT_CONFIG } from './dist/mqtt-broker.js';

console.log('🚀 Starting Simple MQTT P2P Demo...');

async function runSimpleDemo() {
  try {
    // Create P2P Network for Repository 1
    console.log('📡 Setting up Repository 1...');
    const repo1 = createP2PNetwork({
      broker: 'localhost',
      port: 1883,
      repositories: ['demo-repo-1'],
      enableDiscovery: true,
      syncInterval: 10
    });

    // Create P2P Network for Repository 2  
    console.log('📡 Setting up Repository 2...');
    const repo2 = createP2PNetwork({
      broker: 'localhost',
      port: 1883,
      repositories: ['demo-repo-2'],
      enableDiscovery: true,
      syncInterval: 10
    });

    // Initialize both networks
    await Promise.all([
      repo1.initialize(),
      repo2.initialize()
    ]);

    console.log('✅ Both repositories initialized successfully!');

    // Wait for peer discovery
    console.log('🔍 Waiting for peer discovery...');
    await new Promise(resolve => setTimeout(resolve, 3000));

    // Get network statistics
    const stats1 = repo1.getNetworkStats();
    const stats2 = repo2.getNetworkStats();

    console.log('📊 Network Statistics:');
    console.log(`Repository 1 - Peers: ${stats1.connectedPeers}, Canvases: ${stats1.activeCanvases}`);
    console.log(`Repository 2 - Peers: ${stats2.connectedPeers}, Canvases: ${stats2.activeCanvases}`);

    // Test message broadcasting
    console.log('📢 Testing broadcast message...');
    await repo1.broadcastMessage({
      type: 'demo-message',
      content: 'Hello from Repository 1!',
      timestamp: Date.now()
    });

    // Wait for message propagation
    await new Promise(resolve => setTimeout(resolve, 1000));

    // Test repository sync
    console.log('🔄 Testing repository synchronization...');
    await repo1.syncRepository('demo-repo-1');
    await repo2.syncRepository('demo-repo-2');

    // Final statistics
    const finalStats1 = repo1.getNetworkStats();
    const finalStats2 = repo2.getNetworkStats();

    console.log('📈 Final Network Statistics:');
    console.log(`Repository 1 - Peers: ${finalStats1.connectedPeers}, Messages: ${finalStats1.totalMessages}`);
    console.log(`Repository 2 - Peers: ${finalStats2.connectedPeers}, Messages: ${finalStats2.totalMessages}`);

    console.log('🎉 Demo completed successfully!');

    // Cleanup
    await Promise.all([
      repo1.disconnect(),
      repo2.disconnect()
    ]);

    console.log('✅ Cleanup completed');

  } catch (error) {
    console.error('❌ Demo failed:', error);
    process.exit(1);
  }
}

// Run the demo
runSimpleDemo();