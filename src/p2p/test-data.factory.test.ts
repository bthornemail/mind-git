# @domain DIGITAL - Digital systems, software, compilers, algorithms
import { describe, it, expect } from '@jest/globals';

describe('MQTT P2P System - Test Utilities', () => {
  describe('Test Data Factory', () => {
    it('should create valid test canvases', () => {
      const canvas = createTestCanvas('basic');
      expect(canvas.id).toBe('test-canvas');
      expect(canvas.nodes).toHaveLength(3);
      expect(canvas.edges).toHaveLength(2);
      expect(canvas.metadata.author).toBe('test-author');
    });

    it('should create large test canvases', () => {
      const canvas = createTestCanvas('large');
      expect(canvas.nodes).toHaveLength(1000);
      expect(canvas.edges).toHaveLength(999);
    });

    it('should create real-time test canvases', () => {
      const canvas = createTestCanvas('realtime');
      expect(canvas.nodes).toHaveLength(10);
      expect(canvas.edges).toHaveLength(9);
    });

    it('should create performance test canvases', () => {
      const canvas = createTestCanvas('performance');
      expect(canvas.nodes).toHaveLength(100);
      expect(canvas.edges).toHaveLength(99);
    });
  });

  describe('Test Scenarios', () => {
    it('should create comprehensive test suite', () => {
      const scenarios = [
        'basic-canvas',
        'large-canvas',
        'realtime-canvas',
        'performance-canvas',
        'collaboration-canvas',
        'sync-canvas',
        'conflict-canvas',
        'edge-cases-canvas'
      ];

      scenarios.forEach(scenario => {
        const canvas = createTestCanvas(scenario);
        expect(canvas).toBeDefined();
        expect(canvas.id).toBe(`${scenario}-canvas`);
        expect(canvas.nodes.length).toBeGreaterThan(0);
        expect(canvas.edges.length).toBeGreaterThan(0);
      });
    });
  });

  describe('Performance Test Data', () => {
    it('should generate realistic test data', () => {
      const performanceData = generatePerformanceTestData();
      
      expect(performanceData).toHaveProperty('latency');
      expect(performanceData).toHaveProperty('throughput');
      expect(performanceData).toHaveProperty('memory');
      expect(performanceData).toHaveProperty('cpu');
      expect(performanceData.latency).toBeGreaterThan(0);
      expect(performanceData.throughput).toBeGreaterThan(0);
    });
  });

  describe('Network Test Data', () => {
    it('should generate realistic network conditions', () => {
      const networkData = generateNetworkTestData();
      
      expect(networkData).toHaveProperty('packetLoss');
      expect(networkData).toHaveProperty('latency');
      expect(networkData).toHaveProperty('bandwidth');
      expect(networkData.packetLoss).toBeGreaterThanOrEqual(0);
      expect(networkData.latency).toBeGreaterThan(0);
      expect(networkData.bandwidth).toBeGreaterThan(0);
    });
  });

  describe('Security Test Data', () => {
    it('should generate security test cases', () => {
      const securityData = generateSecurityTestData();
      
      expect(securityData).toHaveProperty('authentication');
      expect(securityData).toHaveProperty('encryption');
      expect(securityData).toHaveProperty('accessControl');
      expect(securityData.authentication).toHaveProperty('validCredentials');
      expect(securityData.authentication).toHaveProperty('invalidCredentials');
      expect(securityData.encryption).toHaveProperty('encryptedData');
      expect(securityData.accessControl).toHaveProperty('authorizedAccess');
      expect(securityData.accessControl).toHaveProperty('unauthorizedAccess');
    });
  });
});

// Helper functions for test data generation
function createTestCanvas(type: string) {
  const baseCanvas = {
    id: `${type}-canvas`,
    name: `${type.charAt(0).toUpperCase() + ${type.slice(1)} Canvas`,
    metadata: {
      created: Date.now(),
      author: 'test-author',
      version: '1.0.0'
    },
    nodes: [],
    edges: []
  };

  switch (type) {
    case 'basic':
      baseCanvas.nodes = [
        { id: '1', type: 'activate', x: 100, y: 100 },
        { id: '2', type: 'integrate', x: 200, y: 100 },
        { id: '3', type: 'transform', x: 300, y: 100 }
      ];
      baseCanvas.edges = [
        { from: '1', to: '2', type: 'data' }
      ];
      break;
      
    case 'large':
      baseCanvas.nodes = Array(1000).fill(null).map((_, i) => ({
        id: `node-${i}`,
        type: 'activate',
        x: Math.random() * 1000,
        y: Math.random() * 1000
      }));
      baseCanvas.edges = Array(999).fill(null).map((_, i) => ({
        from: `node-${i}`,
        to: `node-${i + 1}`,
        type: 'data'
      }));
      break;
      
    case 'realtime':
      baseCanvas.nodes = Array(10).fill(null).map((_, i) => ({
        id: `rt-node-${i}`,
        type: 'activate',
        x: i * 100,
        y: i * 100,
        lastUpdate: Date.now() - (i * 1000)
      }));
      baseCanvas.edges = Array(9).fill(null).map((_, i) => ({
        from: `rt-node-${i}`,
        to: `rt-node-${i + 1}`,
        type: 'data',
        timestamp: Date.now() - (9 - i) * 1000
      }));
      break;
      
    case 'performance':
      baseCanvas.nodes = Array(100).fill(null).map((_, i) => ({
        id: `perf-node-${i}`,
        type: 'transform',
        x: i * 50,
        y: i * 50,
        metadata: { operations: i * 1000 }
      }));
      baseCanvas.edges = Array(99).fill(null).map((_, i) => ({
        from: `perf-node-${i}`,
        to: `perf-node-${i + 1}`,
        type: 'data',
        performance: { latency: Math.random() * 100, throughput: Math.random() * 1000 }
      }));
      break;
      
    default:
      return baseCanvas;
  }
}

function generatePerformanceTestData() {
  return {
    latency: {
      min: 10,
      max: 500,
      average: 100,
      p95: 200,
      p99: 300
    },
    throughput: {
      min: 100,
      max: 10000,
      average: 1000,
      p95: 5000,
      p99: 8000
    },
    memory: {
      min: 10 * 1024 * 1024,
      max: 100 * 1024 * 1024,
      average: 50 * 1024 * 1024,
      p95: 80 * 1024 * 1024,
      p99: 95 * 1024 * 1024
    },
    cpu: {
      min: 5,
      max: 80,
      average: 25,
      p95: 60,
      p99: 75
    }
  };
}

function generateNetworkTestData() {
  return {
    packetLoss: {
      min: 0,
      max: 0.1,
      average: 0.01,
      p95: 0.05,
      p99: 0.1
    },
    latency: {
      min: 5,
      max: 200,
      average: 50,
      p95: 150,
      p99: 200
    },
    bandwidth: {
      min: 1,
      max: 1000,
      average: 100,
      p95: 500,
      p99: 800
    }
  };
}

function generateSecurityTestData() {
  return {
    authentication: {
      validCredentials: {
        username: 'test-user',
        password: 'test-password',
        clientId: 'test-client'
      },
      invalidCredentials: {
        username: '',
        password: 'test-password',
        clientId: 'test-client'
      },
      weakPassword: {
        username: 'test-user',
        password: '123456',
        clientId: 'test-client'
      },
      correctPassword: {
        username: 'test-user',
        password: 'correct-password',
        clientId: 'test-client'
      }
    },
    encryption: {
      plainData: {
        apiKey: 'secret-api-key',
        canvasContent: 'confidential user data'
      },
      encryptedData: {
        apiKey: 'encrypted-api-key',
        canvasContent: 'encrypted confidential user data',
        iv: 'mock-iv',
        authTag: 'mock-tag'
      }
    },
    accessControl: {
      authorizedAccess: {
        clientId: 'authorized-client',
        topics: ['mind-git/canvas'],
        permissions: ['read', 'write']
      },
      unauthorizedAccess: {
        clientId: 'unauthorized-client',
        topics: ['admin/'],
        permissions: ['read', 'write']
      }
    }
  };
}