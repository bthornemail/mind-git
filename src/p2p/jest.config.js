# @domain DIGITAL - Digital systems, software, compilers, algorithms
import { describe, it, expect, beforeAll, afterAll } from '@jest/globals';

// Global test setup
beforeAll(() => {
  // Set test timeout
  jest.setTimeout(30000); // 30 seconds
  
  // Mock console methods
  global.console = {
    log: jest.fn(),
    error: jest.fn(),
    warn: jest.fn(),
    info: jest.fn()
  };
});

afterAll(() => {
  // Restore console
  global.console.log.mockRestore();
  global.console.error.mockRestore();
  global.console.warn.mockRestore();
  global.console.info.mockRestore();
  
  // Clear any remaining mocks
  jest.clearAllMocks();
});

describe('MQTT P2P System - Test Configuration', () => {
  describe('Test Environment', () => {
    it('should have proper test configuration', () => {
      expect(process.env.NODE_ENV).toBe('test');
      expect(jest.getTimeout()).toBe(30000);
    });
  });

  describe('Mock Configuration', () => {
    it('should configure mocks properly', () => {
      // Verify all mocks are properly configured
      expect(jest.isMockFunction(global.console.log)).toBe(true);
      expect(jest.isMockFunction(global.console.error)).toBe(true);
      expect(jest.isMockFunction(global.console.warn)).toBe(true);
      expect(jest.isMockFunction(global.console.info)).toBe(true);
    });
  });
});