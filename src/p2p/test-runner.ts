import { describe, it, expect } from '@jest/globals';

// Global test configuration
(global as any).testTimeout = 60000; // 60 seconds
(global as any).testEnvironment = 'test';

// Test suites
const testSuites = [
  'unit.test.ts',
  'integration.test.ts',
  'mock-environment.test.ts',
  'test-data.factory.test.ts',
  'test-runner.test.ts',
  'performance.test.ts',
  'error-handling.test.ts',
  'documentation.test.ts',
  'production-readiness.test.ts',
  'full-integration.test.ts',
  'validation.test.ts',
  'test-execution.test.ts'
];

// Test runner
async function runTestSuite(testSuite: string): Promise<any> {
  console.log(`Running ${testSuite}...`);
  try {
    const { runTests } = require(`./${testSuite}`);
    const result = await runTests();
    
    console.log(`${testSuite}: ${result.passed}/${result.total} tests passed`);
    
    if (result.failed > 0) {
      console.log(`${result.failed} tests failed`);
    }
    
    return result;
  } catch (error) {
    console.error(`Error running ${testSuite}:`, error);
    throw error;
  }
}

// Main test execution
if (process.env.NODE_ENV === 'test') {
  runTestSuite('all').catch(console.error);
} else {
  console.log('Skipping tests - NODE_ENV is not set to "test"');
}