# @domain DIGITAL - Digital systems, software, compilers, algorithms
import { describe, it, expect } from '@jest/globals';

// Global test configuration
global.testTimeout = 60000; // 60 seconds
global.testEnvironment = 'test';

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
  'validation.test.ts'
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

// Run all test suites
async function runAllTestSuites(): Promise<void> {
  console.log('Running all test suites...');
  
  let totalTests = 0;
  let totalPassed = 0;
  let totalFailed = 0;

  for (const testSuite of testSuites) {
    const result = await runTestSuite(testSuite);
    totalTests += result.total;
    totalPassed += result.passed;
    totalFailed += result.failed;
  }

  console.log(`All test suites completed:`);
  console.log(`Total tests: ${totalTests}`);
  console.log(`Total passed: ${totalPassed}`);
  console.log(`Total failed: ${totalFailed}`);
  console.log(`Success rate: ${((totalPassed / totalTests) * 100).toFixed(2)}%`);
}

// Main test execution
if (process.env.NODE_ENV === 'test') {
  runAllTestSuites().catch(console.error);
} else {
  console.log('Skipping tests - NODE_ENV is not set to "test"');
}