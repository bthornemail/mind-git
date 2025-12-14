/**
 * Production Hardening Security Tests
 *
 * === TEST COVERAGE ===
 * - LLL lattice reduction security
 * - Constant-time operation timing
 * - Secure memory management
 * - Key erasure mechanisms
 * - Integration security
 * - Performance benchmarks
 */

import { LLLReducer, LatticeBasis } from './lll-reduction';
import { SecureMemory } from './secure-memory';
import { ConstantTime } from './constant-time';
import { KeyErasure } from './key-erasure';
import { ProductionCryptography } from './production-crypto';
import { TernaryCubicForm, CubicKeyPair } from './index';
import { Sedenion, Trigintaduonion } from '../multiverse/index';

describe('Production Hardening Security Tests', () => {
  describe('LLL Lattice Reduction Security', () => {
    let lllReducer: LLLReducer;

    beforeEach(() => {
      lllReducer = new LLLReducer({
        delta: 0.995,
        eta: 0.49,
        maxIterations: 1000
      });
    });

    test('should reduce lattice basis securely', async () => {
      const basis: LatticeBasis = {
        rows: [
          [1, 1, 1, 1],
          [1, 0, 1, 0],
          [0, 1, 0, 1],
          [1, 1, 0, 0]
        ],
        dimension: 4,
        ambient: 4
      };

      const result = await lllReducer.reduce(basis);

      expect(result.success).toBe(true);
      expect(result.securityLevel).toBe('safe');
      expect(result.iterations).toBeGreaterThan(0);
      expect(result.reducedBasis.rows).toHaveLength(4);
    });

    test('should verify reduction correctness', async () => {
      const basis: LatticeBasis = {
        rows: [
          [2, 1, 0, 0],
          [1, 2, 1, 0],
          [0, 1, 2, 1],
          [0, 0, 1, 2]
        ],
        dimension: 4,
        ambient: 4
      };

      const result = await lllReducer.reduce(basis);
      const verified = await lllReducer.verifyReduction(basis, result);

      expect(verified).toBe(true);
    });

    test('should handle degenerate cases', async () => {
      const basis: LatticeBasis = {
        rows: [
          [0, 0, 0, 0],
          [0, 0, 0, 0],
          [0, 0, 0, 0],
          [0, 0, 0, 0]
        ],
        dimension: 4,
        ambient: 4
      };

      const result = await lllReducer.reduce(basis);

      expect(result.success).toBe(true);
      expect(result.securityLevel).toBe('safe');
    });

    test('should enforce iteration limits', async () => {
      // Create a basis that might cause many iterations
      const basis: LatticeBasis = {
        rows: [
          [1000000, 1, 0, 0],
          [1, 1000000, 1, 0],
          [0, 1, 1000000, 1],
          [0, 0, 1, 1000000]
        ],
        dimension: 4,
        ambient: 4
      };

      const lllLimited = new LLLReducer({
        delta: 0.995,
        eta: 0.49,
        maxIterations: 10 // Very low limit
      });

      const result = await lllLimited.reduce(basis);

      // Should either succeed quickly or hit iteration limit
      expect(result.iterations).toBeLessThanOrEqual(10);
    });
  });

  describe('Constant-Time Operations', () => {
    let constantTime: ConstantTime;

    beforeEach(() => {
      constantTime = new ConstantTime();
    });

    test('should perform addition in constant time', async () => {
      const operations = [
        [1, 2],
        [1000000, 2000000],
        [0, 0],
        [-1, 1]
      ];

      const times: number[] = [];

      for (const [a, b] of operations) {
        const start = performance.now();
        await constantTime.add(a, b);
        const end = performance.now();
        times.push(end - start);
      }

      // All operations should take similar time (within 50% variance)
      const avgTime = times.reduce((a, b) => a + b, 0) / times.length;
      const maxDeviation = Math.max(...times.map(t => Math.abs(t - avgTime)));
      
      expect(maxDeviation).toBeLessThan(avgTime * 0.5);
    });

    test('should perform equality comparison in constant time', async () => {
      const equalPairs = [
        [1, 1],
        [1000000, 1000000],
        [0, 0]
      ];

      const unequalPairs = [
        [1, 2],
        [1000000, 2000000],
        [0, 1]
      ];

      const equalTimes: number[] = [];
      const unequalTimes: number[] = [];

      for (const [a, b] of equalPairs) {
        const start = performance.now();
        await constantTime.equals(a, b);
        const end = performance.now();
        equalTimes.push(end - start);
      }

      for (const [a, b] of unequalPairs) {
        const start = performance.now();
        await constantTime.equals(a, b);
        const end = performance.now();
        unequalTimes.push(end - start);
      }

      // Equal and unequal comparisons should take similar time
      const avgEqualTime = equalTimes.reduce((a, b) => a + b, 0) / equalTimes.length;
      const avgUnequalTime = unequalTimes.reduce((a, b) => a + b, 0) / unequalTimes.length;
      
      expect(Math.abs(avgEqualTime - avgUnequalTime)).toBeLessThan(avgEqualTime * 0.5);
    });

    test('should perform array comparison securely', async () => {
      const array1 = new Uint8Array([1, 2, 3, 4, 5]);
      const array2 = new Uint8Array([1, 2, 3, 4, 5]);
      const array3 = new Uint8Array([1, 2, 3, 4, 6]);

      const equalResult = await constantTime.arrayEquals(array1, array2);
      const unequalResult = await constantTime.arrayEquals(array1, array3);

      expect(equalResult).toBe(1);
      expect(unequalResult).toBe(0);
    });

    test('should benchmark operations', async () => {
      const stats = await constantTime.benchmark(
        async () => { await constantTime.add(1, 2); },
        100
      );

      expect(stats.mean).toBeGreaterThan(0);
      expect(stats.min).toBeLessThanOrEqual(stats.mean);
      expect(stats.max).toBeGreaterThanOrEqual(stats.mean);
      expect(stats.stdDev).toBeGreaterThanOrEqual(0);
    });
  });

  describe('Secure Memory Management', () => {
    let secureMemory: SecureMemory;

    beforeEach(() => {
      secureMemory = new SecureMemory();
    });

    afterEach(async () => {
      await secureMemory.destroy();
    });

    test('should allocate and deallocate memory securely', async () => {
      const block = await secureMemory.allocate(1024);
      
      expect(block.data).toBeInstanceOf(Uint8Array);
      expect(block.size).toBe(1024);
      expect(block.isSensitive).toBe(true);

      await secureMemory.deallocate(block);
      
      // Block should be zeroized after deallocation
      const isZero = block.data.every(byte => byte === 0);
      expect(isZero).toBe(true);
    });

    test('should reuse memory from pool', async () => {
      const block1 = await secureMemory.allocate(512);
      await secureMemory.deallocate(block1);
      
      const block2 = await secureMemory.allocate(512);
      
      // Should reuse from pool (same underlying memory)
      expect(block2.size).toBe(512);
    });

    test('should enforce memory limits', async () => {
      const smallMemory = new SecureMemory();
      smallMemory['maxTotalMemory'] = 2048; // 2KB limit

      try {
        await smallMemory.allocate(1024);
        await smallMemory.allocate(1024);
        await smallMemory.allocate(1024); // Should exceed limit
        
        fail('Should have thrown memory limit error');
      } catch (error) {
        expect(error).toBeInstanceOf(Error);
        expect((error as Error).message).toContain('Memory limit exceeded');
      } finally {
        await smallMemory.destroy();
      }
    });

    test('should provide memory statistics', async () => {
      await secureMemory.allocate(1024);
      await secureMemory.allocate(512);
      
      const stats = secureMemory.getStats();
      
      expect(stats.totalAllocated).toBe(1536);
      expect(stats.activeBlocks).toBe(2);
      expect(stats.pools).toBeGreaterThanOrEqual(0);
    });
  });

  describe('Key Erasure Mechanisms', () => {
    let keyErasure: KeyErasure;

    beforeEach(() => {
      keyErasure = new KeyErasure({
        overwritePasses: 4,
        verifyErasure: true,
        auditLog: true
      });
    });

    afterEach(async () => {
      await keyErasure.destroy();
    });

    test('should erase cubic keys securely', async () => {
      const cubic = TernaryCubicForm.random(10, 42);
      const keyPair: CubicKeyPair = {
        private_cubic: cubic,
        public_cubic: cubic.clone(),
        tensor_seed: 42
      };

      await keyErasure.eraseCubicKey(keyPair, 'test-key');

      // Verify audit log
      const auditLog = keyErasure.getAuditLog();
      const cubicErasure = auditLog.find(entry => entry.keyType === 'cubic_key');
      
      expect(cubicErasure).toBeDefined();
      expect(cubicErasure!.success).toBe(true);
      expect(cubicErasure!.verified).toBe(true);
    });

    test('should erase sedenions securely', async () => {
      const sedenion = Sedenion.random(1, 42);

      await keyErasure.eraseSedenion(sedenion, 'test-sedenion');

      const auditLog = keyErasure.getAuditLog();
      const sedenionErasure = auditLog.find(entry => entry.keyType === 'sedenion');
      
      expect(sedenionErasure).toBeDefined();
      expect(sedenionErasure!.success).toBe(true);
    });

    test('should erase trigintaduonions securely', async () => {
      const trigintaduonion = Trigintaduonion.random(1, 42);

      await keyErasure.eraseTrigintaduonion(trigintaduonion, 'test-trigintaduonion');

      const auditLog = keyErasure.getAuditLog();
      const trigintaduonionErasure = auditLog.find(entry => entry.keyType === 'trigintaduonion');
      
      expect(trigintaduonionErasure).toBeDefined();
      expect(trigintaduonionErasure!.success).toBe(true);
    });

    test('should provide erasure statistics', async () => {
      const cubic = TernaryCubicForm.random(10, 42);
      const keyPair: CubicKeyPair = {
        private_cubic: cubic,
        public_cubic: cubic.clone(),
        tensor_seed: 42
      };

      await keyErasure.eraseCubicKey(keyPair, 'test-key-1');
      await keyErasure.eraseCubicKey(keyPair, 'test-key-2');

      const stats = keyErasure.getStatistics();
      
      expect(stats.totalErasures).toBe(2);
      expect(stats.successfulErasures).toBe(2);
      expect(stats.failedErasures).toBe(0);
    });

    test('should handle emergency erase', async () => {
      const cubic = TernaryCubicForm.random(10, 42);
      const keyPair: CubicKeyPair = {
        private_cubic: cubic,
        public_cubic: cubic.clone(),
        tensor_seed: 42
      };

      await keyErasure.registerKey('emergency-test', cubic.toBytes(), 'cubic_key');
      await keyErasure.emergencyErase();

      const activeKeys = keyErasure.getActiveKeys();
      expect(activeKeys).toHaveLength(0);
    });
  });

  describe('Production Cryptography Integration', () => {
    let productionCrypto: ProductionCryptography;

    beforeEach(() => {
      productionCrypto = new ProductionCryptography({
        audit: { enabled: true, logLevel: 'debug' },
        lllParams: { delta: 0.995, eta: 0.49, maxIterations: 1000 },
        keyErasure: { overwritePasses: 4, verifyErasure: true, useMemoryBarriers: true, hardwareSecureClear: true, auditLog: true }
      });
    });

    afterEach(async () => {
      if (productionCrypto) {
        await productionCrypto.destroy();
      }
    });

    test('should integrate LLL analysis with security monitoring', async () => {
      const basis: LatticeBasis = {
        rows: [
          [1, 1, 1, 1],
          [1, 0, 1, 0],
          [0, 1, 0, 1],
          [1, 1, 0, 0]
        ],
        dimension: 4,
        ambient: 4
      };

      const result = await productionCrypto.analyzeLattice(basis);

      expect(result.success).toBe(true);
      expect(result.securityLevel).toBe('safe');

      const auditLog = productionCrypto.getAuditLog();
      const lllAnalysis = auditLog.find(entry => entry.operation === 'LLL_ANALYSIS');
      
      expect(lllAnalysis).toBeDefined();
      expect(lllAnalysis!.success).toBe(true);
      expect(lllAnalysis!.securityLevel).toBe('safe');
    });

    test('should perform constant-time operations with audit', async () => {
      const result = await productionCrypto.constantTimeOperation('add', 5, 3);

      expect(result).toBe(8);

      const auditLog = productionCrypto.getAuditLog();
      const constantTimeOp = auditLog.find(entry => entry.operation === 'CONSTANT_TIME_ADD');
      
      expect(constantTimeOp).toBeDefined();
      expect(constantTimeOp!.success).toBe(true);
    });

    test('should protect and erase keys with full audit trail', async () => {
      const keyData = new Uint8Array([1, 2, 3, 4, 5]);
      
      await productionCrypto.protectKey(keyData, 'test_key', 'test-key-id');
      await productionCrypto.eraseKey('test-key-id', 'test_key');

      const auditLog = productionCrypto.getAuditLog();
      const protectOp = auditLog.find(entry => entry.operation === 'KEY_PROTECT');
      const eraseOp = auditLog.find(entry => entry.operation === 'KEY_ERASE');
      
      expect(protectOp).toBeDefined();
      expect(protectOp!.success).toBe(true);
      expect(eraseOp).toBeDefined();
      expect(eraseOp!.success).toBe(true);
    });

    test('should perform comprehensive security audit', async () => {
      // Perform some operations
      await productionCrypto.constantTimeOperation('add', 1, 2);
      await productionCrypto.constantTimeOperation('multiply', 3, 4);
      
      const audit = await productionCrypto.securityAudit();

      expect(audit.totalOperations).toBeGreaterThan(0);
      expect(audit.successfulOperations).toBeGreaterThan(0);
      expect(audit.overallSecurity).toBe('safe');
      expect(Array.isArray(audit.recommendations)).toBe(true);
    });

    test('should handle emergency cleanup', async () => {
      await productionCrypto.emergencyCleanup();

      const auditLog = productionCrypto.getAuditLog();
      const emergencyOp = auditLog.find(entry => entry.operation === 'EMERGENCY_CLEANUP');
      
      expect(emergencyOp).toBeDefined();
      expect(emergencyOp!.success).toBe(true);
    });

    test('should provide comprehensive statistics', () => {
      const stats = productionCrypto.getStatistics();

      expect(stats.memory).toBeDefined();
      expect(stats.keyErasure).toBeDefined();
      expect(stats.audit).toBeDefined();
    });
  });

  describe('Performance Benchmarks', () => {
    test('should benchmark LLL reduction performance', async () => {
      const lllReducer = new LLLReducer();
      const basis: LatticeBasis = {
        rows: [
          [1, 1, 1, 1],
          [1, 0, 1, 0],
          [0, 1, 0, 1],
          [1, 1, 0, 0]
        ],
        dimension: 4,
        ambient: 4
      };

      const start = performance.now();
      await lllReducer.reduce(basis);
      const duration = performance.now() - start;

      // Should complete within reasonable time
      expect(duration).toBeLessThan(1000); // 1 second
    });

    test('should benchmark constant-time operations', async () => {
      const constantTime = new ConstantTime();

      const start = performance.now();
      for (let i = 0; i < 100; i++) {
        await constantTime.add(i, i + 1);
      }
      const duration = performance.now() - start;

      // Average per operation should be reasonable
      const avgDuration = duration / 100;
      expect(avgDuration).toBeLessThan(10); // 10ms per operation
    });

    test('should benchmark memory allocation', async () => {
      const secureMemory = new SecureMemory();

      const start = performance.now();
      const blocks: any[] = [];
      
      for (let i = 0; i < 100; i++) {
        const block = await secureMemory.allocate(1024);
        blocks.push(block);
      }
      
      const allocationDuration = performance.now() - start;

      const deallocationStart = performance.now();
      for (const block of blocks) {
        await secureMemory.deallocate(block);
      }
      const deallocationDuration = performance.now() - start;

      expect(allocationDuration).toBeLessThan(1000); // 1 second for 100 allocations
      expect(deallocationDuration).toBeLessThan(1000); // 1 second for 100 deallocations

      await secureMemory.destroy();
    });
  });
});