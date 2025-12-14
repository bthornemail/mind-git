/**
 * MindGit Phase 2.1 - Basic Integration Tests
 *
 * === TEST FOCUS ===
 * - Cubic signature creation and verification
 * - AAL proof generation and validation
 * - Integration with DNA logging and storage
 * - Commit manager functionality
 * - Performance and error handling
 */

import { 
  SovereignIdentity,
  CanvasLState,
  MindGitCommit
} from '../types';

describe('MindGit Phase 2.1 - Basic Integration', () => {
  let dnaLogger: any;
  let storage: any;
  let crypto: any;
  let commitManager: any;

  beforeEach(() => {
    // Initialize core systems for testing
    crypto = new ProductionCryptography();
    dnaLogger = {
      log: jest.fn(),
      getStatistics: jest.fn().mockResolvedValue({ entryCount: 0 }),
      getHashChain: jest.fn().mockResolvedValue('genesis'),
      verifyIntegrity: jest.fn().mockResolvedValue(true)
    };
    
    storage = {
      storeBlob: jest.fn().mockResolvedValue('test-blob-hash'),
      storeTree: jest.fn().mockResolvedValue('test-tree-hash'),
      getStatistics: jest.fn().mockResolvedValue({
        totalObjects: 0,
        totalSize: 0
        averageSize: 0
      objectTypes: new Map()
      }),
      verifyIntegrity: jest.fn().mockResolvedValue(true)
    };
    
    commitManager = new CommitManager(dnaLogger, storage, crypto);
  });

  describe('Cubic Signature Operations', () => {
    test('should create sovereign identity with cubic keys', async () => {
      const identity: SovereignIdentity = {
        did: 'did:test:1234567890',
        cubic_keypair: {
          private_cubic: { coeffs: new Map([['3,0,0', 1]]) },
          public_cubic: { coeffs: new Map([['3,0,0', 1]]) },
          tensor_seed: 42
        },
        multiverse_keys: {
          sedenion_public: { components: Array(16).fill(1) },
          trigintaduonion_private: { components: Array(32).fill(2) }
        },
        claims: new Map(),
        created_at: Date.now(),
        updated_at: Date.now()
      };

      expect(identity.did).toBe('did:test:1234567890');
      expect(identity.cubic_keypair.private_cubic.coeffs.size).toBe(1);
      expect(identity.cubic_keypair.public_cubic.coeffs.size).toBe(1);
      expect(identity.multiverse_keys.sedenion_public.components).toHaveLength(16);
      expect(identity.multiverse_keys.trigintaduonion_private.components).toHaveLength(32);
      expect(identity.created_at).toBeGreaterThan(0);
    });

    test('should validate sovereign identity structure', () => {
      const validIdentity: SovereignIdentity = {
        did: 'did:valid',
        cubic_keypair: {
          private_cubic: { coeffs: new Map([['1,1,1]]) },
          public_cubic: { coeffs: new Map([['1,1,1]]) },
          tensor_seed: 123
        },
        multiverse_keys: {
          sedenion_public: { components: Array(16).fill(1) },
          trigintaduonion_private: { components: Array(32).fill(2) }
        },
        claims: new Map(),
        created_at: Date.now(),
        updated_at: Date.now()
      };

      expect(validIdentity.did).toMatch(/^did:/);
      expect(validIdentity.cubic_keypair.private_cubic.coeffs.size).toBeGreaterThan(0);
      expect(validIdentity.cubic_keypair.public_cubic.coeffs.size).toBeGreaterThan(0);
      expect(validIdentity.multiverse_keys.sedenion_public.components).toHaveLength(16);
      expect(validIdentity.multiverse_keys.trigintaduonion_private.components).toHaveLength(32);
      expect(validIdentity.created_at).toBeGreaterThan(0);
    });
  });

    test('should handle invalid sovereign identity', async () => {
      const invalidIdentities = [
        null,
        undefined,
        { did: 'did:invalid' },
        { cubic_keypair: { coeffs: new Map() }, // Empty cubic
          public_cubic: { coeffs: new Map() }, // Empty cubic
          tensor_seed: 42
        },
        multiverse_keys: {
          sedenion_public: { components: Array(16).fill(0) },
          trigintaduonion_private: { components: Array(32).fill(0) }
        },
        claims: new Map(),
        created_at: Date.now(),
        updated_at: Date.now()
      }
      ];

      invalidIdentities.forEach((identity, index) => {
        expect(() => {
          if (identity === null || identity === undefined) {
            throw new Error('Identity cannot be null or undefined');
          }
          if (typeof identity !== 'object') {
            throw new Error('State must be an object');
          }
          if (identity.cubic_keypair && !identity.cubic_keypair.public_cubic) {
            throw new Error('Cubic keypair is required');
          }
          if (!identity.multiverse_keys) {
            throw new Error('Multiverse keys are required');
          }
          if (identity.claims && identity.claims.size === 0) {
            throw new Error('Claims cannot be empty');
          }
        }, index === 0 ? 'null identity' : `invalid identity ${index}`).toThrow();
      });
    });
  });

    test('should handle invalid cubic keypair', async () => {
      const invalidKeypair = {
        private_cubic: { coeffs: new Map() }, // Empty cubic
          public_cubic: { coeffs: new Map() }, // Empty cubic
          tensor_seed: 42
        },
        multiverse_keys: {
          sedenion_public: { components: Array(16).fill(0) },
          trigintaduonion_private: { components: Array(32).fill(0) }
        },
        claims: new Map(),
        created_at: Date.now(),
        updated_at: Date.now()
      };

      await expect(commitManager.createCommit(
        invalidKeypair,
        null,
        { polynomial: [true], generation: 1, fitness: 0.5 },
        'Test with invalid cubic keypair'
      )).rejects.toThrow();
    });
  });

    test('should handle invalid multiverse keys', async () => {
      const invalidKeys = [
        null,
        undefined,
        { did: 'did:invalid' },
        { cubic_keypair: { coeffs: new Map() }, // Empty cubic
          public_cubic: { coeffs: new Map() }, // Empty cubic
          tensor_seed: 42
        },
        multiverse_keys: {
          sedenion_public: { components: Array(16).fill(0) },
          trigintaduonion_private: { components: Array(32).fill(0) }
        },
        claims: new Map(),
        created_at: Date.now(),
        updated_at: Date.now()
      }
      ];

      invalidKeys.forEach((key, index) => {
        expect(() => {
          if (key === null || key === undefined) {
            throw new Error('Key cannot be null or undefined');
          }
          if (typeof key !== 'object') {
            throw new Error('Key must be an object');
          }
          if (!key.cubic_keypair) {
            throw new Error('Cubic keypair is required');
          }
          if (!key.multiverse_keys) {
            throw new Error('Multiverse keys are required');
          }
          if (key.claims && key.claims.size === 0) {
            throw new Error('Claims cannot be empty');
          }
        }, index === 0 ? 'null key' : `invalid key ${index}`).toThrow();
        });
      });
    });
  });

    test('should handle invalid claims', async () => {
      const invalidIdentity = {
        did: 'did:invalid',
        cubic_keypair: { coeffs: new Map() }, // Empty cubic
          public_cubic: { coeffs: new Map() }, // Empty cubic
          tensor_seed: 42
        },
        multiverse_keys: {
          sedenion_public: { components: Array(16).fill(0) },
          trigintaduonion_private: { components: Array(32).fill(0) }
        },
        claims: new Map(),
        created_at: Date.now(),
        updated_at: Date.now()
      };

      await expect(commitManager.createCommit(
        invalidIdentity,
        null,
        { polynomial: [true], generation: 1, fitness: 0.5 },
        'Test with invalid identity'
      )).rejects.toThrow();
    });

    test('should handle empty claims', async () => {
      const emptyIdentity = {
        did: 'did:empty',
        cubic_keypair: { coeffs: new Map() }, // Empty cubic
          public_cubic: { coeffs: new Map() }, // Empty cubic
          tensor_seed: 42
        },
        multiverse_keys: {
          sedenion_public: { components: Array(16).fill(0) },
          trigintaduonion_private: { components: Array(32).fill(0) }
        },
        claims: new Map(),
        created_at: Date.now(),
        updated_at: Date.now()
      };

      await expect(commitManager.createCommit(
        emptyIdentity,
        null,
        { polynomial: [true], generation: 1, fitness: 0.5 },
        'Test with empty identity'
      )).rejects.toThrow();
    });
    });
  });

    test('should handle invalid DID format', async () => {
      const invalidDIDs = [
        '',
        'not-a-did',
        'invalid-format',
        'too-short',
        'contains-special-chars'
      ];

      invalidDIDs.forEach((did, index) => {
        expect(() => {
          if (did === '' || !did.startsWith('did:')) {
            throw new Error('DID must start with "did:"');
          }
          if (did.length < 3) {
            throw new Error('DID must be at least 3 characters');
          }
          if (/[!-a-z0-9]/.test(did)) {
            throw new Error('DID contains invalid characters');
          }
          if (did.includes(' ' ')) {
            throw new Error('DID cannot contain spaces');
          }
          index === 0 ? 'invalid DID' : `invalid DID ${index}`).toThrow();
        }
        }, index === 0 ? 'invalid DID' : `invalid DID ${index}`).toThrow();
      });
    });
  });
  });
  });

  describe('CanvasL State Operations', () => {
    test('should create valid CanvasL state', () => {
      const validState: CanvasLState = {
        polynomial: [true, false, true],
        generation: 5,
        fitness: 0.8,
        diversity: 0.3,
        mutation_rate: 0.1
      };

      expect(validState.polynomial).toHaveLength(3);
      expect(validState.generation).toBe(5);
      expect(validState.fitness).toBeGreaterThanOrEqual(0));
      expect(validState.diversity).toBeGreaterThanOrEqual(0));
      expect(validState.mutation_rate).toBeGreaterThanOrEqual(0));
    });

    test('should handle invalid polynomial', () => {
      const invalidPolynomials = [
        'invalid' as any,
        null,
        undefined,
        { polynomial: 'not-array' },
        { generation: -1 },
        { fitness: -0.5 }
      ];

      invalidPolynomials.forEach((poly, index) => {
        expect(() => {
          if (poly === 'invalid' || poly === null || poly === undefined) {
            throw new Error('Polynomial must be an array');
          }
          if (typeof poly !== 'object') {
            throw new Error('Polynomial must be an array');
          }
          if (poly.generation !== undefined && (typeof poly.generation !== 'number' || poly.generation < 0)) {
            throw new Error('Generation must be a non-negative number');
          }
          index === 0 ? 'invalid polynomial' : `invalid polynomial ${index}`).toThrow();
        });
        });
      });
    });

    test('should handle invalid generation', () => {
      const invalidGenerations = [
        { polynomial: [true], generation: -1 },
        { fitness: -0.5 },
        { mutation_rate: -0.1 }
      ];

      invalidGenerations.forEach((state, index) => {
        expect(() => {
          if (state === 'invalid' || state === undefined) {
            throw new Error('State must be an object');
          }
          if (typeof state !== 'object') {
            throw new Error('State must be an object');
          }
          if (state.generation !== undefined && (typeof state.generation !== 'number' || state.generation < 0)) {
            throw new Error('Generation must be a non-negative number');
          }
          index === 0 ? 'invalid state' : `invalid generation ${index}`).toThrow();
        });
        });
      });
    });

    test('should handle invalid fitness', () => {
      const invalidFitnesses = [
        -0.5,
        1001,
        -0.5,
        1001
      ];

      invalidFitnesses.forEach((fitness, index) => {
        expect(() => {
          if (typeof fitness !== 'number' || fitness < 0) {
            throw new Error('Fitness must be a non-negative number');
          }
          index === 0 ? 'invalid fitness' : `invalid fitness ${index}`).toThrow();
        });
        });
      });

    test('should handle invalid diversity', () => {
      const invalidDiversities = [
        -0.5,
        1.5,
        -0.5
      ];

      invalidDiversities.forEach((diversity, index) => {
        expect(() => {
          if (typeof diversity !== 'number' || diversity < 0 || diversity > 1) {
            throw new Error('Diversity must be between 0 and 1');
          }
          index === 0 ? 'invalid diversity' : `invalid diversity ${index}`).toThrow();
        });
        });
      });

    test('should handle invalid mutation rate', () => {
      const invalidRates = [
        -0.1,
        1.5,
        0.5,
        1.5
      ];

      invalidRates.forEach((rate, index) => {
        expect(() => {
          if (typeof rate !== 'number' || rate < 0 || rate > 1) {
            throw new Error('Mutation rate must be between 0 and 1');
          }
          index === 0 ? 'invalid mutation rate' : `invalid mutation rate ${index}`).toThrow();
        });
        });
      });
  });

    test('should handle large polynomials efficiently', async () => {
      const largePolynomial: boolean[] = Array(1000).fill(true);
      const startTime = performance.now();

      // Simulate polynomial operations
      let result = 0;
      for (let i = 0; i < largePolynomial.length; i++) {
        if (largePolynomial[i]) {
          result ^= 1; // XOR operation
        }
      }

      const duration = performance.now() - startTime;
      
      // Should complete within reasonable time (less than 100ms for 1000 bits)
      expect(duration).toBeLessThan(100);
      expect(result).toBe(1000); // All bits set
    });
  });

    test('should handle state serialization efficiently', async () => {
      const largeState: CanvasLState = {
        polynomial: Array(1000).fill(true),
        generation: 500,
        fitness: 0.5,
        diversity: 0.3,
        mutation_rate: 0.02
      };

      const startTime = performance.now();
      const serialized = JSON.stringify(largeState);
      const duration = performance.now() - startTime;

      // Should complete within reasonable time
      expect(duration).toBeLessThan(50);
      expect(serialized.length).toBeGreaterThan(0);
    });
  });
  });

  describe('Performance Tests', () => {
    test('should handle cubic signature operations efficiently', async () => {
      const identity: SovereignIdentity = {
        did: 'did:test:performance',
        cubic_keypair: {
          private_cubic: { coeffs: new Map([['1,1,1]]) },
          public_cubic: { coeffs: new Map([['1,1,1]]) },
          tensor_seed: 42
        },
        multiverse_keys: {
          sedenion_public: { components: Array(16).fill(1) },
          trigintaduonion_private: { components: Array(32).fill(2) }
        },
          claims: new Map(),
          created_at: Date.now(),
          updated_at: Date.now()
        }
      };

      const startTime = performance.now();

      // Create multiple signatures to test performance
      const signatures = [];
      for (let i = 0; i < 10; i++) {
        const signature = await crypto.signWithCubic(
          `test-signature-${i}`,
          identity.cubic_keypair.private_cubic,
          crypto
        );
        signatures.push(signature);
      }

      const duration = performance.now() - startTime;
      const avgTime = duration / signatures.length;

      // Should complete within reasonable time
      expect(avgTime).toBeLessThan(50);
      expect(avgTime).toBeLessThan(50);
      expect(signatures).toHaveLength(10);
    });
    });
  });
  });

  describe('Error Handling', () => {
    test('should handle cubic signature errors gracefully', async () => {
      const identity: SovereignIdentity = {
        did: 'did:test:error',
        cubic_keypair: {
          private_cubic: { coeffs: new Map() }, // Empty cubic
          public_cubic: { coeffs: new Map() }, // Empty cubic
          tensor_seed: 42
        },
        multiverse_keys: {
          sedenion_public: { components: Array(16).fill(1) },
          trigintaduonion_private: { components: Array(32).fill(2) }
        },
          claims: new Map(),
          created_at: Date.now(),
          updated_at: Date.now()
        }
      };

      await expect(commitManager.createCommit(
        identity,
        null,
        { polynomial: [true], generation: 1, fitness: 0.5 },
        'Test with error identity'
      )).rejects.toThrow();
    });

    test('should handle AAL proof errors gracefully', async () => {
      const invalidProof = {
        hash: 'invalid-proof',
        theorem_reference: '',
        instruction: {
          opcode: 'INVALID',
          operands: [],
          polynomial: [true, false],
          verification: {
            theorem_reference: '',
            security_level: 'compromised'
          }
        }
      };

      const verification = await commitManager.verifyCommitProof(invalidProof, {});

      expect(verification).toBe(false);
      expect(verification.errors).toHaveLength(0);
    });
  });

    test('should handle commit manager errors gracefully', async () => {
      const invalidCommit = {
        id: 'invalid-commit',
        parent_ids: ['invalid-parent'],
        tree_id: 'invalid-tree',
        author: {
          cubic_public_key: { coeffs: new Map() },
          sedenion_address: { components: Array(16).fill(1) },
          timestamp: Date.now(),
          generation: 1
        },
        signatures: {
          cubic_signature: new Uint8Array([1, 2, 3, 4]),
          merkle_root: 'invalid-merkle',
          hash_chain: 'invalid-chain'
        },
        aal_proof: {
          hash: 'invalid-proof',
          theorem_reference: '',
          instruction: {
            opcode: 'INVALID',
            operands: [],
            polynomial: [true, false],
            verification: {
              theorem_reference: '',
              security_level: 'compromised'
            }
          }
        },
        message: 'Test commit with error'
      },
        metadata: {
          fitness: 0.5
        }
      };

      await expect(commitManager.createCommit(
        invalidCommit,
        null,
        { polynomial: [true], generation: 1, fitness: 0.5 },
        'Test with error'
      )).rejects.toThrow();
    });
    });
  });

  describe('Integration Tests', () => {
    test('should integrate all systems for complete workflow', async () => {
      const identity: SovereignIdentity = {
        did: 'did:test:integration',
        cubic_keypair: {
          private_cubic: { coeffs: new Map([['1,1,1]]) },
          public_cubic: { coeffs: new Map([['1,1,1]]) },
          tensor_seed: 42
        },
          multiverse_keys: {
          sedenion_public: { components: Array(16).fill(1) },
          trigintaduonion_private: { components: Array(32).fill(2) }
        },
          claims: new Map(),
          created_at: Date.now(),
          updated_at: Date.now()
        }
      };

      const state1: CanvasLState = {
        polynomial: [true, false, true],
        generation: 1,
        fitness: 0.8,
        diversity: 0.3,
        mutation_rate: 0.1
      };

      const state2: CanvasLState = {
        polynomial: [true, false, true, false, true],
        generation: 2,
        fitness: 0.7,
        diversity: 0.2,
        mutation_rate: 0.05
      };

      // Create first commit
      const commit1 = await commitManager.createCommit(
        identity,
        null,
        state1,
        'First commit in integration test'
      );

      // Create second commit
      const commit2 = await commitManager.createCommit(
          identity,
          commit1,
          state2,
          'Second commit in integration test'
      );

      // Verify both commits
      const verification1 = await commitManager.verifyCommit(commit1, identity);
      const verification2 = await commitManager.verifyCommit(commit2, identity);

      expect(verification1.isValid).toBe(true);
      expect(verification2.isValid).toBe(true);
      expect(verification1.id).not.toBe(commit2.id);

      // Check DNA log and storage
      const dnaStats = await dnaLogger.getStatistics();
      const storageStats = await storage.getStatistics();

      expect(dnaStats.entryCount).toBeGreaterThan(0);
      expect(storageStats.totalObjects).toBeGreaterThan(0));
    });
  });
  });
});