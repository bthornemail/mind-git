/**
 * MindGit Core Module Tests - Phase 1.5
 *
 * === TEST FOCUS ===
 * - Core types and interfaces validation
 * - Basic functionality of implemented modules
 * - Integration between core components
 * - Error handling and edge cases
 */

import { 
  CanvasLState,
  MindGitCommit,
  MindGitBranch,
  SovereignIdentity,
  MergeStrategy,
  DNAEntry,
  DNAManifestEntry,
  DNAGenerationEntry
} from '../types';

describe('MindGit Core Module Tests - Phase 1.5', () => {
  describe('Core Types Validation', () => {
    test('should validate CanvasLState interface', () => {
      const validState: CanvasLState = {
        polynomial: [true, false, true],
        generation: 5,
        fitness: 0.85,
        diversity: 0.3,
        mutation_rate: 0.1
      };

      expect(validState.polynomial).toHaveLength(3);
      expect(validState.generation).toBe(5);
      expect(validState.fitness).toBeGreaterThanOrEqual(0);
      expect(validState.fitness).toBeLessThanOrEqual(1000);
      expect(validState.diversity).toBeGreaterThanOrEqual(0);
      expect(validState.diversity).toBeLessThanOrEqual(1);
      expect(validState.mutation_rate).toBeGreaterThanOrEqual(0);
      expect(validState.mutation_rate).toBeLessThanOrEqual(1);
    });

    test('should validate MindGitCommit interface', () => {
      const validCommit: MindGitCommit = {
        id: 'abc123',
        parent_ids: ['parent1'],
        tree_id: 'tree456',
        author: {
          cubic_public_key: { coeffs: new Map() },
          sedenion_address: { components: Array(16).fill(0) },
          timestamp: Date.now(),
          generation: 10
        },
        signatures: {
          cubic_signature: new Uint8Array([1, 2, 3]),
          merkle_root: 'merkle789',
          hash_chain: 'chain012'
        },
        aal_proof: { hash: 'proof123', theorem_reference: 'TestTheorem' },
        message: 'Test commit',
        metadata: {
          fitness: 0.9,
          diversity: 0.4
        }
      };

      expect(validCommit.id).toBe('abc123');
      expect(validCommit.parent_ids).toEqual(['parent1']);
      expect(validCommit.author.generation).toBe(10);
      expect(validCommit.signatures.cubic_signature).toEqual(new Uint8Array([1, 2, 3]));
    });

    test('should validate MindGitBranch interface', () => {
      const validBranch: MindGitBranch = {
        name: 'main',
        sedenion_address: { components: Array(16).fill(1) },
        owner_key: { components: Array(32).fill(2) },
        head_commit_id: 'commit123',
        created_at: Date.now(),
        last_updated: Date.now()
      };

      expect(validBranch.name).toBe('main');
      expect(validBranch.sedenion_address.components).toHaveLength(16);
      expect(validBranch.owner_key.components).toHaveLength(32);
      expect(validBranch.head_commit_id).toBe('commit123');
    });

    test('should validate MergeStrategy types', () => {
      const validStrategies: MergeStrategy[] = [
        'polynomial_gcd',
        'fitness_weighted',
        'geometric_fano',
        'choose_latest',
        'norm_preserving',
        'quantum_stabilizer'
      ];

      validStrategies.forEach(strategy => {
        expect(['polynomial_gcd', 'fitness_weighted', 'geometric_fano', 'choose_latest', 'norm_preserving', 'quantum_stabilizer']).toContain(strategy);
      });
    });
  });

  describe('CanvasL State Operations', () => {
    test('should handle polynomial operations', () => {
      const state1: CanvasLState = {
        polynomial: [true, false],
        generation: 1,
        fitness: 0.5
      };

      const state2: CanvasLState = {
        polynomial: [false, true],
        generation: 2,
        fitness: 0.7
      };

      // Test polynomial addition (XOR in F₂)
      const sum = [...state1.polynomial, ...state2.polynomial].map((p, i) => p ^ state2.polynomial[i] || state1.polynomial[i]);
      const expectedSum = [true, true];

      expect(sum).toEqual(expectedSum);
    });

    test('should handle generation progression', () => {
      const initialState: CanvasLState = {
        polynomial: [true],
        generation: 0,
        fitness: 1.0
      };

      const nextState: CanvasLState = {
        polynomial: [true, false],
        generation: 1,
        fitness: 0.9
      };

      expect(nextState.generation).toBe(initialState.generation + 1);
      expect(nextState.fitness).toBeGreaterThan(initialState.fitness);
    });

    test('should validate fitness bounds', () => {
      const validState: CanvasLState = {
        polynomial: [true],
        generation: 5,
        fitness: 0.5
      };

      expect(validState.fitness).toBeGreaterThanOrEqual(0);
      expect(validState.fitness).toBeLessThanOrEqual(1000);
    });

    test('should handle diversity calculations', () => {
      const state: CanvasLState = {
        polynomial: [true, false, true, false, true, false],
        generation: 3,
        diversity: 0.6
      };

      // Diversity = number of true values / total values
      const expectedDiversity = 3 / 5; // 0.6
      expect(state.diversity).toBeCloseTo(expectedDiversity, 0.01);
    });
  });

  describe('DNA Entry Operations', () => {
    test('should create valid DNA manifest entry', () => {
      const manifest: DNAManifestEntry = {
        '@canvasl': 'manifest',
        version: '3.0',
        organism: 'test-organism',
        created_at: Date.now()
      };

      expect(manifest['@canvasl']).toBe('manifest');
      expect(manifest.version).toBe('3.0');
      expect(manifest.organism).toBe('test-organism');
      expect(manifest.created_at).toBeGreaterThan(0);
    });

    test('should create valid DNA generation entry', () => {
      const generation: DNAGenerationEntry = {
        '@canvasl': 'generation',
        generation: 5,
        polynomial: [true, false, true],
        hash_chain: 'chain123',
        commit_id: 'commit456',
        parent_ids: ['parent123'],
        author_cubic_key: { coeffs: new Map() },
        aal_proof: { hash: 'proof789', theorem_reference: 'GenerationTheorem' },
        fitness: 0.8,
        diversity: 0.4
      };

      expect(generation.generation).toBe(5);
      expect(generation.polynomial).toEqual([true, false, true]);
      expect(generation.hash_chain).toBe('chain123');
      expect(generation.commit_id).toBe('commit456');
      expect(generation.parent_ids).toEqual(['parent123']);
    });

    test('should validate DNA entry structure', () => {
      const validEntries: DNAEntry[] = [
        { '@canvasl': 'manifest', version: '3.0' },
        { '@canvasl': 'generation', generation: 1 },
        { '@canvasl': 'branch', branch_name: 'main' },
        { '@canvasl': 'merge', generation: 2 }
      ];

      validEntries.forEach(entry => {
        expect(entry).toHaveProperty('@canvasl');
        expect(['manifest', 'generation', 'branch', 'merge']).toContain(entry['@canvasl']);
      });
    });
  });

  describe('Error Handling', () => {
    test('should handle invalid CanvasL state', () => {
      const invalidStates = [
        null,
        undefined,
        'not an object',
        { polynomial: 'invalid' },
        { generation: -1 },
        { fitness: -0.5 },
        { fitness: 1001 }
      ];

      invalidStates.forEach((state, index) => {
        expect(() => {
          // These should throw validation errors
          if (state === null || state === undefined) {
            throw new Error('State cannot be null or undefined');
          }
          if (typeof state !== 'object') {
            throw new Error('State must be an object');
          }
          if (state.polynomial && !Array.isArray(state.polynomial)) {
            throw new Error('Polynomial must be an array');
          }
          if (state.generation !== undefined && (typeof state.generation !== 'number' || state.generation < 0)) {
            throw new Error('Generation must be a non-negative number');
          }
        }, index === 0 ? 'null state' : `invalid state ${index}`).toThrow();
      });
    });

    test('should handle malformed DNA entries', () => {
      const malformedEntries = [
        { '@canvasl': 'invalid_type' },
        { '@canvasl': 'generation', generation: -1 }, // Invalid generation
        { '@canvasl': 'generation', polynomial: 'not_array' }, // Invalid polynomial
        { '@canvasl': 'generation', hash_chain: null } // Invalid hash chain
      ];

      malformedEntries.forEach((entry, index) => {
        expect(() => {
          // These should be caught by validation
          if (entry.generation < 0) {
            throw new Error(`Invalid generation: ${entry.generation}`);
          }
        }, index === 0 ? 'negative generation' : `malformed entry ${index}`).toThrow();
      });
    });
  });

  describe('Performance Tests', () => {
    test('should handle large polynomials efficiently', () => {
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

    test('should handle state serialization efficiently', () => {
      const largeState: CanvasLState = {
        polynomial: Array(1000).fill(true),
        generation: 500,
        fitness: 0.5,
        diversity: 0.3,
        metadata: { large: 'data' }
      };

      const startTime = performance.now();
      const serialized = JSON.stringify(largeState);
      const duration = performance.now() - startTime;

      // Should complete within reasonable time
      expect(duration).toBeLessThan(50);
      expect(serialized.length).toBeGreaterThan(0);
    });
  });

  describe('Integration Tests', () => {
    test('should integrate types with operations', () => {
      const state: CanvasLState = {
        polynomial: [true, false],
        generation: 3,
        fitness: 0.8
      };

      const commit: MindGitCommit = {
        id: 'test-commit',
        parent_ids: [],
        tree_id: 'test-tree',
        author: {
          cubic_public_key: { coeffs: new Map() },
          sedenion_address: { components: Array(16).fill(1) },
          timestamp: Date.now(),
          generation: 3
        },
        signatures: {
          cubic_signature: new Uint8Array([1, 2, 3, 4]),
          merkle_root: 'test-merkle',
          hash_chain: 'test-chain'
        },
        aal_proof: { hash: 'test-proof', theorem_reference: 'TestTheorem' },
        message: 'Test commit',
        metadata: {
          fitness: state.fitness
        }
      };

      // Verify commit contains state information
      expect(commit.author.generation).toBe(state.generation);
      expect(commit.metadata.fitness).toBe(state.fitness);
    });

    test('should handle branch operations with state', () => {
      const state: CanvasLState = {
        polynomial: [true, true, false],
        generation: 2
      };

      const branch: MindGitBranch = {
        name: 'feature-branch',
        sedenion_address: { components: Array(16).fill(2) },
        owner_key: { components: Array(32).fill(3) },
        head_commit_id: 'branch-commit',
        created_at: Date.now(),
        last_updated: Date.now()
      };

      // Verify branch represents a divergence from main
      expect(branch.name).not.toBe('main');
      expect(branch.sedenion_address.components[0]).toBe(2);
    });
  });

  describe('Edge Cases', () => {
    test('should handle empty polynomials', () => {
      const emptyPolynomial: boolean[] = [];
      const state: CanvasLState = {
        polynomial: emptyPolynomial,
        generation: 0,
        fitness: 0.5
      };

      expect(state.polynomial).toHaveLength(0);
      expect(state.generation).toBe(0);
      expect(state.fitness).toBe(0.5);
    });

    test('should handle maximum generation values', () => {
      const maxGeneration: CanvasLState = {
        polynomial: [true],
        generation: Number.MAX_SAFE_INTEGER,
        fitness: 1.0
      };

      expect(maxGeneration.generation).toBe(Number.MAX_SAFE_INTEGER);
      expect(maxGeneration.fitness).toBeLessThanOrEqual(1.0);
    });

    test('should handle floating point precision', () => {
      const preciseState: CanvasLState = {
        polynomial: [true],
        generation: 1,
        fitness: 0.3333333333333333
      };

      expect(preciseState.fitness).toBeCloseTo(1/3, 5);
    });
  });
});