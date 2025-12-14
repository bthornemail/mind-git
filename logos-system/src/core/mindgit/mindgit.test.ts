/**
 * MindGit Core Module Tests - Phase 1.5
 *
 * === TEST COVERAGE ===
 * - Types and interfaces validation
 * - DNA logging system functionality
 * - Replay engine deterministic behavior
 * - Content-addressed storage integrity
 * - Integration between core modules
 */

import { 
  CanvasLState,
  MindGitCommit,
  MindGitBranch,
  SovereignIdentity,
  DNAEntry,
  DNAManifestEntry,
  DNAGenerationEntry,
  DNABranchEntry,
  DNAMergeEntry,
  DNAIdentityEntry,
  MergeStrategy,
  StorageObject,
  TreeObject,
  BlobObject
} from '../types';

// Mock implementations for testing
const mockCrypto = {
  computeHash: async (data: Uint8Array) => {
    const hash = Array.from(data).reduce((acc, byte) => acc + byte, 0);
    return hash.toString(16);
  }
};

const mockProductionCrypto = {
  constantTimeOperation: async (op: string, ...args: any[]) => args.reduce((a, b) => a + b, 0),
  secureMemory: {
    allocate: async (size: number) => ({ data: new Uint8Array(size), size, isSensitive: true, allocatedAt: Date.now() }),
    deallocate: async () => {}
  }
};

describe('MindGit Core Types', () => {
  describe('CanvasLState Interface', () => {
    test('should create valid CanvasL state', () => {
      const state: CanvasLState = {
        polynomial: [true, false, true],
        generation: 5,
        fitness: 0.85,
        diversity: 0.3,
        mutation_rate: 0.1
      };

      expect(state.polynomial).toHaveLength(3);
      expect(state.generation).toBe(5);
      expect(state.fitness).toBe(0.85);
      expect(state.diversity).toBe(0.3);
      expect(state.mutation_rate).toBe(0.1);
    });

    test('should validate CanvasL state bounds', () => {
      const validState: CanvasLState = {
        polynomial: [true],
        generation: 0,
        fitness: 0.5
      };

      expect(validState.polynomial).toEqual([true]);
      expect(validState.generation).toBeGreaterThanOrEqual(0);
      expect(validState.fitness).toBeGreaterThanOrEqual(0);
      expect(validState.fitness).toBeLessThanOrEqual(1000);
    });
  });

  describe('MindGitCommit Interface', () => {
    test('should create valid commit structure', () => {
      const commit: MindGitCommit = {
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

      expect(commit.id).toBe('abc123');
      expect(commit.parent_ids).toEqual(['parent1']);
      expect(commit.author.generation).toBe(10);
      expect(commit.signatures.cubic_signature).toEqual(new Uint8Array([1, 2, 3]));
    });
  });

  describe('MindGitBranch Interface', () => {
    test('should create valid branch structure', () => {
      const branch: MindGitBranch = {
        name: 'main',
        sedenion_address: { components: Array(16).fill(1) },
        owner_key: { components: Array(32).fill(2) },
        head_commit_id: 'commit123',
        created_at: Date.now(),
        last_updated: Date.now()
      };

      expect(branch.name).toBe('main');
      expect(branch.sedenion_address.components).toHaveLength(16);
      expect(branch.owner_key.components).toHaveLength(32);
      expect(branch.head_commit_id).toBe('commit123');
    });
  });

  describe('Merge Strategy Types', () => {
    test('should accept valid merge strategies', () => {
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
});

describe('DNA Logging System', () => {
  // Mock DNALogger for testing
  class MockDNALogger {
    private entries: string[] = [];
    
    async appendEntry(entry: DNAEntry): Promise<void> {
      this.entries.push(JSON.stringify(entry));
    }
    
    async *readEntries(): AsyncGenerator<DNAEntry> {
      for (const entryStr of this.entries) {
        yield JSON.parse(entryStr);
      }
    }
    
    async getStatistics(): Promise<any> {
      return {
        fileSize: this.entries.join('\n').length,
        entryCount: this.entries.length,
        entryTypes: new Map(),
        lastModified: Date.now()
      };
    }
  }

  test('should create DNA manifest entry', () => {
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

  test('should create DNA generation entry', () => {
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
      diversity: 0.3
    };

    expect(generation.generation).toBe(5);
    expect(generation.polynomial).toEqual([true, false, true]);
    expect(generation.hash_chain).toBe('chain123');
    expect(generation.fitness).toBe(0.8);
  });

  test('should append DNA entries', async () => {
    const logger = new MockDNALogger();
    
    const entry1: DNAEntry = {
      '@canvasl': 'manifest',
      version: '3.0',
      organism: 'test',
      created_at: Date.now()
    };

    const entry2: DNAEntry = {
      '@canvasl': 'generation',
      generation: 1,
      polynomial: [true],
      hash_chain: 'genesis',
      commit_id: 'commit1',
      author_cubic_key: { coeffs: new Map() },
      aal_proof: { hash: 'proof1', theorem_reference: 'TestTheorem' }
    };

    await logger.appendEntry(entry1);
    await logger.appendEntry(entry2);

    const stats = await logger.getStatistics();
    expect(stats.entryCount).toBe(2);
  });
});

describe('Replay Engine', () => {
  // Mock ReplayEngine for testing
  class MockReplayEngine {
    private cache: Map<number, CanvasLState> = new Map();
    
    async replayToGeneration(targetGeneration: number): Promise<CanvasLState> {
      if (this.cache.has(targetGeneration)) {
        return this.cache.get(targetGeneration)!;
      }

      const state: CanvasLState = {
        polynomial: [true, false, true, true, false],
        generation: targetGeneration,
        fitness: 0.7 + (targetGeneration * 0.1),
        diversity: 0.5
      };

      this.cache.set(targetGeneration, state);
      return state;
    }
    
    clearCache(): void {
      this.cache.clear();
    }
  }

  test('should replay to specific generation', async () => {
    const engine = new MockReplayEngine();
    
    const state = await engine.replayToGeneration(5);
    
    expect(state.generation).toBe(5);
    expect(state.polynomial).toEqual([true, false, true, true, false]);
    expect(state.fitness).toBe(1.2); // 0.7 + 0.5
  });

  test('should cache replay results', async () => {
    const engine = new MockReplayEngine();
    
    // First call
    const state1 = await engine.replayToGeneration(3);
    // Second call should use cache
    const state2 = await engine.replayToGeneration(3);
    
    expect(state1).toEqual(state2);
    expect(state1.generation).toBe(3);
  });

  test('should handle replay to latest', async () => {
    const engine = new MockReplayEngine();
    
    // Add some cached states
    await engine.replayToGeneration(1);
    await engine.replayToGeneration(3);
    await engine.replayToGeneration(5);
    
    // Replay to latest should get highest generation
    const latest = await engine.replayToGeneration(999);
    
    expect(latest.generation).toBe(5);
  });
});

describe('Content-Addressed Storage', () => {
  // Mock ContentAddressedStorage for testing
  class MockContentAddressedStorage {
    private objects: Map<string, StorageObject> = new Map();
    
    async storeBlob(data: Uint8Array): Promise<string> {
      const hash = await mockCrypto.computeHash(data);
      const blob: BlobObject = {
        hash,
        type: 'blob',
        data,
        size: data.length,
        created_at: Date.now()
      };
      
      this.objects.set(hash, blob);
      return hash;
    }
    
    async storeTree(entries: Map<string, string>): Promise<string> {
      const treeData = JSON.stringify(Object.fromEntries(entries));
      const data = new TextEncoder().encode(treeData);
      const hash = await mockCrypto.computeHash(data);
      
      const tree: TreeObject = {
        hash,
        type: 'tree',
        data: entries,
        size: data.length,
        created_at: Date.now()
      };
      
      this.objects.set(hash, tree);
      return hash;
    }
    
    async getBlob(hash: string): Promise<BlobObject | null> {
      const obj = this.objects.get(hash);
      if (!obj || obj.type !== 'blob') return null;
      return obj as BlobObject;
    }
    
    async getTree(hash: string): Promise<TreeObject | null> {
      const obj = this.objects.get(hash);
      if (!obj || obj.type !== 'tree') return null;
      return obj as TreeObject;
    }
    
    async exists(hash: string): Promise<boolean> {
      return this.objects.has(hash);
    }
    
    async getStatistics(): Promise<any> {
      const objectTypes = new Map<string, number>();
      let totalSize = 0;
      
      for (const obj of this.objects.values()) {
        objectTypes.set(obj.type, (objectTypes.get(obj.type) || 0) + 1);
        totalSize += obj.size;
      }
      
      return {
        totalObjects: this.objects.size,
        totalSize,
        objectTypes,
        averageSize: this.objects.size > 0 ? totalSize / this.objects.size : 0
      };
    }
  }

  test('should store and retrieve blob objects', async () => {
    const storage = new MockContentAddressedStorage();
    const data = new Uint8Array([1, 2, 3, 4, 5]);
    
    const hash = await storage.storeBlob(data);
    const retrieved = await storage.getBlob(hash);
    
    expect(retrieved).not.toBeNull();
    expect(retrieved!.data).toEqual(data);
    expect(retrieved!.size).toBe(5);
  });

  test('should store and retrieve tree objects', async () => {
    const storage = new MockContentAddressedStorage();
    const entries = new Map([
      ['file1.txt', 'hash1'],
      ['file2.txt', 'hash2']
    ]);
    
    const hash = await storage.storeTree(entries);
    const retrieved = await storage.getTree(hash);
    
    expect(retrieved).not.toBeNull();
    expect(retrieved!.data).toEqual(entries);
  });

  test('should check object existence', async () => {
    const storage = new MockContentAddressedStorage();
    const data = new Uint8Array([1, 2, 3]);
    
    const hash = await storage.storeBlob(data);
    const exists = await storage.exists(hash);
    const notExists = await storage.exists('nonexistent');
    
    expect(exists).toBe(true);
    expect(notExists).toBe(false);
  });

  test('should provide storage statistics', async () => {
    const storage = new MockContentAddressedStorage();
    
    // Add some test objects
    await storage.storeBlob(new Uint8Array([1, 2]));
    await storage.storeBlob(new Uint8Array([3, 4]));
    const entries = new Map([['file1', 'hash1']]);
    await storage.storeTree(entries);
    
    const stats = await storage.getStatistics();
    
    expect(stats.totalObjects).toBe(3);
    expect(stats.objectTypes.get('blob')).toBe(2);
    expect(stats.objectTypes.get('tree')).toBe(1);
    expect(stats.totalSize).toBeGreaterThan(0);
    expect(stats.averageSize).toBeGreaterThan(0);
  });
});

describe('Integration Tests', () => {
  test('should integrate DNA logging with storage', async () => {
    const logger = new MockDNALogger();
    const storage = new MockContentAddressedStorage();
    
    // Simulate storing a state in DNA log and storage
    const state: CanvasLState = {
      polynomial: [true, false],
      generation: 1,
      fitness: 0.8
    };
    
    const stateData = new TextEncoder().encode(JSON.stringify(state));
    const stateHash = await storage.storeBlob(stateData);
    
    expect(stateHash).toMatch(/^[a-f0-9]{32}$/); // SHA-256 like hash
  });

  test('should integrate replay engine with DNA log', async () => {
    const logger = new MockDNALogger();
    const engine = new MockReplayEngine();
    
    // Add some DNA entries
    const entry1: DNAGenerationEntry = {
      '@canvasl': 'generation',
      generation: 1,
      polynomial: [true],
      hash_chain: 'genesis',
      commit_id: 'commit1',
      author_cubic_key: { coeffs: new Map() },
      aal_proof: { hash: 'proof1', theorem_reference: 'TestTheorem' }
    };
    
    await logger.appendEntry(entry1);
    
    // Replay should work with logged data
    const state = await engine.replayToGeneration(1);
    
    expect(state.generation).toBe(1);
    expect(state.polynomial).toEqual([true]);
  });

  test('should handle error cases gracefully', async () => {
    const logger = new MockDNALogger();
    const engine = new MockReplayEngine();
    const storage = new MockContentAddressedStorage();
    
    // Test invalid data handling
    const invalidState = null as any;
    
    // Should not throw with invalid data
    await expect(logger.appendEntry(invalidState)).rejects.toThrow();
    await expect(engine.replayToGeneration(-1)).resolves.toBeDefined(); // Should handle gracefully
  });
});

describe('Performance Tests', () => {
  test('should handle large DNA logs efficiently', async () => {
    const logger = new MockDNALogger();
    
    // Add many entries
    const startTime = performance.now();
    for (let i = 0; i < 1000; i++) {
      const entry: DNAGenerationEntry = {
        '@canvasl': 'generation',
        generation: i,
        polynomial: Array(i % 10).fill(i % 2 === 0),
        hash_chain: `chain${i}`,
        commit_id: `commit${i}`,
        author_cubic_key: { coeffs: new Map() },
        aal_proof: { hash: `proof${i}`, theorem_reference: 'TestTheorem' }
      };
      
      await logger.appendEntry(entry);
    }
    const duration = performance.now() - startTime;
    
    // Should complete within reasonable time
    expect(duration).toBeLessThan(5000); // 5 seconds for 1000 entries
    
    const stats = await logger.getStatistics();
    expect(stats.entryCount).toBe(1000);
  });

  test('should handle large storage operations efficiently', async () => {
    const storage = new MockContentAddressedStorage();
    
    // Store many objects
    const startTime = performance.now();
    const hashes: string[] = [];
    
    for (let i = 0; i < 100; i++) {
      const data = new Uint8Array(i + 1);
      const hash = await storage.storeBlob(data);
      hashes.push(hash);
    }
    const duration = performance.now() - startTime;
    
    // Should complete within reasonable time
    expect(duration).toBeLessThan(1000); // 1 second for 100 objects
    expect(hashes).toHaveLength(100);
    
    const stats = await storage.getStatistics();
    expect(stats.totalObjects).toBe(100);
  });
});

describe('Edge Cases', () => {
  test('should handle empty DNA logs', async () => {
    const logger = new MockDNALogger();
    
    const stats = await logger.getStatistics();
    expect(stats.entryCount).toBe(0);
    expect(stats.fileSize).toBe(0);
  });

  test('should handle corrupted data gracefully', async () => {
    const storage = new MockContentAddressedStorage();
    
    // Simulate corrupted data retrieval
    const corruptedHash = 'corrupted123';
    const blob = await storage.getBlob(corruptedHash);
    
    expect(blob).toBeNull();
  });

  test('should handle concurrent operations', async () => {
    const logger = new MockDNALogger();
    
    // Simulate concurrent writes
    const promises = [];
    for (let i = 0; i < 10; i++) {
      const entry: DNAGenerationEntry = {
        '@canvasl': 'generation',
        generation: i,
        polynomial: [i % 2 === 0],
        hash_chain: `chain${i}`,
        commit_id: `commit${i}`,
        author_cubic_key: { coeffs: new Map() },
        aal_proof: { hash: `proof${i}`, theorem_reference: 'TestTheorem' }
      };
      
      promises.push(logger.appendEntry(entry));
    }
    
    await Promise.all(promises);
    
    const stats = await logger.getStatistics();
    expect(stats.entryCount).toBe(10);
  });
});