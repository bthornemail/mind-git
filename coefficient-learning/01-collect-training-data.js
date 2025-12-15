#!/usr/bin/env node

/**
 * Pfister 32 Coefficient Learning - Step 1: Training Data Collection
 *
 * Collects 32D semantic vectors from all 10 analyzed repositories
 * and generates all 45 possible pairs for training.
 *
 * Mathematical Foundation:
 * - Extract semantic vectors from kernel metadata
 * - Generate C(10,2) = 45 repository pairs
 * - Include ground truth from 5 validated pairs
 */

import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

// Repository list
const REPOSITORIES = [
  { name: 'react', path: 'test-repos/react' },
  { name: 'vue', path: 'test-repos/vue' },
  { name: 'express', path: 'test-repos/express' },
  { name: 'fastapi', path: 'test-repos/fastapi' },
  { name: 'tensorflow', path: 'test-repos/tensorflow' },
  { name: 'pytorch', path: 'test-repos/pytorch' },
  { name: 'webpack', path: 'test-repos/webpack' },
  { name: 'vite', path: 'test-repos/vite' },
  { name: 'redis', path: 'test-repos/redis' },
  { name: 'postgresql', path: 'test-repos/postgres' }
];

// Ground truth from validated pairs
const GROUND_TRUTH = [
  { repoA: 'react', repoB: 'vue', similarity: 0.8997, domain: 'frontend' },
  { repoA: 'express', repoB: 'fastapi', similarity: 0.6105, domain: 'backend' },
  { repoA: 'tensorflow', repoB: 'pytorch', similarity: 0.8268, domain: 'ml' },
  { repoA: 'webpack', repoB: 'vite', similarity: 0.8370, domain: 'build' },
  { repoA: 'redis', repoB: 'postgresql', similarity: 0.7384, domain: 'database' }
];

/**
 * Load kernel metadata from repository
 */
function loadKernelMetadata(repoPath) {
  const kernelPath = path.join(__dirname, '..', repoPath, '.metadata-kernel');
  const registryPath = path.join(kernelPath, 'components', 'registry.jsonl');

  if (!fs.existsSync(registryPath)) {
    throw new Error(`Kernel metadata not found: ${registryPath}`);
  }

  // Load registry (it's actually JSON, not JSONL)
  const registry = JSON.parse(fs.readFileSync(registryPath, 'utf-8'));

  return {
    repository: path.basename(repoPath),
    components: registry.components || [],
    totalComponents: (registry.components || []).length
  };
}

/**
 * Extract 32D semantic vector from kernel metadata
 *
 * Vector structure: 8 layers × 4 features = 32 dimensions
 * Features per layer:
 *   0: Presence (normalized component count)
 *   1: Complexity (normalized average)
 *   2: Mathematical content ratio
 *   3: Test coverage ratio
 */
function extract32DVector(metadata) {
  const vector = new Array(32).fill(0);
  const components = metadata.components || [];

  // Group components by layer
  const layerGroups = {};
  for (let i = 1; i <= 8; i++) {
    layerGroups[i] = components.filter(c => c.layer === i);
  }

  // Extract features for each layer
  for (let layer = 1; layer <= 8; layer++) {
    const baseIndex = (layer - 1) * 4;
    const layerComponents = layerGroups[layer] || [];

    if (layerComponents.length > 0) {
      // Feature 0: Presence (normalized component count)
      vector[baseIndex + 0] = Math.min(1.0, layerComponents.length / 20);

      // Feature 1: Complexity (normalized average)
      const avgComplexity = layerComponents.reduce((sum, c) => sum + (c.complexity || 0), 0) / layerComponents.length;
      vector[baseIndex + 1] = Math.min(1.0, avgComplexity / 100);

      // Feature 2: Mathematical content ratio
      const mathComponents = layerComponents.filter(c => c.mathematical && c.mathematical.hasMathematical);
      vector[baseIndex + 2] = layerComponents.length > 0 ? mathComponents.length / layerComponents.length : 0;

      // Feature 3: Test coverage ratio
      const totalFiles = layerComponents.reduce((sum, c) => sum + (c.files || 0), 0);
      const totalTests = layerComponents.reduce((sum, c) => sum + (c.tests || 0), 0);
      vector[baseIndex + 3] = totalFiles > 0 ? Math.min(1.0, totalTests / totalFiles) : 0;
    }
  }

  return vector;
}

/**
 * Compute norm of vector
 */
function computeNorm(vector) {
  return Math.sqrt(vector.reduce((sum, val) => sum + val * val, 0));
}

/**
 * Compute cosine similarity between two vectors
 */
function cosineSimilarity(vecA, vecB) {
  const dotProduct = vecA.reduce((sum, val, i) => sum + val * vecB[i], 0);
  const normA = computeNorm(vecA);
  const normB = computeNorm(vecB);

  if (normA === 0 || normB === 0) return 0;

  return dotProduct / (normA * normB);
}

/**
 * Main execution
 */
async function main() {
  console.log('🧮 Pfister 32 Coefficient Learning - Training Data Collection');
  console.log('================================================================================\n');

  // Step 1: Collect 32D vectors from all repositories
  console.log('📊 Extracting semantic vectors from repositories...\n');

  const vectors = [];
  for (const repo of REPOSITORIES) {
    try {
      const metadata = loadKernelMetadata(repo.path);
      const vector = extract32DVector(metadata);
      const norm = computeNorm(vector);

      vectors.push({
        name: repo.name,
        path: repo.path,
        vector: vector,
        norm: norm,
        components: metadata.components?.length || 0
      });

      console.log(`  ✅ ${repo.name.padEnd(15)} | Components: ${String(metadata.components?.length || 0).padStart(4)} | Norm: ${norm.toFixed(4)}`);
    } catch (error) {
      console.error(`  ❌ ${repo.name}: ${error.message}`);
    }
  }

  // Step 2: Generate all pairs
  console.log('\n🔗 Generating all repository pairs...\n');

  const pairs = [];
  for (let i = 0; i < vectors.length; i++) {
    for (let j = i + 1; j < vectors.length; j++) {
      const repoA = vectors[i];
      const repoB = vectors[j];

      // Compute cosine similarity
      const similarity = cosineSimilarity(repoA.vector, repoB.vector);

      // Check if this is a ground truth pair
      const groundTruth = GROUND_TRUTH.find(
        gt => (gt.repoA === repoA.name && gt.repoB === repoB.name) ||
              (gt.repoA === repoB.name && gt.repoB === repoA.name)
      );

      const pair = {
        id: pairs.length + 1,
        repoA: repoA.name,
        repoB: repoB.name,
        vectorA: repoA.vector,
        vectorB: repoB.vector,
        normA: repoA.norm,
        normB: repoB.norm,
        cosineSimilarity: similarity,
        groundTruth: groundTruth || null,
        domain: groundTruth?.domain || 'unknown'
      };

      pairs.push(pair);

      const marker = groundTruth ? '🎯' : '  ';
      console.log(`  ${marker} Pair ${String(pair.id).padStart(2)}: ${repoA.name.padEnd(12)} + ${repoB.name.padEnd(12)} | Similarity: ${(similarity * 100).toFixed(2)}%${groundTruth ? ' [VALIDATED]' : ''}`);
    }
  }

  // Step 3: Save training data
  console.log('\n💾 Saving training data...\n');

  const trainingDataPath = path.join(__dirname, 'training-data');

  // Save vectors
  const vectorsData = {
    generated: new Date().toISOString(),
    repositories: vectors.length,
    vectors: vectors.map(v => ({
      name: v.name,
      path: v.path,
      norm: v.norm,
      components: v.components,
      vector: v.vector
    }))
  };

  fs.writeFileSync(
    path.join(trainingDataPath, 'vectors.json'),
    JSON.stringify(vectorsData, null, 2)
  );
  console.log(`  ✅ Vectors saved: ${vectors.length} repositories`);

  // Save pairs
  const pairsData = {
    generated: new Date().toISOString(),
    totalPairs: pairs.length,
    groundTruthPairs: pairs.filter(p => p.groundTruth).length,
    trainingPairs: pairs.filter(p => !p.groundTruth).length,
    pairs: pairs
  };

  fs.writeFileSync(
    path.join(trainingDataPath, 'pairs.json'),
    JSON.stringify(pairsData, null, 2)
  );
  console.log(`  ✅ Pairs saved: ${pairs.length} total (${pairsData.groundTruthPairs} validated, ${pairsData.trainingPairs} training)`);

  // Save ground truth separately
  const groundTruthData = {
    generated: new Date().toISOString(),
    pairs: pairs.filter(p => p.groundTruth)
  };

  fs.writeFileSync(
    path.join(trainingDataPath, 'ground-truth.json'),
    JSON.stringify(groundTruthData, null, 2)
  );
  console.log(`  ✅ Ground truth saved: ${groundTruthData.pairs.length} validated pairs`);

  // Step 4: Summary statistics
  console.log('\n📊 Training Data Summary');
  console.log('================================================================================');
  console.log(`Repositories analyzed:     ${vectors.length}`);
  console.log(`Total components:          ${vectors.reduce((sum, v) => sum + v.components, 0)}`);
  console.log(`Training pairs generated:  ${pairs.length}`);
  console.log(`  - Ground truth pairs:    ${pairsData.groundTruthPairs} (validated)`);
  console.log(`  - Training pairs:        ${pairsData.trainingPairs} (for learning)`);
  console.log(`\nSimilarity distribution:`);
  console.log(`  - Min:  ${(Math.min(...pairs.map(p => p.cosineSimilarity)) * 100).toFixed(2)}%`);
  console.log(`  - Max:  ${(Math.max(...pairs.map(p => p.cosineSimilarity)) * 100).toFixed(2)}%`);
  console.log(`  - Mean: ${(pairs.reduce((sum, p) => sum + p.cosineSimilarity, 0) / pairs.length * 100).toFixed(2)}%`);

  console.log('\n✅ Training data collection complete!');
  console.log(`📁 Data saved to: ${trainingDataPath}/`);
}

main().catch(console.error);
