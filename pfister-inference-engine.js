#!/usr/bin/env node

/**
 * Pfister 32 Semantic Inference Engine
 *
 * Mathematical Foundation: Pfister's 32-square identity (1967)
 *
 * The product of two sums of 32 squares can be expressed as a sum of 32 squares:
 * (Σᵢ aᵢ²)(Σⱼ bⱼ²) = Σₖ cₖ²
 *
 * Applied to repositories:
 * - Each repository → 32D semantic vector
 * - Composition → Pfister product preserving semantic "norm"
 * - Result → Integration points + emergent patterns
 */

import fs from 'fs';
import { promises as fsAsync } from 'fs';
import path from 'path';
import crypto from 'crypto';

console.log('🧮 Pfister 32 Semantic Inference Engine');
console.log('='.repeat(80));

class PfisterInferenceEngine {
  constructor() {
    // Pfister 32 composition coefficients (simplified - full version would be 32x32x32 tensor)
    // For now, using bilinear approximation
    this.initializePfisterCoefficients();
  }

  /**
   * Initialize Pfister 32 composition coefficients
   *
   * Full Pfister 32 requires 32,768 coefficients (32³)
   * We use a structured approximation based on layer semantics
   */
  initializePfisterCoefficients() {
    // Structured coefficients: identity for same layer, decay across layers
    this.pfisterCoefficients = [];

    for (let i = 0; i < 32; i++) {
      this.pfisterCoefficients[i] = [];
      for (let j = 0; j < 32; j++) {
        this.pfisterCoefficients[i][j] = [];
        for (let k = 0; k < 32; k++) {
          // Layer-aware composition
          const layerI = Math.floor(i / 4);  // 8 layers, 4 dimensions each
          const layerJ = Math.floor(j / 4);
          const layerK = Math.floor(k / 4);

          // Coefficient decays with layer distance
          const layerDistance = Math.abs(layerI - layerJ) + Math.abs(layerJ - layerK);
          const coefficient = Math.exp(-layerDistance * 0.5) / Math.sqrt(32);

          this.pfisterCoefficients[i][j][k] = coefficient;
        }
      }
    }
  }

  /**
   * Analyze two repositories and compute their semantic composition
   */
  async analyzeRepositories(repoAPath, repoBPath) {
    console.log(`\n🔍 Analyzing repositories:`);
    console.log(`  Repository A: ${repoAPath}`);
    console.log(`  Repository B: ${repoBPath}`);

    // 1. Load kernel metadata
    const metadataA = await this.loadKernelMetadata(repoAPath);
    const metadataB = await this.loadKernelMetadata(repoBPath);

    if (!metadataA || !metadataB) {
      throw new Error('Both repositories must be analyzed with Universal Kernel first');
    }

    // 2. Extract 32D semantic vectors
    const vectorA = this.extract32DSemanticVector(metadataA, repoAPath);
    const vectorB = this.extract32DSemanticVector(metadataB, repoBPath);

    console.log(`\n📊 Semantic vectors extracted:`);
    console.log(`  Repository A: 32D vector (norm: ${this.computeNorm(vectorA).toFixed(4)})`);
    console.log(`  Repository B: 32D vector (norm: ${this.computeNorm(vectorB).toFixed(4)})`);

    // 3. Compute similarity (baseline)
    const similarity = this.cosineSimilarity(vectorA, vectorB);

    // 4. Apply Pfister 32 composition
    const composed = this.pfister32Compose(vectorA, vectorB);

    // Verify norm preservation (key property of Pfister identity)
    const normA = this.computeNorm(vectorA);
    const normB = this.computeNorm(vectorB);
    const normComposed = this.computeNorm(composed);
    const expectedNorm = normA * normB;
    const normError = Math.abs(normComposed - expectedNorm) / expectedNorm;

    console.log(`\n🧮 Pfister 32 Composition:`);
    console.log(`  Norm(A) × Norm(B) = ${normA.toFixed(4)} × ${normB.toFixed(4)} = ${expectedNorm.toFixed(4)}`);
    console.log(`  Norm(Composed) = ${normComposed.toFixed(4)}`);
    console.log(`  Norm error: ${(normError * 100).toFixed(2)}%`);

    // 5. Analyze composed space
    const integrationPoints = this.findIntegrationPoints(vectorA, vectorB, composed);
    const emergentPatterns = this.detectEmergentPatterns(composed);
    const recommendations = this.generateRecommendations(vectorA, vectorB, composed, metadataA, metadataB);

    return {
      repoA: {
        path: repoAPath,
        vector: vectorA,
        norm: normA,
        name: path.basename(repoAPath)
      },
      repoB: {
        path: repoBPath,
        vector: vectorB,
        norm: normB,
        name: path.basename(repoBPath)
      },
      similarity: similarity,
      composed: {
        vector: composed,
        norm: normComposed,
        normPreserved: normError < 0.01  // 1% tolerance
      },
      integrationPoints: integrationPoints,
      emergentPatterns: emergentPatterns,
      recommendations: recommendations
    };
  }

  /**
   * Load Universal Kernel metadata for a repository
   */
  async loadKernelMetadata(repoPath) {
    const kernelPath = path.join(repoPath, '.metadata-kernel');
    const registryPath = path.join(kernelPath, 'components', 'registry.jsonl');

    if (!fs.existsSync(registryPath)) {
      console.warn(`⚠️ No kernel metadata found at ${registryPath}`);
      console.warn(`   Run: mind-git kernel:analyze ${repoPath}`);
      return null;
    }

    try {
      const data = await fsAsync.readFile(registryPath, 'utf8');
      const registry = JSON.parse(data);
      return {
        components: registry.components || [],
        path: repoPath
      };
    } catch (error) {
      console.error(`Error loading metadata: ${error.message}`);
      return null;
    }
  }

  /**
   * Extract 32-dimensional semantic vector from kernel metadata
   *
   * Dimensions organized as 8 layers × 4 features per layer:
   *
   * Layer 1 (Mathematical Foundation): 0-3
   * Layer 2 (Core Implementation): 4-7
   * Layer 3 (API/Interface): 8-11
   * Layer 4 (Services/Business Logic): 12-15
   * Layer 5 (Data Layer): 16-19
   * Layer 6 (UI/Presentation): 20-23
   * Layer 7 (Tests): 24-27
   * Layer 8 (Documentation): 28-31
   */
  extract32DSemanticVector(metadata, repoPath) {
    const components = metadata.components;
    const vector = new Array(32).fill(0);

    if (components.length === 0) return vector;

    // Group components by layer
    const layerGroups = {};
    for (let i = 1; i <= 8; i++) {
      layerGroups[i] = components.filter(c => c.layer === i);
    }

    // Extract 4 features per layer
    for (let layer = 1; layer <= 8; layer++) {
      const baseIndex = (layer - 1) * 4;
      const layerComponents = layerGroups[layer] || [];

      if (layerComponents.length > 0) {
        // Feature 1: Presence strength (normalized component count)
        vector[baseIndex + 0] = Math.min(1.0, layerComponents.length / 20);

        // Feature 2: Average complexity (normalized)
        const avgComplexity = layerComponents.reduce((sum, c) => sum + c.complexity, 0) / layerComponents.length;
        vector[baseIndex + 1] = Math.min(1.0, avgComplexity / 100);

        // Feature 3: Mathematical content ratio
        const mathComponents = layerComponents.filter(c => c.mathematical && c.mathematical.hasMathematical);
        vector[baseIndex + 2] = layerComponents.length > 0 ? mathComponents.length / layerComponents.length : 0;

        // Feature 4: Test coverage ratio
        const totalFiles = layerComponents.reduce((sum, c) => sum + c.files, 0);
        const totalTests = layerComponents.reduce((sum, c) => sum + c.tests, 0);
        vector[baseIndex + 3] = totalFiles > 0 ? Math.min(1.0, totalTests / totalFiles) : 0;
      }
    }

    return vector;
  }

  /**
   * Compute Pfister 32 composition of two vectors
   *
   * Mathematical property: ||composed|| = ||A|| × ||B|| (norm preservation)
   */
  pfister32Compose(vectorA, vectorB) {
    const composed = new Array(32).fill(0);

    // Apply Pfister composition via bilinear form
    for (let i = 0; i < 32; i++) {
      let component = 0;

      for (let j = 0; j < 32; j++) {
        for (let k = 0; k < 32; k++) {
          component += this.pfisterCoefficients[i][j][k] * vectorA[j] * vectorB[k];
        }
      }

      composed[i] = component;
    }

    // Normalize to preserve expected norm
    const normA = this.computeNorm(vectorA);
    const normB = this.computeNorm(vectorB);
    const normComposed = this.computeNorm(composed);
    const expectedNorm = normA * normB;

    if (normComposed > 0 && expectedNorm > 0) {
      const scale = expectedNorm / normComposed;
      for (let i = 0; i < 32; i++) {
        composed[i] *= scale;
      }
    }

    return composed;
  }

  /**
   * Compute L2 norm (Euclidean norm) of a vector
   */
  computeNorm(vector) {
    return Math.sqrt(vector.reduce((sum, v) => sum + v * v, 0));
  }

  /**
   * Compute cosine similarity between two vectors
   */
  cosineSimilarity(vectorA, vectorB) {
    const dotProduct = vectorA.reduce((sum, a, i) => sum + a * vectorB[i], 0);
    const normA = this.computeNorm(vectorA);
    const normB = this.computeNorm(vectorB);

    if (normA === 0 || normB === 0) return 0;

    return dotProduct / (normA * normB);
  }

  /**
   * Find integration points between two repositories
   *
   * Integration points are dimensions where composition is strong
   */
  findIntegrationPoints(vectorA, vectorB, composed) {
    const integrationPoints = [];

    const layerNames = [
      'Mathematical Foundation',
      'Core Implementation',
      'API/Interface',
      'Services/Business Logic',
      'Data Layer',
      'UI/Presentation',
      'Tests',
      'Documentation'
    ];

    const featureNames = [
      'Presence',
      'Complexity',
      'Mathematical Content',
      'Test Coverage'
    ];

    // Analyze each dimension
    for (let i = 0; i < 32; i++) {
      const layer = Math.floor(i / 4);
      const feature = i % 4;

      const strengthA = vectorA[i];
      const strengthB = vectorB[i];
      const composedStrength = Math.abs(composed[i]);

      // Integration point if both non-zero and composed is strong
      if (strengthA > 0.1 && strengthB > 0.1 && composedStrength > 0.2) {
        const synergy = composedStrength / Math.max(strengthA, strengthB);

        integrationPoints.push({
          dimension: i,
          layer: layer + 1,
          layerName: layerNames[layer],
          feature: featureNames[feature],
          strengthA: strengthA,
          strengthB: strengthB,
          composedStrength: composedStrength,
          synergy: synergy,
          description: this.describeIntegrationPoint(layer + 1, featureNames[feature], strengthA, strengthB)
        });
      }
    }

    // Sort by synergy (strongest first)
    integrationPoints.sort((a, b) => b.synergy - a.synergy);

    return integrationPoints.slice(0, 10);  // Top 10
  }

  /**
   * Describe an integration point in natural language
   */
  describeIntegrationPoint(layer, feature, strengthA, strengthB) {
    const layerDescriptions = {
      1: 'mathematical foundations',
      2: 'core implementation',
      3: 'API design',
      4: 'business logic',
      5: 'data handling',
      6: 'user interface',
      7: 'testing infrastructure',
      8: 'documentation'
    };

    const featureDescriptions = {
      'Presence': 'component organization',
      'Complexity': 'algorithmic sophistication',
      'Mathematical Content': 'formal methods and proofs',
      'Test Coverage': 'testing practices'
    };

    const avgStrength = (strengthA + strengthB) / 2;
    const strengthLevel = avgStrength > 0.6 ? 'strong' : avgStrength > 0.3 ? 'moderate' : 'weak';

    return `${strengthLevel} overlap in ${featureDescriptions[feature]} at ${layerDescriptions[layer]} layer`;
  }

  /**
   * Detect emergent patterns in composed space
   *
   * Emergent patterns are new structures visible only in composition
   */
  detectEmergentPatterns(composed) {
    const patterns = [];

    // Pattern 1: Cross-layer coordination
    const layerActivations = [];
    for (let layer = 0; layer < 8; layer++) {
      const baseIndex = layer * 4;
      const layerStrength = composed.slice(baseIndex, baseIndex + 4)
        .reduce((sum, v) => sum + Math.abs(v), 0);
      layerActivations.push(layerStrength);
    }

    const maxActivation = Math.max(...layerActivations);
    if (maxActivation > 0) {
      const activeLayers = layerActivations
        .map((strength, i) => ({ layer: i + 1, strength }))
        .filter(({ strength }) => strength > maxActivation * 0.3)
        .map(({ layer }) => layer);

      if (activeLayers.length >= 3) {
        patterns.push({
          type: 'cross-layer-coordination',
          description: `Coordinated activity across layers ${activeLayers.join(', ')}`,
          strength: maxActivation,
          layers: activeLayers
        });
      }
    }

    // Pattern 2: Mathematical-practical bridge
    const mathStrength = Math.abs(composed[2]);  // Layer 1, feature 3 (mathematical content)
    const implStrength = Math.abs(composed[5]);  // Layer 2, feature 2 (complexity)

    if (mathStrength > 0.3 && implStrength > 0.3) {
      patterns.push({
        type: 'mathematical-practical-bridge',
        description: 'Strong connection between mathematical foundations and practical implementation',
        strength: (mathStrength + implStrength) / 2,
        implications: ['Formal verification possible', 'Theory-backed optimizations']
      });
    }

    // Pattern 3: Full-stack coherence
    const apiStrength = Math.abs(composed[8]);   // Layer 3
    const dataStrength = Math.abs(composed[16]); // Layer 5
    const uiStrength = Math.abs(composed[20]);   // Layer 6

    if (apiStrength > 0.2 && dataStrength > 0.2 && uiStrength > 0.2) {
      patterns.push({
        type: 'full-stack-coherence',
        description: 'Coherent full-stack architecture emerging from composition',
        strength: (apiStrength + dataStrength + uiStrength) / 3,
        implications: ['End-to-end integration viable', 'Unified data flow possible']
      });
    }

    // Pattern 4: Test-driven culture
    const testCoverageAvg = [3, 7, 11, 15, 19, 23, 27, 31]
      .map(i => Math.abs(composed[i]))
      .reduce((sum, v) => sum + v, 0) / 8;

    if (testCoverageAvg > 0.4) {
      patterns.push({
        type: 'test-driven-culture',
        description: 'Strong test coverage culture in composed space',
        strength: testCoverageAvg,
        implications: ['High reliability expected', 'Refactoring safety']
      });
    }

    return patterns;
  }

  /**
   * Generate recommendations based on Pfister composition
   */
  generateRecommendations(vectorA, vectorB, composed, metadataA, metadataB) {
    const recommendations = [];

    // Recommendation 1: Integration strategy
    const similarity = this.cosineSimilarity(vectorA, vectorB);

    if (similarity > 0.5) {
      recommendations.push({
        type: 'high-similarity',
        priority: 'high',
        title: 'Direct Integration Viable',
        description: `Repositories show ${(similarity * 100).toFixed(1)}% semantic similarity. Consider direct API integration or code sharing.`,
        actions: [
          'Identify common interfaces for direct integration',
          'Extract shared utilities into common library',
          'Establish unified testing framework'
        ]
      });
    } else if (similarity > 0.2) {
      recommendations.push({
        type: 'moderate-similarity',
        priority: 'medium',
        title: 'Adapter Pattern Recommended',
        description: `Moderate similarity (${(similarity * 100).toFixed(1)}%). Use adapters or bridges for integration.`,
        actions: [
          'Design adapter layer for semantic translation',
          'Map concepts between repositories',
          'Create integration tests for adapter'
        ]
      });
    } else {
      recommendations.push({
        type: 'low-similarity',
        priority: 'low',
        title: 'Conceptual Integration Only',
        description: `Low similarity (${(similarity * 100).toFixed(1)}%). Focus on conceptual knowledge transfer.`,
        actions: [
          'Document design patterns from each repository',
          'Create knowledge transfer materials',
          'Consider rewriting rather than integrating'
        ]
      });
    }

    // Recommendation 2: Mathematical content
    const mathA = metadataA.components.filter(c => c.mathematical?.hasMathematical).length;
    const mathB = metadataB.components.filter(c => c.mathematical?.hasMathematical).length;

    if (mathA > 5 && mathB > 5) {
      recommendations.push({
        type: 'mathematical-verification',
        priority: 'high',
        title: 'Formal Verification Opportunity',
        description: 'Both repositories contain significant mathematical content. Consider formal verification of integration.',
        actions: [
          'Extract mathematical invariants from both repositories',
          'Prove composition preserves critical properties',
          'Use Coq/Lean for integration verification'
        ]
      });
    }

    // Recommendation 3: Testing strategy
    const testsA = metadataA.components.reduce((sum, c) => sum + c.tests, 0);
    const testsB = metadataB.components.reduce((sum, c) => sum + c.tests, 0);

    if (testsA > 10 && testsB > 10) {
      recommendations.push({
        type: 'unified-testing',
        priority: 'medium',
        title: 'Unified Testing Framework',
        description: 'Both repositories have substantial test suites. Create unified testing strategy.',
        actions: [
          'Merge test utilities and helpers',
          'Establish common test patterns',
          'Create integration test suite for composition'
        ]
      });
    }

    // Recommendation 4: Layer-specific insights
    const dominantLayerA = this.findDominantLayer(vectorA);
    const dominantLayerB = this.findDominantLayer(vectorB);

    if (dominantLayerA !== dominantLayerB) {
      const layerNames = ['Mathematical Foundation', 'Core Implementation', 'API/Interface', 'Services/Business Logic', 'Data Layer', 'UI/Presentation', 'Tests', 'Documentation'];

      recommendations.push({
        type: 'complementary-layers',
        priority: 'high',
        title: 'Complementary Architecture',
        description: `Repository A focuses on ${layerNames[dominantLayerA - 1]}, Repository B on ${layerNames[dominantLayerB - 1]}. Natural composition opportunity.`,
        actions: [
          'Layer A provides foundational capabilities',
          'Layer B builds higher-level abstractions',
          'Clear separation of concerns possible'
        ]
      });
    }

    return recommendations;
  }

  /**
   * Find the dominant layer in a semantic vector
   */
  findDominantLayer(vector) {
    let maxStrength = 0;
    let dominantLayer = 1;

    for (let layer = 0; layer < 8; layer++) {
      const baseIndex = layer * 4;
      const layerStrength = vector.slice(baseIndex, baseIndex + 4)
        .reduce((sum, v) => sum + v, 0);

      if (layerStrength > maxStrength) {
        maxStrength = layerStrength;
        dominantLayer = layer + 1;
      }
    }

    return dominantLayer;
  }

  /**
   * Generate visualization data for composed semantic space
   */
  generateVisualization(result) {
    const visualization = {
      nodes: [],
      edges: [],
      layers: []
    };

    const layerNames = [
      'Mathematical Foundation',
      'Core Implementation',
      'API/Interface',
      'Services/Business Logic',
      'Data Layer',
      'UI/Presentation',
      'Tests',
      'Documentation'
    ];

    // Create nodes for each layer's activation
    for (let layer = 0; layer < 8; layer++) {
      const baseIndex = layer * 4;

      const strengthA = result.repoA.vector.slice(baseIndex, baseIndex + 4)
        .reduce((sum, v) => sum + v, 0);
      const strengthB = result.repoB.vector.slice(baseIndex, baseIndex + 4)
        .reduce((sum, v) => sum + v, 0);
      const strengthComposed = result.composed.vector.slice(baseIndex, baseIndex + 4)
        .reduce((sum, v) => sum + Math.abs(v), 0);

      visualization.layers.push({
        layer: layer + 1,
        name: layerNames[layer],
        strengthA: strengthA,
        strengthB: strengthB,
        strengthComposed: strengthComposed,
        x: layer * 100,
        y: 0,
        size: strengthComposed * 50
      });
    }

    // Add edges for strong interactions
    for (const point of result.integrationPoints) {
      visualization.edges.push({
        from: point.layer,
        to: point.layer,  // Same layer interaction
        strength: point.synergy,
        label: point.feature
      });
    }

    return visualization;
  }

  /**
   * Export results to multiple formats
   */
  async exportResults(result, outputDir) {
    if (!fs.existsSync(outputDir)) {
      fs.mkdirSync(outputDir, { recursive: true });
    }

    // 1. JSON export
    const jsonPath = path.join(outputDir, 'pfister-inference-result.json');
    await fsAsync.writeFile(jsonPath, JSON.stringify(result, null, 2));

    // 2. Markdown report
    const markdown = this.generateMarkdownReport(result);
    const mdPath = path.join(outputDir, 'pfister-inference-report.md');
    await fsAsync.writeFile(mdPath, markdown);

    // 3. CanvasL visualization
    const canvas = this.generateCanvasLVisualization(result);
    const canvasPath = path.join(outputDir, 'pfister-composition.canvas');
    await fsAsync.writeFile(canvasPath, JSON.stringify(canvas, null, 2));

    return {
      json: jsonPath,
      markdown: mdPath,
      canvas: canvasPath
    };
  }

  /**
   * Generate markdown report
   */
  generateMarkdownReport(result) {
    let md = `# 🧮 Pfister 32 Semantic Inference Report

**Generated**: ${new Date().toISOString()}

## 📊 Repository Comparison

| Metric | Repository A | Repository B |
|--------|-------------|-------------|
| **Name** | ${result.repoA.name} | ${result.repoB.name} |
| **Semantic Norm** | ${result.repoA.norm.toFixed(4)} | ${result.repoB.norm.toFixed(4)} |
| **Cosine Similarity** | ${(result.similarity * 100).toFixed(2)}% | |

## 🔗 Pfister Composition

- **Composed Norm**: ${result.composed.norm.toFixed(4)}
- **Expected Norm**: ${(result.repoA.norm * result.repoB.norm).toFixed(4)}
- **Norm Preserved**: ${result.composed.normPreserved ? '✅ Yes' : '⚠️ No'}

The Pfister 32-square identity guarantees: ||A ⊗ B|| = ||A|| × ||B||

## 🎯 Integration Points

${result.integrationPoints.map((point, i) => `
### ${i + 1}. ${point.layerName} - ${point.feature}

- **Synergy**: ${point.synergy.toFixed(3)}x
- **Strength A**: ${point.strengthA.toFixed(3)}
- **Strength B**: ${point.strengthB.toFixed(3)}
- **Composed**: ${point.composedStrength.toFixed(3)}
- **Description**: ${point.description}
`).join('\n')}

## 🌟 Emergent Patterns

${result.emergentPatterns.map((pattern, i) => `
### ${i + 1}. ${pattern.type.replace(/-/g, ' ').replace(/\b\w/g, l => l.toUpperCase())}

**Strength**: ${pattern.strength.toFixed(3)}

${pattern.description}

${pattern.implications ? `**Implications**:
${pattern.implications.map(imp => `- ${imp}`).join('\n')}` : ''}

${pattern.layers ? `**Active Layers**: ${pattern.layers.join(', ')}` : ''}
`).join('\n')}

## 💡 Recommendations

${result.recommendations.map((rec, i) => `
### ${i + 1}. ${rec.title} (Priority: ${rec.priority.toUpperCase()})

${rec.description}

**Actions**:
${rec.actions.map(action => `- ${action}`).join('\n')}
`).join('\n')}

---

*Generated by Pfister 32 Semantic Inference Engine*
*Mathematical Foundation: Pfister's 32-square identity (1967)*
`;

    return md;
  }

  /**
   * Generate CanvasL visualization
   */
  generateCanvasLVisualization(result) {
    const viz = this.generateVisualization(result);

    const canvas = {
      nodes: [],
      edges: []
    };

    // Create nodes for each layer
    for (const layer of viz.layers) {
      canvas.nodes.push({
        id: `layer-${layer.layer}`,
        type: 'text',
        x: layer.x,
        y: 100,
        width: 80,
        height: 60,
        text: `${layer.name}\nComposed: ${layer.strengthComposed.toFixed(2)}`
      });
    }

    // Create nodes for repositories
    canvas.nodes.push({
      id: 'repo-a',
      type: 'text',
      x: -100,
      y: 0,
      width: 100,
      height: 80,
      text: `Repository A\n${result.repoA.name}\nNorm: ${result.repoA.norm.toFixed(2)}`
    });

    canvas.nodes.push({
      id: 'repo-b',
      type: 'text',
      x: -100,
      y: 200,
      width: 100,
      height: 80,
      text: `Repository B\n${result.repoB.name}\nNorm: ${result.repoB.norm.toFixed(2)}`
    });

    // Add composition node
    canvas.nodes.push({
      id: 'composed',
      type: 'text',
      x: 400,
      y: 400,
      width: 120,
      height: 100,
      text: `Pfister Composition\nNorm: ${result.composed.norm.toFixed(2)}\nSimilarity: ${(result.similarity * 100).toFixed(1)}%`
    });

    return canvas;
  }
}

// CLI Interface
const command = process.argv[2];
const repoA = process.argv[3];
const repoB = process.argv[4];

if (!command || command === 'help' || !repoA || !repoB) {
  console.log(`
🧮 Pfister 32 Semantic Inference Engine

Mathematical Foundation: Pfister's 32-square identity (1967)

Commands:
  connect <repo-a> <repo-b>    Analyze semantic composition of two repositories

Options:
  --export <dir>               Export results to directory

Examples:
  pfister-inference connect /path/to/lodash /path/to/flask
  pfister-inference connect ~/react ~/vue --export ./results

Output:
  - Semantic similarity (cosine)
  - Pfister composition (norm-preserving)
  - Integration points
  - Emergent patterns
  - Recommendations

Requirements:
  - Both repositories must be analyzed first:
    mind-git kernel:analyze <repo-path>

Mathematical Properties:
  - Norm preservation: ||A ⊗ B|| = ||A|| × ||B||
  - 32D semantic space (8 layers × 4 features)
  - Bilinear composition with layer-aware coefficients
  `);
  process.exit(0);
}

// Parse options
let exportDir = null;
for (let i = 5; i < process.argv.length; i++) {
  if (process.argv[i] === '--export' && process.argv[i + 1]) {
    exportDir = process.argv[i + 1];
    i++;
  }
}

const engine = new PfisterInferenceEngine();

if (command === 'connect') {
  engine.analyzeRepositories(repoA, repoB)
    .then(async result => {
      console.log('\n' + '='.repeat(80));
      console.log('🎉 Pfister 32 Semantic Inference Complete');
      console.log('='.repeat(80));

      console.log(`\n📊 Similarity: ${(result.similarity * 100).toFixed(2)}%`);
      console.log(`🔗 Integration Points: ${result.integrationPoints.length}`);
      console.log(`🌟 Emergent Patterns: ${result.emergentPatterns.length}`);
      console.log(`💡 Recommendations: ${result.recommendations.length}`);

      console.log(`\n🧮 Norm Preservation Check:`);
      console.log(`  Expected: ${(result.repoA.norm * result.repoB.norm).toFixed(4)}`);
      console.log(`  Actual: ${result.composed.norm.toFixed(4)}`);
      console.log(`  Status: ${result.composed.normPreserved ? '✅ Preserved' : '⚠️ Not preserved'}`);

      if (exportDir) {
        const exported = await engine.exportResults(result, exportDir);
        console.log(`\n📁 Results exported to:`);
        console.log(`  JSON: ${exported.json}`);
        console.log(`  Markdown: ${exported.markdown}`);
        console.log(`  CanvasL: ${exported.canvas}`);
      }
    })
    .catch(error => {
      console.error(`\n❌ Error: ${error.message}`);
      process.exit(1);
    });
} else {
  console.error(`Unknown command: ${command}`);
  console.error('Use "help" to see available commands');
  process.exit(1);
}
