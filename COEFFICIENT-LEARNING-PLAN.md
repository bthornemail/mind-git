# 🧮 Pfister 32 Coefficient Learning Plan

**Date**: December 15, 2025
**Status**: Phase 2 - In Progress
**Objective**: Learn optimal Pfister coefficients from repository corpus

---

## 🎯 Objectives

### Primary Goals

1. **Learn Optimal Coefficients**: Replace hand-crafted layer-aware coefficients with learned ones
2. **Improve Accuracy**: Enhance similarity predictions and pattern detection
3. **Validate Improvement**: Prove learned coefficients outperform hand-crafted ones
4. **Maintain Guarantees**: Preserve norm preservation property

### Success Criteria

- ✅ Coefficient tensor learned from corpus (32³ = 32,768 coefficients)
- ✅ Norm preservation maintained (<1% error)
- ✅ Improved similarity accuracy vs hand-crafted baseline
- ✅ Cross-validation performance documented
- ✅ Production-ready learned coefficients

---

## 📊 Training Data

### Available Repository Corpus

We have 10 repositories already analyzed:
1. React (539 components)
2. Vue (80 components)
3. Express (41 components)
4. FastAPI (316 components)
5. TensorFlow (1059 components)
6. PyTorch (993 components)
7. Webpack (838 components)
8. Vite (515 components)
9. Redis (43 components)
10. PostgreSQL (287 components)

**Total**: 4,711 components across 10 repositories

### Training Pairs

All combinations of 10 repositories: **C(10,2) = 45 pairs**

Already validated: 5 pairs
Additional pairs available: 40 pairs

**Training strategy**:
- Use 5 validated pairs as ground truth
- Generate 35 additional pairs for training
- Reserve 5 pairs for validation

---

## 🏗️ Architecture

### Coefficient Learning System

```
Training Data → Feature Extraction → Optimization → Validation → Production
     ↓                  ↓                  ↓              ↓            ↓
  45 pairs      32D vectors × 2    Gradient Descent   5-fold CV   Deploy
```

### Components to Build

1. **Training Data Collector**: Extract 32D vectors from all 10 repos
2. **Pair Generator**: Create all 45 combinations with semantic vectors
3. **Coefficient Optimizer**: Learn optimal 32³ coefficient tensor
4. **Validator**: Cross-validation and performance metrics
5. **Updater**: Replace hand-crafted coefficients in Pfister engine

---

## 🧮 Learning Algorithm

### Objective Function

Minimize the error between predicted and observed similarity while preserving norms:

```
Loss = α × SimilarityError + β × NormError

where:
- SimilarityError = Σ (predicted_similarity - observed_similarity)²
- NormError = Σ (||A ⊗ B|| - ||A|| × ||B||)²
- α = 1.0 (similarity weight)
- β = 1000.0 (norm preservation is critical)
```

### Constraints

1. **Norm Preservation**: ||A ⊗ B|| = ||A|| × ||B|| (hard constraint)
2. **Symmetry**: c[i,j,k] = c[j,i,k] (bilinear form symmetry)
3. **Bounded**: c[i,j,k] ∈ [-1, 1] (prevent explosive growth)

### Optimization Method

**Gradient Descent with Constraints**:
- Initial coefficients: Current hand-crafted layer-aware values
- Learning rate: 0.01 (with decay)
- Batch size: All 45 pairs (full batch)
- Epochs: 1000 (with early stopping)
- Constraint enforcement: Project to feasible set after each step

---

## 📈 Evaluation Metrics

### Performance Metrics

1. **Similarity MAE** (Mean Absolute Error): |predicted - observed|
2. **Norm Preservation Error**: |composed_norm - expected_norm|
3. **Pattern Detection Accuracy**: Do emergent patterns still appear?
4. **Recommendation Quality**: Human evaluation of actionability

### Baseline (Hand-Crafted Coefficients)

From validation:
- Similarity range: 61.05% - 89.97%
- Norm error: 0.00% (all pairs)
- Patterns detected: 4 per pair (consistent)
- Recommendation quality: 4.46/5.0

### Target (Learned Coefficients)

- Similarity predictions: <5% MAE
- Norm error: <0.1% (maintain guarantee)
- Patterns detected: ≥4 per pair
- Recommendation quality: ≥4.5/5.0

---

## 🔧 Implementation Plan

### Step 1: Training Data Collection (Day 1)

**Build**: `coefficient-learning/01-collect-training-data.js`

```javascript
// Extract all 32D vectors from 10 repositories
const trainingData = [];
for (const repo of repositories) {
  const metadata = loadKernelMetadata(repo);
  const vector = extract32DVector(metadata);
  trainingData.push({ repo, vector });
}

// Generate all 45 pairs
const pairs = [];
for (let i = 0; i < repos.length; i++) {
  for (let j = i + 1; j < repos.length; j++) {
    pairs.push({
      repoA: repos[i],
      repoB: repos[j],
      vectorA: trainingData[i].vector,
      vectorB: trainingData[j].vector
    });
  }
}
```

### Step 2: Coefficient Optimization (Day 2-3)

**Build**: `coefficient-learning/02-optimize-coefficients.js`

```javascript
// Initialize with hand-crafted coefficients
let coefficients = initializeLayerAwareCoefficients();

// Gradient descent with norm preservation
for (let epoch = 0; epoch < 1000; epoch++) {
  let totalLoss = 0;

  for (const pair of pairs) {
    // Forward pass
    const composed = pfisterCompose(pair.vectorA, pair.vectorB, coefficients);
    const similarity = cosineSimilarity(pair.vectorA, pair.vectorB);

    // Compute loss
    const similarityError = computeSimilarityError(composed, similarity);
    const normError = computeNormError(composed, pair.vectorA, pair.vectorB);
    const loss = 1.0 * similarityError + 1000.0 * normError;

    // Backward pass (gradient)
    const gradients = computeGradients(loss, coefficients);

    // Update coefficients
    coefficients = updateWithConstraints(coefficients, gradients, learningRate);

    totalLoss += loss;
  }

  // Early stopping
  if (totalLoss < threshold) break;
}
```

### Step 3: Cross-Validation (Day 4)

**Build**: `coefficient-learning/03-cross-validate.js`

5-fold cross-validation:
- Split 45 pairs into 5 folds (9 pairs each)
- Train on 4 folds, validate on 1 fold
- Repeat 5 times, average results

### Step 4: Comparison & Analysis (Day 5)

**Build**: `coefficient-learning/04-compare-results.js`

Compare learned vs hand-crafted:
- Similarity prediction accuracy
- Norm preservation quality
- Pattern detection consistency
- Recommendation actionability

### Step 5: Production Integration (Day 6)

**Update**: `pfister-inference-engine.js`

Replace `generateLayerAwareCoefficients()` with learned coefficients:

```javascript
// Load learned coefficients from training
const LEARNED_COEFFICIENTS = loadLearnedCoefficients();

// Use in Pfister composition
pfister32Compose(vectorA, vectorB) {
  const composed = new Array(32).fill(0);
  for (let i = 0; i < 32; i++) {
    for (let j = 0; j < 32; j++) {
      for (let k = 0; k < 32; k++) {
        composed[i] += LEARNED_COEFFICIENTS[i][j][k] * vectorA[j] * vectorB[k];
      }
    }
  }
  return composed;
}
```

---

## 📊 Expected Outcomes

### Best Case

- Learned coefficients improve similarity predictions by 10-20%
- Norm preservation maintained (<0.1% error)
- New emergent patterns discovered
- Recommendation quality improves to 4.8/5.0

### Acceptable Case

- Learned coefficients match hand-crafted performance
- Norm preservation maintained (<0.5% error)
- Same patterns detected
- Recommendation quality maintained at 4.46/5.0

### Requires Adjustment

- Learned coefficients worse than hand-crafted
- Norm preservation degraded (>1% error)
- Pattern detection fails
- Need to adjust learning algorithm or constraints

---

## 🚀 Next Steps After Coefficient Learning

### If Successful (Learned > Hand-Crafted)

1. **Deploy Learned Coefficients**: Update production Pfister engine
2. **Expand Corpus**: Clone 40 more repositories for better learning
3. **Continuous Learning**: Periodic retraining as corpus grows

### If Equivalent (Learned ≈ Hand-Crafted)

1. **Document Findings**: Hand-crafted coefficients are optimal
2. **Skip Learning**: Use hand-crafted in production
3. **Move to Multi-Repo**: Focus on N-way composition

### If Failed (Learned < Hand-Crafted)

1. **Analyze Failure**: Why did learning fail?
2. **Adjust Algorithm**: Try different optimization methods
3. **Keep Hand-Crafted**: Maintain current approach

---

## 📁 Directory Structure

```
coefficient-learning/
├── 01-collect-training-data.js      # Extract vectors from 10 repos
├── 02-optimize-coefficients.js      # Gradient descent optimizer
├── 03-cross-validate.js             # 5-fold cross-validation
├── 04-compare-results.js            # Learned vs hand-crafted
├── 05-production-update.js          # Deploy to Pfister engine
├── training-data/
│   ├── vectors.json                 # 32D vectors for all repos
│   ├── pairs.json                   # All 45 pairs
│   └── ground-truth.json            # 5 validated pairs
├── learned-coefficients/
│   ├── coefficients-epoch-*.json    # Checkpoints
│   └── final-coefficients.json      # Production coefficients
└── results/
    ├── training-loss.csv            # Loss over epochs
    ├── cross-validation.json        # CV results
    └── comparison-report.md         # Final comparison
```

---

## 🎯 Timeline

**Week 1**: Coefficient Learning Implementation
- Day 1: Training data collection
- Day 2-3: Optimization algorithm
- Day 4: Cross-validation
- Day 5: Comparison & analysis
- Day 6: Production integration
- Day 7: Documentation

**Week 2**: Corpus Expansion (if successful)
- Clone 40 additional repositories
- Retrain with larger corpus
- Validate improvement

---

## 🔬 Research Questions

1. **Coefficient Structure**: Do learned coefficients show interpretable patterns?
2. **Layer Importance**: Which layers dominate the learned coefficients?
3. **Sparsity**: Are most coefficients near zero? Can we prune?
4. **Transferability**: Do coefficients learned on one domain transfer to others?

---

**Status**: Ready to begin implementation
**Next Step**: Build training data collector

---

*This coefficient learning plan follows the grounded approach: use existing validated data, measure improvements, maintain mathematical guarantees.*
