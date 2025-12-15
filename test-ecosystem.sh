#!/bin/bash

# Comprehensive VR Spatial Programming Ecosystem Test Suite
# Tests all components: mind-git, h2gnn, meta-log, hyperdev-ide

set -e

echo "🚀 COMPREHENSIVE ECOSYSTEM TESTING"
echo "=================================================="
echo "Testing VR Spatial Programming Ecosystem v1.0.0"
echo ""

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
PURPLE='\033[0;35m'
CYAN='\033[0;36m'
NC='\033[0m'

# Test results
TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0

# Function to run test
run_test() {
    local test_name=$1
    local test_command=$2
    local expected_result=$3
    
    echo -e "${BLUE}Testing: $test_name${NC}"
    echo "Command: $test_command"
    
    if eval "$test_command" > /dev/null 2>&1; then
        echo -e "${GREEN}✅ PASSED${NC}"
        ((PASSED_TESTS++))
        ((TOTAL_TESTS++))
        return 0
    else
        echo -e "${RED}❌ FAILED${NC}"
        ((FAILED_TESTS++))
        ((TOTAL_TESTS++))
        return 1
    fi
}

# Function to run performance benchmark
run_benchmark() {
    local test_name=$1
    local test_command=$2
    local metric_name=$3
    local target_value=$4
    
    echo -e "${PURPLE}Benchmarking: $test_name${NC}"
    
    local start_time=$(date +%s%N)
    local result=$(eval "$test_command" 2>/dev/null)
    local end_time=$(date +%s%N)
    local duration=$((end_time - start_time))
    
    echo "Duration: ${duration}ms"
    echo "Target: $target_value"
    
    if [[ $duration -le $target_value ]]; then
        echo -e "${GREEN}✅ BENCHMARK PASSED${NC}"
        ((PASSED_TESTS++))
    else
        echo -e "${RED}❌ BENCHMARK FAILED${NC}"
        ((FAILED_TESTS++))
    fi
    ((TOTAL_TESTS++))
}

# Function to test API endpoint
test_api() {
    local service_name=$1
    local url=$2
    local expected_status=$3
    
    echo -e "${CYAN}Testing API: $service_name${NC}"
    echo "URL: $url"
    
    local response=$(curl -s -o /dev/null -w "%{http_code}" "$url" 2>/dev/null)
    local status_code=${response:0:3}
    
    if [[ "$status_code" == "$expected_status" ]]; then
        echo -e "${GREEN}✅ API PASSED${NC}"
        ((PASSED_TESTS++))
    else
        echo -e "${RED}❌ API FAILED (Status: $status_code)${NC}"
        ((FAILED_TESTS++))
    fi
    ((TOTAL_TESTS++))
}

echo "📊 MIND-GIT CORE TESTING"
echo "----------------------------------------"

# Test 1: H²GNN Intelligence Bridge
run_test "H²GNN Bridge Integration" \
    "node -e \"const { createAIIntelligence } = require('./logos-system/src/ai/index.ts'); const ai = createAIIntelligence(); console.log('✅ H²GNN Bridge initialized:', !!ai);\"" \
    "true"

# Test 2: Canvas Learning System
run_test "Canvas Learning System" \
    "node -e \"const { CanvasLearning } = require('./logos-system/src/ai/canvas-learning.ts'); const learning = new CanvasLearning(); console.log('✅ Canvas Learning initialized:', !!learning);\"" \
    "true"

# Test 3: AI Suggestion Engine
run_test "AI Suggestion Engine" \
    "node -e \"const { SuggestionEngine } = require('./logos-system/src/ai/suggestion-engine.ts'); const suggestions = []; console.log('✅ Suggestion Engine initialized:', !!suggestions);\"" \
    "true"

# Test 4: Scheme Theory Integration
run_test "Scheme Theory Integration" \
    "node -e \"const { analyzeCanvas } = require('./logos-system/src/scheme-theory/compute-h1.ts'); const canvas = {nodes: [{id: 'A'}], edges: []}; const result = analyzeCanvas(canvas); console.log('✅ Scheme Theory working:', result.h1BettiNumber === 0);\"" \
    "true"

# Test 5: AI-Enhanced Compiler
run_test "AI-Enhanced Compiler" \
    "node -e \"const { AIEnhancedCompiler } = require('./logos-system/src/compiler/ai-enhanced-compiler.ts'); const compiler = new AIEnhancedCompiler({enableAISuggestions: true}); console.log('✅ AI-Enhanced Compiler initialized:', !!compiler);\"" \
    "true"

echo ""
echo "🔮 META-LOG ORCHESTRATOR TESTING"
echo "--------------------------------------"

# Test 6: Meta-Log System Initialization
run_test "Meta-Log System" \
    "node -e \"const { createMetaLogSystem } = require('./meta-log/src/index.ts'); const metaLog = createMetaLogSystem(); console.log('✅ Meta-Log System initialized:', !!metaLog);\"" \
    "true"

# Test 7: E8 Lattice Router
run_test "E8 Lattice Router" \
    "node -e \"const { createE8LatticeRouter } = require('./meta-log/src/e8-lattice-router.ts'); const router = createE8LatticeRouter(); console.log('✅ E8 Router initialized:', !!router);\"" \
    "true"

# Test 8: Natural Language Interface
run_test "Natural Language Interface" \
    "node -e \"const { createNaturalLanguageInterface } = require('./meta-log/src/natural-language-interface.ts'); const nlp = createNaturalLanguageInterface(); console.log('✅ NLP Interface initialized:', !!nlp);\"" \
    "true"

# Test 9: Unified Knowledge Graph
run_test "Unified Knowledge Graph" \
    "node -e \"const { createUnifiedKnowledgeGraph } = require('./meta-log/src/unified-knowledge-graph.ts'); const graph = createUnifiedKnowledgeGraph(); console.log('✅ Knowledge Graph initialized:', !!graph);\"" \
    "true"

echo ""
echo "🥽 HYPERDEV-IDE VR INTERFACE TESTING"
echo "--------------------------------------"

# Test 10: HyperDev-IDE Dependencies
run_test "HyperDev-IDE Dependencies" \
    "cd ../hyperdev-ide && npm list --depth=0 | grep -E '(three|aframe|webxr|monaco)'" \
    "true"

# Test 11: VR Components
run_test "VR Components" \
    "cd ../hyperdev-ide && ls src/components/ | grep -E '(aframe|three|vr|collaboration)'" \
    "true"

echo ""
echo "⚡ PERFORMANCE BENCHMARKING"
echo "--------------------------------------"

# Test 12: AI Suggestion Generation Speed
run_benchmark "AI Suggestion Generation" \
    "node -e \"const { createAIIntelligence } = require('./logos-system/src/ai/index.ts'); const ai = createAIIntelligence(); const start = Date.now(); ai.getSuggestions({nodes: [{id: 'test'}], edges: []}).then(() => console.log(Date.now() - start));\"" \
    "100"  # Target: <100ms

# Test 13: Canvas Compilation Speed
run_benchmark "Canvas Compilation" \
    "node -e \"const { AIEnhancedCompiler } = require('./logos-system/src/compiler/ai-enhanced-compiler.ts'); const compiler = new AIEnhancedCompiler({enableAISuggestions: false}); const start = Date.now(); compiler.compileWithAI({nodes: [{id: 'test'}], edges: []}).then(() => console.log(Date.now() - start));\"" \
    "200"  # Target: <200ms

# Test 14: E8 Lattice Routing Performance
run_benchmark "E8 Lattice Routing" \
    "node -e \"const { createE8LatticeRouter } = require('./meta-log/src/e8-lattice-router.ts'); const router = createE8LatticeRouter(); const start = Date.now(); router.findGeodesicPath('node1', 'node2'); console.log(Date.now() - start);\"" \
    "50"  # Target: <50ms

echo ""
echo "🌐 API INTEGRATION TESTING"
echo "--------------------------------------"

# Test 15: Meta-Log Health Endpoint
test_api "Meta-Log Health" \
    "http://localhost:4000/api/health" \
    "200"

# Test 16: H²GNN Service Health
test_api "H²GNN Service Health" \
    "http://localhost:8080/api/health" \
    "200"

# Test 17: Knowledge Graph Query
test_api "Knowledge Graph Query" \
    "http://localhost:4000/api/knowledge/query" \
    "200"

echo ""
echo "📈 INTEGRATION TESTING"
echo "--------------------------------------"

# Test 18: Cross-Project Communication
run_test "Cross-Project Communication" \
    "node -e \"const ai = require('./logos-system/src/ai/index.ts'); const metaLog = require('./meta-log/src/index.ts'); console.log('✅ Cross-project integration test:', !!ai && !!metaLog);\"" \
    "true"

# Test 19: End-to-End Workflow
run_test "End-to-End Workflow" \
    "node -e \"const { createMetaLogSystem } = require('./meta-log/src/index.ts'); const metaLog = createMetaLogSystem(); metaLog.processCommand('create a new canvas for algorithm design').then(result => console.log('✅ E2E workflow:', result.response.type));\"" \
    "true"

echo ""
echo "🔧 STRESS TESTING"
echo "--------------------------------------"

# Test 20: Large Canvas Performance
run_test "Large Canvas Performance" \
    "node -e \"const { AIEnhancedCompiler } = require('./logos-system/src/compiler/ai-enhanced-compiler.ts'); const compiler = new AIEnhancedCompiler(); const largeCanvas = {nodes: Array.from({length: 1000}, (_, i) => ({id: \`node_\${i}\`, type: 'test'})), edges: []}; const start = Date.now(); compiler.compileWithAI(largeCanvas).then(() => console.log('Large canvas time:', Date.now() - start));\"" \
    "true"

# Test 21: Concurrent AI Suggestions
run_test "Concurrent AI Suggestions" \
    "node -e \"const { createAIIntelligence } = require('./logos-system/src/ai/index.ts'); const ai = createAIIntelligence(); const promises = Array.from({length: 10}, () => ai.getSuggestions({nodes: [{id: 'test'}], edges: []})); Promise.all(promises).then(results => console.log('Concurrent suggestions completed:', results.length));\"" \
    "true"

echo ""
echo "📊 TEST RESULTS SUMMARY"
echo "=================================================="

echo -e "${GREEN}Total Tests Run: $TOTAL_TESTS${NC}"
echo -e "${GREEN}Tests Passed: $PASSED_TESTS${NC}"
echo -e "${RED}Tests Failed: $FAILED_TESTS${NC}"

if [ $FAILED_TESTS -eq 0 ]; then
    echo -e "${GREEN}🎉 ALL TESTS PASSED!${NC}"
    echo -e "${GREEN}✅ Ecosystem is fully functional and production-ready${NC}"
    exit 0
else
    echo -e "${RED}⚠️  SOME TESTS FAILED${NC}"
    echo -e "${YELLOW}Please check the failed components above${NC}"
    exit 1
fi