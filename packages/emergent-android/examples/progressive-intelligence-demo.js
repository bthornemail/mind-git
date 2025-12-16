#!/usr/bin/env node

const { ProgressiveIntelligenceOrchestrator } = require('../dist/ai/ProgressiveIntelligenceOrchestrator');
const { SwarmIntelligenceEngine } = require('../dist/ai/SwarmIntelligenceEngine');
const chalk = require('chalk');

async function runProgressiveIntelligenceDemo() {
  console.log(chalk.blue('🧠 Progressive Intelligence Demo'));
  console.log(chalk.gray('Mathematical Constraints + TensorFlow + LLM (when needed)\n'));

  // Initialize TensorFlow engine
  const tfEngine = new SwarmIntelligenceEngine();
  await tfEngine.initialize();

  // Create progressive orchestrator with LLM endpoint
  const orchestrator = new ProgressiveIntelligenceOrchestrator(
    tfEngine,
    process.env.LLM_ENDPOINT || 'http://localhost:11434' // Optional LLM
  );

  try {
    console.log(chalk.yellow('🔧 Setting up progressive intelligence scenarios...'));

    // Scenario 1: Pure Mathematical Solution
    console.log(chalk.cyan('\n📐 Scenario 1: Pure Mathematical Constraints'));
    await demonstrateMathematicalSolution(orchestrator);

    // Scenario 2: Hybrid Intelligence
    console.log(chalk.cyan('\n🤖 Scenario 2: Hybrid Intelligence (Math + TensorFlow)'));
    await demonstrateHybridIntelligence(orchestrator);

    // Scenario 3: LLM Enhanced
    console.log(chalk.cyan('\n🧠 Scenario 3: LLM Enhanced Complex Reasoning'));
    await demonstrateLLMEnhanced(orchestrator);

    // Scenario 4: Constraint Violation
    console.log(chalk.cyan('\n❌ Scenario 4: Constraint Violation Handling'));
    await demonstrateConstraintViolation(orchestrator);

    // Scenario 5: Swarm Optimization with E8 Routing
    console.log(chalk.cyan('\n🔍 Scenario 5: Swarm Optimization with E8 Lattice Routing'));
    await demonstrateSwarmOptimization(orchestrator);

    // Show final metrics
    console.log(chalk.cyan('\n📊 Progressive Intelligence Metrics'));
    showFinalMetrics(orchestrator);

    console.log(chalk.green('\n🎉 Progressive Intelligence Demo Complete!'));
    console.log(chalk.cyan('Key insights demonstrated:'));
    console.log(chalk.gray('  • Mathematical constraints are PRIMARY decision layer'));
    console.log(chalk.gray('  • TensorFlow used ONLY when mathematical confidence < 90%'));
    console.log(chalk.gray('  • LLM used ONLY for complex explanation needs'));
    console.log(chalk.gray('  • E8 lattice routing provides optimal paths'));
    console.log(chalk.gray('  • Every decision is mathematically verifiable'));
    console.log(chalk.gray('  • Progressive enhancement maintains transparency'));

  } catch (error) {
    console.error(chalk.red('❌ Demo failed:'), error);
  } finally {
    // Cleanup
    console.log(chalk.yellow('\n🧹 Cleaning up...'));
    orchestrator.dispose();
    tfEngine.dispose();
  }
}

async function demonstrateMathematicalSolution(orchestrator) {
  console.log(chalk.gray('Creating scenario with high-confidence mathematical solution...'));

  // Create nodes that satisfy all constraints
  const nodes = [
    {
      id: 'node-math-1',
      capabilities: { cpu: 80, memory: 2048, battery: 85, network: 70 },
      role: 'worker',
      location: { x: 0, y: 0 }
    },
    {
      id: 'node-math-2',
      capabilities: { cpu: 75, memory: 1536, battery: 78, network: 65 },
      role: 'worker',
      location: { x: 50, y: 30 }
    }
  ];

  // Create simple tasks
  const tasks = [
    {
      id: 'task-math-1',
      type: 'computation',
      requirements: { cpu: 20, memory: 512, battery: 10, network: 20 },
      payload: { algorithm: 'simple' },
      priority: 5
    }
  ];

  const context = {
    tasks,
    nodes,
    swarmState: { nodes, tasks, networkLatency: 50, swarmHealth: 95 },
    complexity: 1,
    hasUnusualConstraints: false,
    requiresExplanation: false
  };

  const decision = await orchestrator.makeDecision(context);

  console.log(chalk.green('✅ Mathematical Decision:'));
  console.log(chalk.gray(`   Path: ${decision.decisionPath}`));
  console.log(chalk.gray(`   Confidence: ${(decision.confidence * 100).toFixed(1)}%`));
  console.log(chalk.gray(`   Reasoning: ${decision.reasoning}`));
  console.log(chalk.gray(`   Mathematical: ${decision.explanation.mathematical}`));
  
  if (decision.e8Routing) {
    console.log(chalk.gray(`   E8 Distance: ${decision.e8Routing.distance.toFixed(2)}`));
    console.log(chalk.gray(`   Hopf Fibration: ${decision.e8Routing.hopfFibration.toFixed(3)}`));
  }
}

async function demonstrateHybridIntelligence(orchestrator) {
  console.log(chalk.gray('Creating scenario requiring TensorFlow enhancement...'));

  // Create nodes with mixed capabilities
  const nodes = [
    {
      id: 'node-hybrid-1',
      capabilities: { cpu: 60, memory: 1024, battery: 45, network: 80 },
      role: 'worker',
      location: { x: 0, y: 0 }
    },
    {
      id: 'node-hybrid-2',
      capabilities: { cpu: 85, memory: 3072, battery: 25, network: 40 },
      role: 'worker',
      location: { x: 100, y: 50 }
    },
    {
      id: 'node-hybrid-3',
      capabilities: { cpu: 40, memory: 768, battery: 90, network: 30 },
      role: 'worker',
      location: { x: 25, y: 75 }
    }
  ];

  // Create complex tasks
  const tasks = [
    {
      id: 'task-hybrid-1',
      type: 'computation',
      requirements: { cpu: 35, memory: 1024, battery: 15, network: 25 },
      payload: { algorithm: 'complex_optimization' },
      priority: 7
    },
    {
      id: 'task-hybrid-2',
      type: 'sensing',
      requirements: { cpu: 25, memory: 512, battery: 8, network: 35 },
      payload: { sensors: ['multi_modal'], frequency: '10hz' },
      priority: 6
    }
  ];

  const context = {
    tasks,
    nodes,
    swarmState: { nodes, tasks, networkLatency: 120, swarmHealth: 75 },
    complexity: 3,
    hasUnusualConstraints: false,
    requiresExplanation: false
  };

  const decision = await orchestrator.makeDecision(context);

  console.log(chalk.yellow('🤖 Hybrid Decision:'));
  console.log(chalk.gray(`   Path: ${decision.decisionPath}`));
  console.log(chalk.gray(`   Confidence: ${(decision.confidence * 100).toFixed(1)}%`));
  console.log(chalk.gray(`   Mathematical: ${decision.explanation.mathematical}`));
  console.log(chalk.gray(`   AI: ${decision.explanation.ai}`));
  console.log(chalk.gray(`   Combined: ${decision.explanation.combined}`));

  if (decision.allocation) {
    console.log(chalk.gray('   Allocation:'));
    decision.allocation.forEach(alloc => {
      console.log(chalk.gray(`     ${alloc.taskId} → ${alloc.nodeId} (${(alloc.confidence * 100).toFixed(1)}% confidence)`));
    });
  }
}

async function demonstrateLLMEnhanced(orchestrator) {
  console.log(chalk.gray('Creating complex scenario requiring LLM reasoning...'));

  // Create diverse nodes
  const nodes = [
    {
      id: 'node-llm-1',
      capabilities: { cpu: 95, memory: 4096, battery: 15, network: 90 },
      role: 'coordinator',
      location: { x: 0, y: 0 }
    },
    {
      id: 'node-llm-2',
      capabilities: { cpu: 30, memory: 512, battery: 95, network: 20 },
      role: 'worker',
      location: { x: 200, y: 100 }
    },
    {
      id: 'node-llm-3',
      capabilities: { cpu: 70, memory: 2048, battery: 50, network: 60 },
      role: 'hybrid',
      location: { x: 50, y: 150 }
    },
    {
      id: 'node-llm-4',
      capabilities: { cpu: 45, memory: 1024, battery: 80, network: 35 },
      role: 'worker',
      location: { x: 150, y: 25 }
    }
  ];

  // Create complex, conflicting tasks
  const tasks = [
    {
      id: 'task-llm-1',
      type: 'coordination',
      requirements: { cpu: 40, memory: 1536, battery: 20, network: 50 },
      payload: { coordination_type: 'emergency_response', priority: 'critical' },
      priority: 10
    },
    {
      id: 'task-llm-2',
      type: 'computation',
      requirements: { cpu: 60, memory: 3072, battery: 30, network: 40 },
      payload: { algorithm: 'real_time_analytics', deadline: '5min' },
      priority: 9
    },
    {
      id: 'task-llm-3',
      type: 'sensing',
      requirements: { cpu: 15, memory: 256, battery: 5, network: 70 },
      payload: { sensors: ['environmental'], coverage: 'wide_area' },
      priority: 4
    }
  ];

  const context = {
    tasks,
    nodes,
    swarmState: { nodes, tasks, networkLatency: 200, swarmHealth: 60 },
    complexity: 8,
    hasUnusualConstraints: true,
    requiresExplanation: true
  };

  const decision = await orchestrator.makeDecision(context);

  console.log(chalk.magenta('🧠 LLM-Enhanced Decision:'));
  console.log(chalk.gray(`   Path: ${decision.decisionPath}`));
  console.log(chalk.gray(`   Confidence: ${(decision.confidence * 100).toFixed(1)}%`));
  console.log(chalk.gray(`   Mathematical: ${decision.explanation.mathematical}`));
  console.log(chalk.gray(`   AI: ${decision.explanation.ai}`));
  console.log(chalk.gray(`   Combined: ${decision.explanation.combined}`));

  if (decision.mathematicalSolution) {
    const solution = decision.mathematicalSolution;
    console.log(chalk.gray(`   Mathematical Solution: ${solution.validNodes.length}/${nodes.length} nodes valid`));
    console.log(chalk.gray(`   Constraint Violations: ${solution.violations.length}`));
  }
}

async function demonstrateConstraintViolation(orchestrator) {
  console.log(chalk.gray('Creating scenario with constraint violations...'));

  // Create nodes that violate constraints
  const nodes = [
    {
      id: 'node-violation-1',
      capabilities: { cpu: 5, memory: 128, battery: 10, network: 5 }, // Violates multiple constraints
      role: 'worker',
      location: { x: 0, y: 0 }
    },
    {
      id: 'node-violation-2',
      capabilities: { cpu: 15, memory: 200, battery: 15, network: 8 }, // Barely passes
      role: 'worker',
      location: { x: 50, y: 30 }
    }
  ];

  // Create demanding tasks
  const tasks = [
    {
      id: 'task-violation-1',
      type: 'computation',
      requirements: { cpu: 50, memory: 2048, battery: 25, network: 40 }, // Impossible for these nodes
      payload: { algorithm: 'high_performance' },
      priority: 8
    }
  ];

  const context = {
    tasks,
    nodes,
    swarmState: { nodes, tasks, networkLatency: 500, swarmHealth: 25 },
    complexity: 5,
    hasUnusualConstraints: true,
    requiresExplanation: true
  };

  const decision = await orchestrator.makeDecision(context);

  console.log(chalk.red('❌ Constraint Violation Decision:'));
  console.log(chalk.gray(`   Path: ${decision.decisionPath}`));
  console.log(chalk.gray(`   Confidence: ${(decision.confidence * 100).toFixed(1)}%`));
  console.log(chalk.gray(`   Reasoning: ${decision.reasoning}`));
  console.log(chalk.gray(`   Mathematical: ${decision.explanation.mathematical}`));

  if (decision.mathematicalSolution) {
    const solution = decision.mathematicalSolution;
    console.log(chalk.gray(`   Valid Nodes: ${solution.validNodes.length}/${nodes.length}`));
    
    if (solution.violations.length > 0) {
      console.log(chalk.gray('   Violations:'));
      solution.violations.forEach(violation => {
        console.log(chalk.gray(`     ${violation.nodeId}: ${violation.constraint.description} (${violation.actualValue} ${violation.constraint.operator} ${violation.constraint.value})`));
      });
    }
  }
}

async function demonstrateSwarmOptimization(orchestrator) {
  console.log(chalk.gray('Demonstrating swarm optimization with E8 lattice routing...'));

  // Create swarm with diverse nodes
  const nodes = [
    {
      id: 'swarm-coordinator',
      capabilities: { cpu: 90, memory: 4096, battery: 80, network: 85 },
      role: 'coordinator',
      location: { x: 0, y: 0 }
    },
    {
      id: 'swarm-worker-1',
      capabilities: { cpu: 70, memory: 2048, battery: 60, network: 50 },
      role: 'worker',
      location: { x: 100, y: 0 }
    },
    {
      id: 'swarm-worker-2',
      capabilities: { cpu: 60, memory: 1536, battery: 75, network: 40 },
      role: 'worker',
      location: { x: 50, y: 87 }
    },
    {
      id: 'swarm-worker-3',
      capabilities: { cpu: 80, memory: 3072, battery: 45, network: 70 },
      role: 'hybrid',
      location: { x: -50, y: 87 }
    },
    {
      id: 'swarm-worker-4',
      capabilities: { cpu: 50, memory: 1024, battery: 90, network: 30 },
      role: 'worker',
      location: { x: -100, y: 0 }
    }
  ];

  const tasks = [
    {
      id: 'swarm-task-1',
      type: 'coordination',
      requirements: { cpu: 25, memory: 512, battery: 10, network: 30 },
      payload: { coordination_type: 'formation_flying' },
      priority: 7
    },
    {
      id: 'swarm-task-2',
      type: 'computation',
      requirements: { cpu: 40, memory: 1024, battery: 15, network: 25 },
      payload: { algorithm: 'distributed_processing' },
      priority: 6
    }
  ];

  const swarmState = {
    nodes,
    tasks,
    networkLatency: 85,
    swarmHealth: 78
  };

  const optimization = await orchestrator.optimizeSwarmWithMathematics(swarmState);

  console.log(chalk.cyan('🔍 Swarm Optimization Results:'));
  console.log(chalk.gray(`   Mathematical Solution: ${optimization.mathematicalSolution.validNodes.length}/${nodes.length} nodes valid`));
  console.log(chalk.gray(`   Routing Rules: ${Object.keys(optimization.routing).length}`));
  console.log(chalk.gray(`   Behavior Updates: ${Object.keys(optimization.behavior).length}`));
  console.log(chalk.gray(`   Swarm Health: ${optimization.health.overall.toFixed(1)}%`));
  console.log(chalk.gray(`   Anomalies: ${Object.keys(optimization.anomalies).filter(id => optimization.anomalies[id] > 0.7).length}`));

  // Show E8 routing paths
  if (Object.keys(optimization.e8Paths).length > 0) {
    console.log(chalk.gray('   E8 Lattice Paths:'));
    Object.entries(optimization.e8Paths).forEach(([sourceId, path]) => {
      console.log(chalk.gray(`     ${sourceId}: distance=${path.distance.toFixed(2)}, hopf=${path.hopfFibration.toFixed(3)}, betti=${path.bettiNumber}`));
    });
  }

  // Show constraint analysis
  const constraintAnalysis = orchestrator.analyzeConstraintEffectiveness(nodes);
  console.log(chalk.gray('   Constraint Effectiveness:'));
  constraintAnalysis.forEach(analysis => {
    console.log(chalk.gray(`     ${analysis.constraint.type}: ${(analysis.effectiveness * 100).toFixed(1)}% effective, ${(analysis.eliminationRate * 100).toFixed(1)}% elimination rate`));
    if (analysis.recommendations.length > 0) {
      analysis.recommendations.forEach(rec => {
        console.log(chalk.gray(`       → ${rec}`));
      });
    }
  });
}

function showFinalMetrics(orchestrator) {
  const metrics = orchestrator.getMetrics();
  const breakdown = orchestrator.getDecisionBreakdown();

  console.log(chalk.cyan('📈 Decision Breakdown:'));
  console.log(chalk.gray(`   Total Decisions: ${metrics.totalDecisions}`));
  console.log(chalk.gray(`   Pure Mathematical: ${breakdown.mathematical} (${breakdown.percentages.mathematical.toFixed(1)}%)`));
  console.log(chalk.gray(`   Hybrid Intelligence: ${breakdown.hybrid} (${breakdown.percentages.hybrid.toFixed(1)}%)`));
  console.log(chalk.gray(`   LLM Enhanced: ${breakdown.llm} (${breakdown.percentages.llm.toFixed(1)}%)`));
  console.log(chalk.gray(`   Constraint Violations: ${breakdown.violations} (${breakdown.percentages.violations.toFixed(1)}%)`));

  console.log(chalk.cyan('📊 Performance Metrics:'));
  console.log(chalk.gray(`   Average Confidence: ${(metrics.averageConfidence * 100).toFixed(1)}%`));
  console.log(chalk.gray(`   Average Decision Latency: ${metrics.decisionLatency.toFixed(1)}ms`));
  console.log(chalk.gray(`   Constraint Effectiveness: ${(metrics.constraintEffectiveness * 100).toFixed(1)}%`));

  console.log(chalk.cyan('⚙️ Decision Thresholds:'));
  const thresholds = orchestrator.getDecisionThresholds();
  console.log(chalk.gray(`   Mathematical: ${(thresholds.mathematical * 100).toFixed(1)}%`));
  console.log(chalk.gray(`   Hybrid: ${(thresholds.hybrid * 100).toFixed(1)}%`));
  console.log(chalk.gray(`   LLM: ${(thresholds.llm * 100).toFixed(1)}%`));
}

// Run demo
if (require.main === module) {
  runProgressiveIntelligenceDemo().catch(console.error);
}

module.exports = { runProgressiveIntelligenceDemo };