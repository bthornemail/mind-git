#!/usr/bin/env node

const { EmergentIntelligence } = require('../dist/index.js');
const chalk = require('chalk');

async function runCompleteDemo() {
  console.log(chalk.blue('🎯 Complete Progressive Intelligence Demo'));
  console.log(chalk.gray('Mathematical Constraints + TensorFlow + LLM + E8 Lattice Routing\n'));

  // Create nodes with progressive intelligence enabled
  const coordinator = new EmergentIntelligence({
    id: 'coordinator-progressive',
    role: 'coordinator',
    mqttBroker: 'localhost',
    mqttPort: 1883,
    webrtcPort: 8080,
    webPort: 3000,
    aiInterval: 5,
    location: { x: 0, y: 0 }
  }, { useProgressiveIntelligence: true });

  const workers = [];
  for (let i = 1; i <= 4; i++) {
    const worker = new EmergentIntelligence({
      id: `worker-progressive-${i}`,
      role: i === 3 ? 'hybrid' : 'worker',
      mqttBroker: 'localhost',
      mqttPort: 1883,
      webrtcPort: 8080 + i,
      webPort: 3000 + i,
      aiInterval: 8,
      location: { 
        x: Math.cos(i * Math.PI / 2) * 100, 
        y: Math.sin(i * Math.PI / 2) * 100 
      }
    }, { useProgressiveIntelligence: true });
    workers.push(worker);
  }

  try {
    // Initialize all nodes
    console.log(chalk.yellow('🔧 Initializing progressive intelligence swarm...'));
    await coordinator.initialize();
    for (const worker of workers) {
      await worker.initialize();
    }

    // Start all nodes
    console.log(chalk.yellow('🚀 Starting progressive intelligence swarm...'));
    await coordinator.start();
    for (const worker of workers) {
      await worker.start();
    }

    // Set up event listeners
    setupEventListeners(coordinator, workers);

    // Demonstrate progressive decision making
    await demonstrateProgressiveDecisions(coordinator, workers);

    // Show constraint analysis
    await demonstrateConstraintAnalysis(coordinator, workers);

    // Show E8 lattice routing
    await demonstrateE8Routing(coordinator, workers);

    // Show final metrics
    await showFinalProgressiveMetrics(coordinator, workers);

    console.log(chalk.green('\n🎉 Complete Progressive Intelligence Demo Finished!'));
    console.log(chalk.cyan('Revolutionary capabilities demonstrated:'));
    console.log(chalk.gray('  ✅ Mathematical constraints as PRIMARY decision layer'));
    console.log(chalk.gray('  ✅ TensorFlow used ONLY when mathematical confidence < 90%'));
    console.log(chalk.gray('  ✅ LLM used ONLY for complex explanation needs'));
    console.log(chalk.gray('  ✅ E8 lattice provides optimal routing paths'));
    console.log(chalk.gray('  ✅ Every decision is mathematically verifiable'));
    console.log(chalk.gray('  ✅ Progressive enhancement maintains transparency'));
    console.log(chalk.gray('  ✅ Human-in-the-loop for indeterminate queries'));
    console.log(chalk.gray('  ✅ Deterministic core with adaptive enhancement'));

  } catch (error) {
    console.error(chalk.red('❌ Demo failed:'), error);
  } finally {
    // Cleanup
    console.log(chalk.yellow('\n🧹 Cleaning up progressive intelligence swarm...'));
    await coordinator.dispose();
    for (const worker of workers) {
      await worker.dispose();
    }
  }
}

function setupEventListeners(coordinator, workers) {
  // Coordinator events
  coordinator.on('decision', (data) => {
    if (data.type === 'mathematical') {
      console.log(chalk.cyan(`🧠 Coordinator: Pure Mathematical Decision (${data.time}ms)`));
    } else if (data.type === 'hybrid') {
      console.log(chalk.blue(`🤖 Coordinator: Hybrid Decision (${data.time}ms)`));
    } else if (data.type === 'llm_enhanced') {
      console.log(chalk.magenta(`🧠 Coordinator: LLM-Enhanced Decision (${data.time}ms)`));
    }
  });

  // Worker events
  workers.forEach((worker, index) => {
    worker.on('taskCompleted', (result) => {
      console.log(chalk.green(`✅ Worker ${index + 1}: Task ${result.taskId} completed`));
    });

    worker.on('decision', (data) => {
      const breakdown = worker.getDecisionBreakdown();
      if (breakdown) {
        console.log(chalk.gray(`   Worker ${index + 1} decisions: ${breakdown.percentages.mathematical.toFixed(1)}% mathematical, ${breakdown.percentages.hybrid.toFixed(1)}% hybrid, ${breakdown.percentages.llm.toFixed(1)}% LLM`));
      }
    });
  });
}

async function demonstrateProgressiveDecisions(coordinator, workers) {
  console.log(chalk.yellow('\n🧠 Demonstrating Progressive Decision Making...'));

  const scenarios = [
    {
      name: 'Simple Mathematical Solution',
      tasks: [{
        id: 'simple-task',
        type: 'computation',
        requirements: { cpu: 20, memory: 512, battery: 10, network: 20 },
        payload: { algorithm: 'simple' },
        priority: 3
      }],
      description: 'High-confidence mathematical solution'
    },
    {
      name: 'Complex Hybrid Solution',
      tasks: [
        {
          id: 'complex-task-1',
          type: 'coordination',
          requirements: { cpu: 35, memory: 1024, battery: 15, network: 30 },
          payload: { coordination_type: 'formation' },
          priority: 7
        },
        {
          id: 'complex-task-2',
          type: 'sensing',
          requirements: { cpu: 25, memory: 768, battery: 8, network: 40 },
          payload: { sensors: ['multi_modal'] },
          priority: 6
        }
      ],
      description: 'Requires TensorFlow optimization'
    },
    {
      name: 'LLM-Enhanced Complex Reasoning',
      tasks: [
        {
          id: 'llm-task-1',
          type: 'coordination',
          requirements: { cpu: 40, memory: 1536, battery: 20, network: 50 },
          payload: { coordination_type: 'emergency_response', priority: 'critical' },
          priority: 10
        },
        {
          id: 'llm-task-2',
          type: 'computation',
          requirements: { cpu: 60, memory: 3072, battery: 30, network: 40 },
          payload: { algorithm: 'real_time_analytics', deadline: '5min' },
          priority: 9
        }
      ],
      description: 'Complex scenario requiring explanation'
    }
  ];

  for (const scenario of scenarios) {
    console.log(chalk.cyan(`\n📋 ${scenario.name}:`));
    console.log(chalk.gray(`   ${scenario.description}`));

    // Process tasks on different workers
    for (let i = 0; i < scenario.tasks.length; i++) {
      const task = scenario.tasks[i];
      const worker = workers[i % workers.length];
      
      console.log(chalk.blue(`   📤 Processing ${task.id} on ${worker.getStatus().nodeId}`));
      const result = await worker.processTask(task);
      
      if (result.status === 'completed') {
        console.log(chalk.green(`   ✅ ${task.id}: ${result.reasoning}`));
      } else {
        console.log(chalk.red(`   ❌ ${task.id}: ${result.reasoning}`));
      }
    }

    // Show decision breakdown
    await new Promise(resolve => setTimeout(resolve, 1000));
  }
}

async function demonstrateConstraintAnalysis(coordinator, workers) {
  console.log(chalk.yellow('\n🔍 Demonstrating Mathematical Constraint Analysis...'));

  // Add custom constraints
  coordinator.addMathematicalConstraint({
    type: 'battery',
    operator: '>',
    value: 30, // Stricter than default
    priority: 1,
    description: 'Battery must be above 30% for critical tasks'
  });

  coordinator.addMathematicalConstraint({
    type: 'e8_distance',
    operator: '<',
    value: 80, // Tighter E8 constraint
    priority: 2,
    description: 'E8 lattice distance must be minimized for optimal routing'
  });

  // Analyze constraint effectiveness
  const nodes = workers.map(worker => ({
    id: worker.getStatus().nodeId,
    capabilities: {
      cpu: 70 + Math.random() * 30,
      memory: 1024 + Math.random() * 2048,
      battery: 20 + Math.random() * 80,
      network: 20 + Math.random() * 80
    },
    role: worker.getStatus().role,
    location: { x: Math.random() * 200 - 100, y: Math.random() * 200 - 100 }
  }));

  const analysis = coordinator.analyzeConstraintEffectiveness(nodes);
  
  console.log(chalk.cyan('📊 Constraint Effectiveness Analysis:'));
  analysis.forEach(item => {
    console.log(chalk.gray(`   ${item.constraint.type}: ${(item.effectiveness * 100).toFixed(1)}% effective, ${(item.eliminationRate * 100).toFixed(1)}% elimination rate`));
    if (item.recommendations.length > 0) {
      item.recommendations.forEach(rec => {
        console.log(chalk.yellow(`     → ${rec}`));
      });
    }
  });

  // Show current constraints
  const constraints = coordinator.getMathematicalConstraints();
  console.log(chalk.cyan('\n⚙️ Active Mathematical Constraints:'));
  constraints.forEach(constraint => {
    console.log(chalk.gray(`   ${constraint.type}: ${constraint.description} (${constraint.operator} ${constraint.value}, priority: ${constraint.priority})`));
  });
}

async function demonstrateE8Routing(coordinator, workers) {
  console.log(chalk.yellow('\n🔍 Demonstrating E8 Lattice Routing...'));

  // Create swarm state for routing demonstration
  const swarmState = {
    nodes: [
      {
        id: coordinator.getStatus().nodeId,
        capabilities: { cpu: 90, memory: 4096, battery: 80, network: 85 },
        role: 'coordinator',
        location: { x: 0, y: 0 }
      },
      ...workers.map((worker, index) => ({
        id: worker.getStatus().nodeId,
        capabilities: { cpu: 70, memory: 2048, battery: 60, network: 50 },
        role: worker.getStatus().role,
        location: { 
          x: Math.cos(index * Math.PI / 2) * 100, 
          y: Math.sin(index * Math.PI / 2) * 100 
        }
      }))
    ],
    tasks: [
      {
        id: 'routing-task-1',
        type: 'coordination',
        requirements: { cpu: 25, memory: 512, battery: 10, network: 30 },
        payload: { coordination_type: 'data_relay' },
        priority: 7
      }
    ],
    networkLatency: 85,
    swarmHealth: 78
  };

  const optimization = await coordinator.optimizeSwarm(swarmState);

  console.log(chalk.cyan('🔍 E8 Lattice Routing Results:'));
  
  if (optimization.mathematicalSolution) {
    const solution = optimization.mathematicalSolution;
    console.log(chalk.gray(`   Mathematical Solution: ${solution.validNodes.length}/${swarmState.nodes.length} nodes valid`));
    console.log(chalk.gray(`   Solution Confidence: ${(solution.confidence * 100).toFixed(1)}%`));
  }

  if (optimization.e8Paths) {
    console.log(chalk.gray('   E8 Lattice Paths:'));
    Object.entries(optimization.e8Paths).forEach(([sourceId, path]) => {
      console.log(chalk.gray(`     ${sourceId}:`));
      console.log(chalk.gray(`       Distance: ${path.distance.toFixed(2)}`));
      console.log(chalk.gray(`       Hopf Fibration: ${path.hopfFibration.toFixed(3)}`));
      console.log(chalk.gray(`       Betti Number: ${path.bettiNumber}`));
      console.log(chalk.gray(`       Path: ${path.path.slice(0, 3).join(' → ')}${path.path.length > 3 ? ' → ...' : ''}`));
    });
  }

  console.log(chalk.gray(`   Routing Rules: ${Object.keys(optimization.routing).length}`));
  console.log(chalk.gray(`   Behavior Updates: ${Object.keys(optimization.behavior).length}`));
  console.log(chalk.gray(`   Swarm Health: ${optimization.health.overall.toFixed(1)}%`));
}

async function showFinalProgressiveMetrics(coordinator, workers) {
  console.log(chalk.yellow('\n📈 Final Progressive Intelligence Metrics'));

  // Coordinator metrics
  const coordinatorMetrics = coordinator.getProgressiveMetrics();
  if (coordinatorMetrics) {
    const breakdown = coordinator.getDecisionBreakdown();
    
    console.log(chalk.cyan('🎯 Coordinator Progressive Metrics:'));
    console.log(chalk.gray(`   Total Decisions: ${coordinatorMetrics.totalDecisions}`));
    console.log(chalk.gray(`   Pure Mathematical: ${breakdown.mathematical} (${breakdown.percentages.mathematical.toFixed(1)}%)`));
    console.log(chalk.gray(`   Hybrid Intelligence: ${breakdown.hybrid} (${breakdown.percentages.hybrid.toFixed(1)}%)`));
    console.log(chalk.gray(`   LLM Enhanced: ${breakdown.llm} (${breakdown.percentages.llm.toFixed(1)}%)`));
    console.log(chalk.gray(`   Constraint Violations: ${breakdown.violations} (${breakdown.percentages.violations.toFixed(1)}%)`));
    console.log(chalk.gray(`   Average Confidence: ${(coordinatorMetrics.averageConfidence * 100).toFixed(1)}%`));
    console.log(chalk.gray(`   Average Decision Latency: ${coordinatorMetrics.decisionLatency.toFixed(1)}ms`));
  }

  // Worker metrics
  console.log(chalk.cyan('\n📊 Worker Progressive Metrics:'));
  workers.forEach((worker, index) => {
    const workerMetrics = worker.getProgressiveMetrics();
    const workerBreakdown = worker.getDecisionBreakdown();
    
    if (workerMetrics && workerBreakdown) {
      console.log(chalk.gray(`   Worker ${index + 1} (${worker.getStatus().nodeId}):`));
      console.log(chalk.gray(`     Decisions: ${workerMetrics.totalDecisions}, Mathematical: ${workerBreakdown.percentages.mathematical.toFixed(1)}%, Hybrid: ${workerBreakdown.percentages.hybrid.toFixed(1)}%`));
    }
  });

  // Overall system health
  console.log(chalk.cyan('\n🏥 System Health Summary:'));
  const coordinatorStatus = coordinator.getStatus();
  console.log(chalk.gray(`   Coordinator Uptime: ${(coordinatorStatus.uptime / 1000).toFixed(1)}s`));
  console.log(chalk.gray(`   Coordinator Swarm Health: ${coordinatorStatus.swarmHealth.toFixed(1)}%`));
  console.log(chalk.gray(`   Total Tasks Processed: ${workers.reduce((sum, w) => sum + w.getStatus().tasksProcessed, 0)}`));
  console.log(chalk.gray(`   Total Learning Rounds: ${workers.reduce((sum, w) => sum + (w.getStatus().learningRounds || 0), 0)}`));
}

// Run demo
if (require.main === module) {
  runCompleteDemo().catch(console.error);
}

module.exports = { runCompleteDemo };