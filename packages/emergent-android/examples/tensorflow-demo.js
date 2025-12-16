#!/usr/bin/env node

const { EmergentIntelligence } = require('../dist/index.js');
const chalk = require('chalk');

async function runTensorFlowDemo() {
  console.log(chalk.blue('🧠 TensorFlow Swarm Intelligence Demo'));
  console.log(chalk.gray('Demonstrating AI-powered swarm optimization\n'));

  // Create a coordinator node with TensorFlow enabled
  const coordinator = new EmergentIntelligence({
    id: 'coordinator-tf',
    role: 'coordinator',
    mqttBroker: 'localhost',
    mqttPort: 1883,
    webrtcPort: 8080,
    webPort: 3000,
    aiInterval: 5, // 5 seconds for demo
    location: { x: 0, y: 0 }
  });

  // Create worker nodes
  const workers = [];
  for (let i = 1; i <= 3; i++) {
    const worker = new EmergentIntelligence({
      id: `worker-tf-${i}`,
      role: 'worker',
      mqttBroker: 'localhost',
      mqttPort: 1883,
      webrtcPort: 8080 + i,
      webPort: 3000 + i,
      aiInterval: 8,
      location: { x: i * 50, y: i * 30 }
    });
    workers.push(worker);
  }

  try {
    // Initialize all nodes
    console.log(chalk.yellow('🔧 Initializing swarm nodes...'));
    await coordinator.initialize();
    for (const worker of workers) {
      await worker.initialize();
    }

    // Start all nodes
    console.log(chalk.yellow('🚀 Starting swarm intelligence...'));
    await coordinator.start();
    for (const worker of workers) {
      await worker.start();
    }

    // Set up event listeners for demonstration
    coordinator.on('decision', (data) => {
      console.log(chalk.cyan(`🧠 Coordinator Decision: ${data.action} (${data.time}ms)`));
    });

    coordinator.on('learning', (data) => {
      console.log(chalk.green(`📚 Learning Round ${data.round}: reward ${data.reward.toFixed(3)}`));
    });

    workers.forEach((worker, index) => {
      worker.on('taskCompleted', (result) => {
        console.log(chalk.magenta(`✅ Worker ${index + 1}: Task ${result.taskId} completed`));
      });
    });

    // Demonstrate task processing
    console.log(chalk.yellow('\n📋 Demonstrating task processing...'));
    
    const demoTasks = [
      {
        id: 'demo-task-1',
        type: 'computation',
        requirements: { cpu: 30, memory: 512, battery: 10, network: 20 },
        payload: { algorithm: 'matrix-multiplication', size: 1000 },
        priority: 8
      },
      {
        id: 'demo-task-2',
        type: 'sensing',
        requirements: { cpu: 20, memory: 256, battery: 5, network: 30 },
        payload: { sensors: ['gps', 'accelerometer', 'battery'], frequency: '1hz' },
        priority: 5
      },
      {
        id: 'demo-task-3',
        type: 'coordination',
        requirements: { cpu: 15, memory: 128, battery: 5, network: 40 },
        payload: { coordination_type: 'swarm_formation', target: 'grid' },
        priority: 7
      }
    ];

    // Process tasks on different workers
    for (let i = 0; i < demoTasks.length; i++) {
      const task = demoTasks[i];
      const worker = workers[i % workers.length];
      
      console.log(chalk.blue(`📤 Sending task ${task.id} to ${worker.getStatus().nodeId}`));
      const result = await worker.processTask(task);
      
      if (result.status === 'completed') {
        console.log(chalk.green(`✅ Task ${task.id} completed successfully`));
        console.log(chalk.gray(`   Processing time: ${result.result.processingTime.toFixed(0)}ms`));
        console.log(chalk.gray(`   Confidence: ${(result.result.confidence * 100).toFixed(1)}%`));
      } else {
        console.log(chalk.red(`❌ Task ${task.id} rejected: ${result.reasoning}`));
      }
    }

    // Demonstrate swarm optimization
    console.log(chalk.yellow('\n🔧 Demonstrating swarm optimization...'));
    
    const swarmState = {
      nodes: [
        {
          id: 'coordinator-tf',
          capabilities: { cpu: 90, memory: 4096, battery: 80, network: 70 },
          role: 'coordinator',
          location: { x: 0, y: 0 }
        },
        ...workers.map((worker, index) => ({
          id: worker.getStatus().nodeId,
          capabilities: { cpu: 70, memory: 2048, battery: 60, network: 50 },
          role: 'worker',
          location: { x: (index + 1) * 50, y: (index + 1) * 30 }
        }))
      ],
      tasks: demoTasks,
      networkLatency: 45,
      swarmHealth: 85
    };

    const optimization = await coordinator.optimizeSwarm(swarmState);
    
    console.log(chalk.cyan('\n📊 Swarm Optimization Results:'));
    console.log(chalk.gray(`   Routing rules: ${Object.keys(optimization.routing).length}`));
    console.log(chalk.gray(`   Behavior updates: ${Object.keys(optimization.behavior).length}`));
    console.log(chalk.gray(`   Swarm health: ${optimization.health.overall.toFixed(1)}%`));
    console.log(chalk.gray(`   Anomalies detected: ${Object.keys(optimization.anomalies).filter(id => optimization.anomalies[id] > 0.7).length}`));

    // Demonstrate problem solving with Particle Swarm Optimization
    console.log(chalk.yellow('\n🔍 Demonstrating Particle Swarm Optimization...'));
    
    // Classic optimization problem: minimize sphere function
    const sphereFunction = (x) => x.reduce((sum, val) => sum + val * val, 0);
    
    const psoResult = await coordinator.solveProblem(
      sphereFunction,
      3, // 3 dimensions
      { swarmSize: 20, maxIterations: 50 }
    );
    
    console.log(chalk.cyan('\n🎯 PSO Results:'));
    console.log(chalk.gray(`   Best solution: [${psoResult.bestSolution.map(v => v.toFixed(4)).join(', ')}]`));
    console.log(chalk.gray(`   Best fitness: ${psoResult.bestFitness.toFixed(8)}`));
    console.log(chalk.gray(`   Target: [0.0000, 0.0000, 0.0000] (fitness: 0.00000000)`));

    // Run benchmark
    console.log(chalk.yellow('\n🏃 Running performance benchmark...'));
    
    const benchmarkResults = await coordinator.runBenchmark(5);
    
    console.log(chalk.cyan('\n📊 Benchmark Results:'));
    console.log(chalk.gray(`   Overall Score: ${benchmarkResults.overall.score} (${benchmarkResults.overall.grade})`));
    console.log(chalk.gray(`   Decision Making: ${benchmarkResults.decisionMaking.avgTime.toFixed(1)}ms avg, ${(benchmarkResults.decisionMaking.avgConfidence * 100).toFixed(1)}% confidence`));
    console.log(chalk.gray(`   Optimization: ${benchmarkResults.optimization.avgTime.toFixed(1)}ms avg`));

    // Show final status
    console.log(chalk.yellow('\n📈 Final Swarm Status:'));
    
    const coordinatorStatus = coordinator.getStatus();
    console.log(chalk.cyan(`   Coordinator: ${coordinatorStatus.nodeId}`));
    console.log(chalk.gray(`     Uptime: ${(coordinatorStatus.uptime / 1000).toFixed(1)}s`));
    console.log(chalk.gray(`     Decisions: ${coordinatorStatus.decisionsMade}`));
    console.log(chalk.gray(`     Learning rounds: ${coordinatorStatus.learningRounds}`));
    console.log(chalk.gray(`     Swarm health: ${coordinatorStatus.swarmHealth.toFixed(1)}%`));

    workers.forEach((worker, index) => {
      const status = worker.getStatus();
      console.log(chalk.cyan(`   Worker ${index + 1}: ${status.nodeId}`));
      console.log(chalk.gray(`     Tasks processed: ${status.tasksProcessed}`));
      console.log(chalk.gray(`     Decisions: ${status.decisionsMade}`));
    });

    console.log(chalk.green('\n🎉 TensorFlow Swarm Intelligence Demo Complete!'));
    console.log(chalk.cyan('Key capabilities demonstrated:'));
    console.log(chalk.gray('  • TensorFlow-based decision making'));
    console.log(chalk.gray('  • Federated learning across swarm'));
    console.log(chalk.gray('  • Particle Swarm Optimization'));
    console.log(chalk.gray('  • Real-time swarm optimization'));
    console.log(chalk.gray('  • Adaptive intelligence based on device capabilities'));

  } catch (error) {
    console.error(chalk.red('❌ Demo failed:'), error);
  } finally {
    // Cleanup
    console.log(chalk.yellow('\n🧹 Cleaning up...'));
    await coordinator.dispose();
    for (const worker of workers) {
      await worker.dispose();
    }
  }
}

// Run the demo
if (require.main === module) {
  runTensorFlowDemo().catch(console.error);
}

module.exports = { runTensorFlowDemo };