#!/usr/bin/env node

/**
 * mind-git OpenCode Integration Demo
 * 
 * Demonstrates the key features of the mind-git OpenCode integration package.
 */

import MindGitOpenCodeIntegration from './.opencode/client.js';

async function runDemo() {
  console.log("🚀 mind-git OpenCode Integration Demo\n");

  const integration = new MindGitOpenCodeIntegration();

  try {
    // 1. Check integration status
    console.log("📊 Checking integration status...");
    const status = await integration.getStatus();
    console.log(JSON.stringify(status, null, 2));
    console.log();

    // 2. List available tools
    console.log("🛠️ Available tools:");
    const tools = await integration.listTools();
    tools.forEach(tool => {
      console.log(`  • ${tool.name}: ${tool.description}`);
    });
    console.log();

    // 3. List available agents
    console.log("🤖 Available agents:");
    const agents = await integration.listAgents();
    agents.forEach(agent => {
      console.log(`  • ${agent.name}: ${agent.description}`);
    });
    console.log();

    // 4. Example: Compile a canvas (if exists)
    const exampleCanvas = "examples/spatial-hello-world.canvas";
    console.log(`📝 Attempting to compile example canvas: ${exampleCanvas}`);
    
    try {
      const compileResult = await integration.compileCanvas(exampleCanvas, {
        target: "javascript",
        verify: true
      });
      console.log("✅ Canvas compilation initiated successfully");
    } catch (error) {
      console.log("ℹ️ Canvas compilation demo skipped (file may not exist)");
    }
    console.log();

    // 5. Example: Mathematical verification
    console.log("🧮 Running mathematical verification demo...");
    try {
      const verifyResult = await integration.verifyMathematics("norm-preservation", {
        dimension: 4,
        operation: "euler",
        vectors: [
          [1, 0, 0, 0],
          [0, 1, 0, 0]
        ]
      });
      console.log("✅ Mathematical verification initiated successfully");
    } catch (error) {
      console.log("ℹ️ Mathematical verification demo skipped");
    }
    console.log();

    // 6. Example: P2P collaboration setup
    console.log("🌐 Setting up P2P collaboration demo...");
    try {
      const collabResult = await integration.setupCollaboration(
        "demo-repository",
        "demo-peer",
        {
          mode: "real-time",
          conflict: "operational-transform"
        }
      );
      console.log("✅ P2P collaboration setup initiated successfully");
    } catch (error) {
      console.log("ℹ️ P2P collaboration demo skipped");
    }
    console.log();

    console.log("🎉 Demo completed! The mind-git OpenCode integration is ready to use.");
    console.log();
    console.log("Next steps:");
    console.log("1. Start OpenCode: opencode");
    console.log("2. Use the CLI: node .opencode/client.js --help");
    console.log("3. Check documentation: cat .opencode/README.md");

  } catch (error) {
    console.error("❌ Demo failed:", error.message);
    console.log("\nTroubleshooting:");
    console.log("1. Ensure OpenCode server is running: opencode");
    console.log("2. Install dependencies: npm run opencode:install");
    console.log("3. Check configuration: cat .opencode/config.json");
  }
}

// Run demo if called directly
if (import.meta.url === `file://${process.argv[1]}`) {
  runDemo();
}

export default runDemo;