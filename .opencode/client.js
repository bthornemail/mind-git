#!/usr/bin/env node

/**
 * mind-git OpenCode Integration Client
 * 
 * Provides seamless integration between mind-git's mathematical foundation
 * and OpenCode's AI-powered development environment.
 */

import { createOpencodeClient } from "@opencode-ai/sdk";
import { readFileSync, existsSync } from "fs";
import { join, dirname } from "path";
import { fileURLToPath } from "url";

const __filename = fileURLToPath(import.meta.url);
const __dirname = dirname(__filename);

class MindGitOpenCodeIntegration {
  constructor(config = {}) {
    this.client = createOpencodeClient({
      baseUrl: config.baseUrl || "http://localhost:4096",
      ...config
    });
    
    this.config = this.loadConfig();
    this.tools = this.loadTools();
    this.agents = this.loadAgents();
  }

  loadConfig() {
    const configPath = join(__dirname, ".opencode", "config.json");
    if (existsSync(configPath)) {
      return JSON.parse(readFileSync(configPath, "utf8"));
    }
    return {};
  }

  loadTools() {
    const toolsDir = join(__dirname, ".opencode", "tools");
    const tools = {};
    
    const toolFiles = [
      "mind-git-compiler.json",
      "mind-git-math.json", 
      "mind-git-p2p.json",
      "mind-git-visualizer.json"
    ];

    for (const file of toolFiles) {
      const filePath = join(toolsDir, file);
      if (existsSync(filePath)) {
        const toolName = file.replace(".json", "");
        tools[toolName] = JSON.parse(readFileSync(filePath, "utf8"));
      }
    }

    return tools;
  }

  loadAgents() {
    const agentsDir = join(__dirname, ".opencode", "agents");
    const agents = {};
    
    const agentFiles = [
      "canvasl-compiler.json",
      "mathematical-verification.json",
      "p2p-collaboration.json"
    ];

    for (const file of agentFiles) {
      const filePath = join(agentsDir, file);
      if (existsSync(filePath)) {
        const agentName = file.replace(".json", "");
        agents[agentName] = JSON.parse(readFileSync(filePath, "utf8"));
      }
    }

    return agents;
  }

  async initializeSession(title = "mind-git Session") {
    try {
      const session = await this.client.session.create({
        body: {
          title,
          model: this.config.model || {
            providerID: "anthropic",
            modelID: "claude-3-5-sonnet-20241022"
          }
        }
      });

      // Inject mind-git context
      await this.client.session.prompt({
        path: { id: session.id },
        body: {
          noReply: true,
          parts: [{
            type: "text",
            text: this.getSystemPrompt()
          }]
        }
      });

      return session;
    } catch (error) {
      console.error("Failed to initialize session:", error);
      throw error;
    }
  }

  getSystemPrompt() {
    return `You are now integrated with the mind-git ecosystem - the world's most advanced VR spatial programming system with mathematical foundation.

Available tools:
${Object.keys(this.tools).map(tool => `- ${tool}: ${this.tools[tool].description}`).join('\n')}

Available specialized agents:
${Object.keys(this.agents).map(agent => `- ${agent}: ${this.agents[agent].description}`).join('\n')}

Mathematical constraints:
- Maintain polynomial algebra over F₂
- Preserve norm preservation in all operations  
- Follow Adams' dimensional constraints (1, 2, 4, 8 dimensions only)
- Ensure formal verification matches implementation

CanvasL Node Types:
- #Activate: (D0) Linear transformations - JMP operations
- #Integrate: (D1) Polynomial addition - ADD operations
- #Propagate: (D2) Polynomial shift - SHL operations
- #BackPropagate: (D3) Polynomial comparison - CMP operations
- #Transform: (D4) Polynomial multiplication - MUL operations
- #Verify: (D5) Consensus voting - VOTE operations
- #Store: (D6) Memory stack - PUSH operations
- #Observe: (D7) Quantum observation - SYNC operations

Always prioritize mathematical integrity and use the specialized agents for complex operations.`;
  }

  async compileCanvas(canvasPath, options = {}) {
    const session = await this.initializeSession("Canvas Compilation");
    
    try {
      const result = await this.client.session.prompt({
        path: { id: session.id },
        body: {
          parts: [{
            type: "text",
            text: `Please compile the CanvasL file at ${canvasPath} using the canvasl-compiler agent. Options: ${JSON.stringify(options)}`
          }]
        }
      });

      return result;
    } finally {
      await this.client.session.delete({ path: { id: session.id } });
    }
  }

  async verifyMathematics(operation, data) {
    const session = await this.initializeSession("Mathematical Verification");
    
    try {
      const result = await this.client.session.prompt({
        path: { id: session.id },
        body: {
          parts: [{
            type: "text", 
            text: `Please verify the mathematical operation "${operation}" with data: ${JSON.stringify(data)} using the mathematical-verification agent.`
          }]
        }
      });

      return result;
    } finally {
      await this.client.session.delete({ path: { id: session.id } });
    }
  }

  async setupCollaboration(repository, peer, options = {}) {
    const session = await this.initializeSession("P2P Collaboration Setup");
    
    try {
      const result = await this.client.session.prompt({
        path: { id: session.id },
        body: {
          parts: [{
            type: "text",
            text: `Please set up P2P collaboration for repository "${repository}" with peer "${peer}" using the p2p-collaboration agent. Options: ${JSON.stringify(options)}`
          }]
        }
      });

      return result;
    } finally {
      await this.client.session.delete({ path: { id: session.id } });
    }
  }

  async listTools() {
    return Object.keys(this.tools).map(name => ({
      name,
      ...this.tools[name]
    }));
  }

  async listAgents() {
    return Object.keys(this.agents).map(name => ({
      name,
      ...this.agents[name]
    }));
  }

  async getStatus() {
    try {
      const config = await this.client.config.get();
      const currentProject = await this.client.project.current();
      
      return {
        connected: true,
        config,
        project: currentProject,
        tools: Object.keys(this.tools),
        agents: Object.keys(this.agents)
      };
    } catch (error) {
      return {
        connected: false,
        error: error.message
      };
    }
  }
}

// CLI Interface
async function main() {
  const command = process.argv[2];
  const integration = new MindGitOpenCodeIntegration();

  switch (command) {
    case "status":
      const status = await integration.getStatus();
      console.log(JSON.stringify(status, null, 2));
      break;

    case "tools":
      const tools = await integration.listTools();
      console.log(JSON.stringify(tools, null, 2));
      break;

    case "agents":
      const agents = await integration.listAgents();
      console.log(JSON.stringify(agents, null, 2));
      break;

    case "compile":
      const canvasPath = process.argv[3];
      if (!canvasPath) {
        console.error("Usage: mind-git-opencode compile <canvas-path>");
        process.exit(1);
      }
      await integration.compileCanvas(canvasPath);
      break;

    case "verify":
      const operation = process.argv[3];
      const dataArg = process.argv[4];
      if (!operation || !dataArg) {
        console.error("Usage: mind-git-opencode verify <operation> <data-json>");
        process.exit(1);
      }
      try {
        const data = JSON.parse(dataArg);
        await integration.verifyMathematics(operation, data);
      } catch (error) {
        console.error("Invalid JSON data:", error.message);
        process.exit(1);
      }
      break;

    case "collaborate":
      const repository = process.argv[3];
      const peer = process.argv[4];
      if (!repository || !peer) {
        console.error("Usage: mind-git-opencode collaborate <repository> <peer>");
        process.exit(1);
      }
      await integration.setupCollaboration(repository, peer);
      break;

    default:
      console.log(`
mind-git OpenCode Integration

Usage:
  mind-git-opencode status                    Show connection status and available tools/agents
  mind-git-opencode tools                     List available tools
  mind-git-opencode agents                    List available specialized agents
  mind-git-opencode compile <canvas-path>     Compile a CanvasL file
  mind-git-opencode verify <op> <data-json>   Verify mathematical operation
  mind-git-opencode collaborate <repo> <peer> Setup P2P collaboration

Examples:
  mind-git-opencode compile examples/spatial-hello-world.canvas
  mind-git-opencode verify norm-preservation '{"dimension": 4, "vectors": [[1,0,0,0], [0,1,0,0]]}'
  mind-git-opencode collaborate my-canvas-project alice
      `);
  }
}

if (import.meta.url === `file://${process.argv[1]}`) {
  main().catch(console.error);
}

export default MindGitOpenCodeIntegration;