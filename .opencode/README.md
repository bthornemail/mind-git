# mind-git OpenCode Integration

Complete integration package for connecting mind-git's mathematical foundation and spatial programming capabilities with OpenCode's AI-powered development environment.

## 🚀 Quick Start

### Installation

1. Install OpenCode SDK:
```bash
npm install @opencode-ai/sdk
```

2. The mind-git OpenCode integration is already included in the `.opencode/` directory.

3. Start OpenCode with mind-git integration:
```bash
opencode
```

### Basic Usage

```bash
# Check integration status
node .opencode/client.js status

# Compile a CanvasL file
node .opencode/client.js compile examples/spatial-hello-world.canvas

# Verify mathematical operations
node .opencode/client.js verify norm-preservation '{"dimension": 4, "vectors": [[1,0,0,0], [0,1,0,0]]}'

# Setup P2P collaboration
node .opencode/client.js collaborate my-canvas-project alice
```

## 📁 Directory Structure

```
.opencode/
├── config.json                    # Main OpenCode configuration
├── client.js                      # Integration client and CLI
├── tools/                         # mind-git specific tools
│   ├── mind-git-compiler.json     # CanvasL visual compiler
│   ├── mind-git-math.json         # Mathematical foundation tools
│   ├── mind-git-p2p.json          # P2P collaboration system
│   └── mind-git-visualizer.json   # WebGL visualization tools
└── agents/                        # Specialized AI agents
    ├── canvasl-compiler.json      # CanvasL compilation expert
    ├── mathematical-verification.json # Formal verification expert
    └── p2p-collaboration.json     # Real-time collaboration expert
```

## 🛠️ Available Tools

### mind-git-compiler
CanvasL visual compiler for spatial programming with mathematical verification.

**Features:**
- Parse and validate .canvas files
- Generate AST representations
- Multi-language code generation (JavaScript, TypeScript, Racket, WebAssembly)
- Formal verification integration
- Performance optimization

**Commands:**
```bash
# Compile to JavaScript
mind-git-compiler compile examples/spatial-hello-world.canvas --target javascript

# Compile with verification
mind-git-compiler compile examples/math-demo.canvas --verify --target typescript

# Validate canvas structure
mind-git-compiler validate examples/complex-canvas.canvas
```

### mind-git-math
Mathematical foundation tools for polynomial algebra and identity chain operations.

**Features:**
- Polynomial operations over F₂
- Identity chain implementations (Brahmagupta → Euler → Degen → Pfister)
- Norm preservation verification
- Adams' theorem compliance checking
- Hopf fibration mathematical properties

**Commands:**
```bash
# Polynomial operations
mind-git-math polynomial add "x^3 + x + 1" "x^2 + 1"
mind-git-math polynomial multiply "x^2 + 1" "x + 1"

# Identity chain operations
mind-git-math identity 4 euler [[1,0,0,0], [0,1,0,0]]

# Mathematical verification
mind-git-math verify norm-preservation --data '{"dimension": 8, "vectors": [...]}'
```

### mind-git-p2p
MQTT-based P2P real-time collaboration system for canvas synchronization.

**Features:**
- Real-time canvas synchronization
- Conflict resolution (OT, CRDT)
- Peer discovery and network management
- Offline support with sync recovery
- Encrypted communication channels

**Commands:**
```bash
# Connect to P2P network
mind-git-p2p connect --repository my-project --peer alice

# Start real-time synchronization
mind-git-p2p sync examples/collaborative.canvas --mode real-time

# Broadcast updates
mind-git-p2p broadcast --message "Canvas updated" --type canvas-update
```

### mind-git-visualizer
WebGL-based visualization tools for mathematical structures and polynomial operations.

**Features:**
- Interactive polynomial visualization
- Hopf fibration rendering
- E₈ lattice visualization
- Canvas graph visualization
- Export to multiple formats (HTML, SVG, WebGL)

**Commands:**
```bash
# Visualize polynomial structure
mind-git-visualizer visualize polynomial "x^4 + x^2 + 1" --output viz.html

# Create Hopf fibration visualization
mind-git-visualizer visualize hopf-fibration "[1,0,0,0]" --interactive

# Export visualization
mind-git-visualizer export html viz.html export.html
```

## 🤖 Specialized Agents

### canvasl-compiler
Expert agent for CanvasL visual programming language compilation and optimization.

**Capabilities:**
- Canvas parsing and validation
- AST generation and optimization
- Multi-language code generation
- Mathematical verification
- Performance optimization
- Visual debugging assistance

**Usage:**
```
Ask the agent to "compile the spatial hello world canvas with verification" or
"optimize this polynomial multiplication canvas for better performance"
```

### mathematical-verification
Expert agent for formal mathematical verification and theorem proving.

**Capabilities:**
- Formal mathematical verification
- Coq proof extraction and validation
- Theorem proving and validation
- Mathematical property checking
- Norm preservation verification
- Dimensional constraint validation

**Usage:**
```
Ask the agent to "verify norm preservation for quaternion multiplication" or
"validate that this 4D operation follows Adams' theorem"
```

### p2p-collaboration
Expert agent for real-time P2P collaboration and canvas synchronization.

**Capabilities:**
- P2P network management
- Real-time canvas synchronization
- Conflict resolution and operational transformation
- Peer discovery and network topology
- Collaborative editing support
- Network optimization and performance tuning

**Usage:**
```
Ask the agent to "setup a collaborative session for team canvas editing" or
"handle network partition recovery for our P2P session"
```

## ⚙️ Configuration

### Main Configuration (.opencode/config.json)

```json
{
  "$schema": "https://opencode.ai/schema/config.json",
  "model": "anthropic/claude-3-5-sonnet-20241022",
  "tools": [
    ".opencode/tools/mind-git-compiler.json",
    ".opencode/tools/mind-git-math.json",
    ".opencode/tools/mind-git-p2p.json",
    ".opencode/tools/mind-git-visualizer.json"
  ],
  "agents": [
    ".opencode/agents/canvasl-compiler.json",
    ".opencode/agents/mathematical-verification.json",
    ".opencode/agents/p2p-collaboration.json"
  ],
  "rules": [
    "Maintain mathematical integrity in all operations",
    "Follow CanvasL visual programming language specifications",
    "Preserve norm preservation in polynomial algebra",
    "Ensure formal verification matches implementation"
  ],
  "workspace": {
    "include": [
      "logos-system/**/*",
      "examples/**/*",
      "demos/**/*",
      "dev-docs/**/*"
    ],
    "exclude": [
      "node_modules/**/*",
      ".git/**/*",
      "*.log"
    ]
  }
}
```

## 🔧 Advanced Usage

### Programmatic Integration

```javascript
import MindGitOpenCodeIntegration from './.opencode/client.js';

const integration = new MindGitOpenCodeIntegration({
  baseUrl: "http://localhost:4096"
});

// Compile canvas with custom options
const result = await integration.compileCanvas(
  'examples/advanced-math.canvas',
  { target: 'webassembly', verify: true }
);

// Verify mathematical properties
const verification = await integration.verifyMathematics(
  'norm-preservation',
  { dimension: 8, vectors: [...] }
);

// Setup collaboration session
const collaboration = await integration.setupCollaboration(
  'team-project',
  'alice',
  { mode: 'real-time', conflict: 'operational-transform' }
);
```

### Custom Tool Integration

Create custom tools by adding JSON files to `.opencode/tools/`:

```json
{
  "name": "my-custom-tool",
  "description": "Custom mind-git integration tool",
  "version": "1.0.0",
  "type": "tool",
  "entry": "path/to/tool.js",
  "parameters": {
    // Define tool parameters
  },
  "commands": {
    // Define command mappings
  }
}
```

### Custom Agent Integration

Create specialized agents by adding JSON files to `.opencode/agents/`:

```json
{
  "name": "my-specialized-agent",
  "description": "Custom AI agent for specific tasks",
  "version": "1.0.0",
  "type": "agent",
  "model": "anthropic/claude-3-5-sonnet-20241022",
  "system": "System prompt for the agent...",
  "tools": ["mind-git-compiler", "mind-git-math"],
  "capabilities": [
    "List of agent capabilities"
  ]
}
```

## 📚 Mathematical Foundation

### CanvasL Node Types

| Prefix | Dimension | Assembly Op | Mathematical Meaning |
|--------|-----------|-------------|---------------------|
| `#Activate:` | D0 | `JMP` | Linear transformation |
| `#Integrate:` | D1 | `ADD` | Polynomial addition |
| `#Propagate:` | D2 | `SHL` | Polynomial shift |
| `#BackPropagate:` | D3 | `CMP` | Polynomial comparison |
| `#Transform:` | D4 | `MUL` | Polynomial multiplication |
| `#Verify:` | D5 | `VOTE` | Consensus voting |
| `#Store:` | D6 | `PUSH` | Memory stack operation |
| `#Observe:` | D7 | `SYNC` | Quantum observation |

### Mathematical Constraints

- **Dimensional Limits**: Only 1, 2, 4, 8 dimensions allow normed division algebras (Adams' Theorem)
- **Norm Preservation**: `||a × b|| = ||a|| × ||b||` must be exact
- **Polynomial Algebra**: All operations over F₂ (boolean coefficients)
- **Identity Chain**: Brahmagupta → Euler → Degen → Pfister sequence

## 🚀 Production Deployment

### Docker Integration

```dockerfile
FROM node:18-alpine

# Install mind-git and OpenCode
RUN npm install -g @opencode-ai/cli
COPY . /app
WORKDIR /app

# Install dependencies
RUN npm install

# Expose OpenCode port
EXPOSE 4096

# Start OpenCode with mind-git integration
CMD ["opencode", "--config", ".opencode/config.json"]
```

### Kubernetes Deployment

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: mind-git-opencode
spec:
  replicas: 3
  selector:
    matchLabels:
      app: mind-git-opencode
  template:
    metadata:
      labels:
        app: mind-git-opencode
    spec:
      containers:
      - name: mind-git-opencode
        image: mind-git/opencode:latest
        ports:
        - containerPort: 4096
        env:
        - name: OPENCODE_CONFIG
          value: ".opencode/config.json"
```

## 🤝 Contributing

### Adding New Tools

1. Create tool definition in `.opencode/tools/`
2. Implement tool functionality
3. Add tests and documentation
4. Update configuration if needed

### Adding New Agents

1. Create agent definition in `.opencode/agents/`
2. Define system prompt and capabilities
3. Specify required tools
4. Test with OpenCode integration

### Testing

```bash
# Test integration status
node .opencode/client.js status

# Test tool functionality
node .opencode/client.js compile examples/test.canvas

# Test mathematical verification
node .opencode/client.js verify adams-theorem '{"dimension": 3}'
```

## 📖 Additional Resources

- [mind-git Main Documentation](../README.md)
- [CanvasL Language Specification](../dev-docs/2._CanvasL_Language_Specification/)
- [Mathematical Foundation](../dev-docs/1._Mathematical_Foundation/)
- [P2P Collaboration Guide](../dev-docs/4._P2P_Collaboration/)
- [OpenCode SDK Documentation](https://opencode.ai/docs/sdk/)

## 📄 License

This integration package is part of the mind-git project and licensed under the MIT License. See [../LICENSE](../LICENSE) for details.