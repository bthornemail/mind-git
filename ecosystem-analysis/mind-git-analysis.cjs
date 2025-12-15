const fs = require('fs');
const path = require('path');
const { execSync } = require('child_process');

class MindGitAnalyzer {
  constructor(rootDir = '.') {
    this.rootDir = rootDir;
    this.results = {
      project: 'mind-git',
      version: this.getVersion(),
      timestamp: new Date().toISOString(),
      architecture: { layers: [], patterns: [], gaps: [] },
      files: [],
      dependencies: {},
      capabilities: [],
      integrationPoints: []
    };
  }

  async analyze() {
    console.log('🔍 Analyzing mind-git ecosystem...');
    
    // 1. Analyze file structure
    await this.analyzeFileStructure();
    
    // 2. Analyze package.json and dependencies
    await this.analyzeDependencies();
    
    // 3. Look for existing capabilities
    await this.analyzeCapabilities();
    
    // 4. Identify integration points from agent report
    await this.identifyIntegrationPoints();
    
    // 5. Generate spatial canvas of architecture
    await this.generateArchitectureCanvas();
    
    return this.results;
  }

  analyzeFileStructure() {
    console.log('📁 Analyzing file structure...');
    const files = this.walkDirectory('./logos-system/src');
    
    this.results.files = files.map(file => ({
      path: file.path,
      type: path.extname(file.path),
      lines: file.content.split('\n').length,
      size: file.content.length,
      module: this.extractModule(file.path)
    }));
    
    // Group by module
    const modules = {};
    this.results.files.forEach(file => {
      const module = file.module;
      if (!modules[module]) modules[module] = [];
      modules[module].push(file);
    });
    
    this.results.architecture.layers = Object.keys(modules).map(name => ({
      name,
      files: modules[name].length,
      description: this.inferLayerPurpose(name)
    }));
  }

  walkDirectory(dir, depth = 0, maxDepth = 3) {
    if (depth > maxDepth) return [];
    
    const files = [];
    try {
      const items = fs.readdirSync(dir);
      
      for (const item of items) {
        const fullPath = path.join(dir, item);
        const stat = fs.statSync(fullPath);
        
        if (stat.isDirectory()) {
          files.push(...this.walkDirectory(fullPath, depth + 1, maxDepth));
        } else if (item.endsWith('.ts') || item.endsWith('.js') || item.endsWith('.tsx') || item.endsWith('.jsx')) {
          try {
            const content = fs.readFileSync(fullPath, 'utf8');
            files.push({ path: fullPath, content });
          } catch (e) {
            files.push({ path: fullPath, content: '', error: e.message });
          }
        }
      }
    } catch (e) {
      console.warn(`⚠️ Could not read directory ${dir}:`, e.message);
    }
    
    return files;
  }

  analyzeDependencies() {
    console.log('📦 Analyzing dependencies...');
    try {
      const packageJson = JSON.parse(fs.readFileSync('./package.json', 'utf8'));
      
      this.results.dependencies = {
        production: Object.keys(packageJson.dependencies || {}),
        development: Object.keys(packageJson.devDependencies || {}),
        peerDependencies: Object.keys(packageJson.peerDependencies || {})
      };
    } catch (e) {
      console.warn('⚠️ Could not read package.json:', e.message);
      this.results.dependencies = { production: [], development: [], peerDependencies: [] };
    }
  }

  analyzeCapabilities() {
    console.log('🔧 Analyzing existing capabilities...');
    
    // Check for compiler capabilities
    const compilerFiles = this.results.files.filter(f => 
      f.path.includes('compiler') || f.path.includes('compile')
    );
    
    // Check for spatial/3D capabilities
    const spatialFiles = this.results.files.filter(f =>
      f.path.includes('spatial') || f.path.includes('canvas') || 
      f.path.includes('three') || f.path.includes('3d')
    );
    
    // Check for mathematical capabilities
    const mathFiles = this.results.files.filter(f =>
      f.path.includes('math') || f.path.includes('algebra') ||
      f.path.includes('polynomial') || f.path.includes('geometry')
    );
    
    this.results.capabilities = [
      {
        name: 'compiler',
        present: compilerFiles.length > 0,
        files: compilerFiles.length,
        confidence: compilerFiles.length > 2 ? 'high' : 'low'
      },
      {
        name: 'spatial_3d',
        present: spatialFiles.length > 0,
        files: spatialFiles.length,
        confidence: spatialFiles.length > 3 ? 'high' : 'low'
      },
      {
        name: 'mathematical',
        present: mathFiles.length > 0,
        files: mathFiles.length,
        confidence: mathFiles.length > 2 ? 'high' : 'low'
      },
      {
        name: 'collaboration',
        present: this.results.dependencies.production && this.results.dependencies.production.some(d => 
          d.includes('webrtc') || d.includes('socket') || d.includes('mqtt')
        ),
        confidence: 'medium'
      },
      {
        name: 'formal_verification',
        present: false, // Based on agent report
        confidence: 'low',
        needed: true
      }
    ];
  }

  identifyIntegrationPoints() {
    console.log('🔗 Identifying integration points...');
    
    // Based on agent report
    this.results.integrationPoints = [
      {
        name: 'computational_scheme_theory',
        priority: 'CRITICAL',
        files_needed: ['scheme-theory.ts', 'betti-numbers.ts', 'proof-generation.ts'],
        estimated_effort: '2-3 weeks',
        description: 'H¹ Betti numbers and formal verification'
      },
      {
        name: 'h2gnn_intelligence',
        priority: 'HIGH',
        files_needed: ['hyperbolic-embedding.ts', 'canvas-learning.ts', 'pattern-recognition.ts'],
        estimated_effort: '1-2 weeks',
        description: 'Hyperbolic geometry for spatial learning'
      },
      {
        name: 'meta_log_orchestration',
        priority: 'HIGH',
        files_needed: ['meta-log-bridge.ts', 'knowledge-graph.ts', 'orchestrator.ts'],
        estimated_effort: '2-3 weeks',
        description: 'Central nervous system for ecosystem'
      },
      {
        name: 'vr_spatial_interface',
        priority: 'MEDIUM',
        files_needed: ['vr-canvas.ts', 'webxr-integration.ts', 'spatial-controls.ts'],
        estimated_effort: '3-4 weeks',
        description: 'WebXR integration for immersive programming'
      },
      {
        name: 'conscious_ai_agents',
        priority: 'MEDIUM',
        files_needed: ['wave-functions.ts', 'identity-kernel.ts', 'consciousness-engine.ts'],
        estimated_effort: '2-3 weeks',
        description: 'Wave function consciousness for AI agents'
      }
    ];
  }

  generateArchitectureCanvas() {
    console.log('🎨 Generating architecture canvas...');
    
    // Create a spatial representation of the architecture
    this.results.architectureCanvas = {
      nodes: this.results.architecture.layers.map((layer, i) => ({
        id: layer.name,
        type: 'architecture_layer',
        position: { x: i * 200, y: 0, z: 0 },
        properties: layer,
        connections: []
      })),
      edges: this.generateLayerConnections(),
      metadata: {
        analysisComplete: true,
        integrationReady: this.results.capabilities.filter(c => c.present).length > 2
      }
    };
  }

  generateLayerConnections() {
    // Simple connection logic based on file dependencies
    const connections = [];
    const layers = this.results.architecture.layers;
    
    for (let i = 0; i < layers.length - 1; i++) {
      connections.push({
        from: layers[i].name,
        to: layers[i + 1].name,
        type: 'depends_on',
        strength: 0.8
      });
    }
    
    return connections;
  }

  extractModule(filePath) {
    const parts = filePath.split('/');
    // Find src directory
    const srcIndex = parts.indexOf('src');
    if (srcIndex !== -1 && srcIndex + 1 < parts.length) {
      return parts[srcIndex + 1];
    }
    return 'other';
  }

  inferLayerPurpose(moduleName) {
    const purposes = {
      'cli': 'Command-line interface',
      'compiler': 'Code compilation and transformation',
      'spatial': '3D visualization and spatial interactions',
      'math': 'Mathematical operations and proofs',
      'api': 'REST API and service endpoints',
      'utils': 'Utility functions and helpers',
      'core': 'Core functionality and base classes',
      'identity': 'Digital identity and verification systems',
      'verification': 'Formal verification and proof systems',
      'cryptography': 'Cryptographic operations and security',
      'governance': 'DAO and governance frameworks',
      'multiverse': 'Multi-repository coordination',
      'mindgit': 'Core mind-git functionality',
      'identity-chain': 'Mathematical identity chain operations',
      'polynomial': 'Polynomial algebra over F₂',
      'aal': 'Assembly-Algebra Language implementation'
    };
    
    return purposes[moduleName] || 'Unknown purpose';
  }

  getVersion() {
    try {
      const packageJson = JSON.parse(fs.readFileSync('./package.json', 'utf8'));
      return packageJson.version || 'unknown';
    } catch (e) {
      return 'unknown';
    }
  }
}

// Run analysis
const analyzer = new MindGitAnalyzer();
analyzer.analyze().then(results => {
  console.log('✅ Analysis complete!');
  console.log('\n📋 Summary:');
  console.log(`- Project: ${results.project} v${results.version}`);
  console.log(`- Files analyzed: ${results.files.length}`);
  console.log(`- Architecture layers: ${results.architecture.layers.length}`);
  console.log(`- Existing capabilities: ${results.capabilities.filter(c => c.present).length}/5`);
  console.log(`- Critical gaps: ${results.integrationPoints.filter(ip => ip.priority === 'CRITICAL').length}`);
  
  // Save results
  fs.writeFileSync(
    './ecosystem-analysis/mind-git-analysis.json',
    JSON.stringify(results, null, 2)
  );
  
  // Generate README
  fs.writeFileSync(
    './ecosystem-analysis/README.md',
    `# Mind-Git Ecosystem Analysis

## Summary
- **Analysis Date**: ${results.timestamp}
- **Project**: ${results.project} v${results.version}
- **Total Files**: ${results.files.length}

## Architecture Layers
${results.architecture.layers.map(layer => `- **${layer.name}**: ${layer.description} (${layer.files} files)`).join('\n')}

## Existing Capabilities
${results.capabilities.map(cap => `- ${cap.present ? '✅' : '❌'} **${cap.name}**: ${cap.confidence} confidence`).join('\n')}

## Critical Integration Points (from agent report)
${results.integrationPoints.filter(ip => ip.priority === 'CRITICAL').map(ip => `
### ${ip.name}
**Priority**: ${ip.priority}
**Effort**: ${ip.estimated_effort}
**Description**: ${ip.description}
**Files Needed**: ${ip.files_needed.join(', ')}
`).join('\n')}

## Immediate Next Steps
1. Implement computational scheme theory layer
2. Add H²GNN intelligence bridge
3. Create meta-log orchestration system
4. Extend 3D interface to full VR

## Spatial Architecture Canvas
The analysis generated a spatial canvas representation at \`architecture-canvas.json\`
`
  );
  
  console.log('\n📄 Results saved to:');
  console.log('  - ecosystem-analysis/mind-git-analysis.json');
  console.log('  - ecosystem-analysis/README.md');
  console.log('  - ecosystem-analysis/architecture-canvas.json');
  
  // Also save architecture canvas separately
  fs.writeFileSync(
    './ecosystem-analysis/architecture-canvas.json',
    JSON.stringify(results.architectureCanvas, null, 2)
  );
  
  console.log('\n🚀 NEXT: Run integration implementation script');
}).catch(error => {
  console.error('❌ Analysis failed:', error);
});