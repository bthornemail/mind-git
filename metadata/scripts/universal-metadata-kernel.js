#!/usr/bin/env node

/**
 * MIND-GIT Universal Metadata Kernel
 * 
 * A universal system for adding metadata to any Git repository
 * and creating human-understandable interfaces to complex systems
 */

import fs from 'fs';
import { promises as fsAsync } from 'fs';
import path from 'path';
import { execSync } from 'child_process';
import crypto from 'crypto';

console.log('🧠 MIND-GIT Universal Metadata Kernel');
console.log('='.repeat(80));

class UniversalMetadataKernel {
  constructor(repoPath = process.cwd()) {
    this.repoPath = repoPath;
    this.metadataDir = path.join(repoPath, '.metadata-kernel');
    this.ensureDirectories();
  }

  ensureDirectories() {
    const dirs = [
      this.metadataDir,
      path.join(this.metadataDir, 'components'),
      path.join(this.metadataDir, 'relationships'),
      path.join(this.metadataDir, 'exports'),
      path.join(this.metadataDir, 'templates')
    ];
    
    dirs.forEach(dir => {
      if (!fs.existsSync(dir)) {
        fs.mkdirSync(dir, { recursive: true });
      }
    });
  }

  /**
   * Analyze any Git repository and generate metadata kernel
   */
  async analyzeRepository() {
    console.log(`🔍 Analyzing repository: ${this.repoPath}`);
    
    // 1. Detect repository type and structure
    const repoInfo = await this.detectRepositoryType();
    
    // 2. Scan for all relevant files
    const files = await this.scanRepository();
    
    // 3. Generate metadata for each component
    const components = await this.generateComponentMetadata(files, repoInfo);
    
    // 4. Create relationships between components
    const relationships = await this.generateRelationships(components);
    
    // 5. Generate AGENTS.md files
    await this.generateAgentsFiles(components);
    
    // 6. Create export system
    await this.createExportSystem(components);
    
    // 7. Generate CanvasL visualization
    await this.generateCanvasLVisualization(components);
    
    return {
      repoInfo,
      components,
      relationships,
      kernelPath: this.metadataDir
    };
  }

  /**
   * Detect repository type and characteristics
   */
  async detectRepositoryType() {
    const repoInfo = {
      type: 'unknown',
      languages: [],
      frameworks: [],
      buildSystems: [],
      testFrameworks: [],
      mathematical: false,
      hasTests: false,
      hasDocs: false,
      hasCI: false
    };

    // Check for package.json
    const packageJsonPath = path.join(this.repoPath, 'package.json');
    if (fs.existsSync(packageJsonPath)) {
      try {
        const packageJson = JSON.parse(fs.readFileSync(packageJsonPath, 'utf8'));
        repoInfo.type = 'nodejs';
        repoInfo.languages.push('javascript', 'typescript');
        
        if (packageJson.dependencies) {
          repoInfo.frameworks = Object.keys(packageJson.dependencies);
        }
        
        if (packageJson.scripts) {
          repoInfo.buildSystems = Object.keys(packageJson.scripts)
            .filter(script => script.includes('build') || script.includes('test'));
        }
      } catch (error) {
        console.warn('⚠️ Could not parse package.json');
      }
    }

    // Check for Python
    if (fs.existsSync(path.join(this.repoPath, 'setup.py')) ||
        fs.existsSync(path.join(this.repoPath, 'requirements.txt')) ||
        fs.existsSync(path.join(this.repoPath, 'pyproject.toml'))) {
      repoInfo.type = 'python';
      repoInfo.languages.push('python');
    }

    // Check for Rust
    if (fs.existsSync(path.join(this.repoPath, 'Cargo.toml'))) {
      repoInfo.type = 'rust';
      repoInfo.languages.push('rust');
    }

    // Check for mathematical content
    const files = await this.scanRepository();
    const hasMathematical = files.some(file => {
      try {
        const content = fs.readFileSync(file, 'utf8');
        return content.includes('polynomial') || 
               content.includes('algebra') || 
               content.includes('theorem') || 
               content.includes('proof') ||
               content.includes('coq') ||
               content.includes('lean');
      } catch (error) {
        return false;
      }
    });
    
    repoInfo.mathematical = hasMathematical;
    repoInfo.hasTests = files.some(file => file.includes('.test.') || file.includes('.spec.'));
    repoInfo.hasDocs = files.some(file => 
      file.includes('README') || 
      file.includes('docs/') || 
      file.includes('doc/')
    );
    repoInfo.hasCI = files.some(file => 
      file.includes('.github/workflows/') || 
      file.includes('.gitlab-ci.yml') ||
      file.includes('Dockerfile')
    );

    return repoInfo;
  }

  /**
   * Scan repository for relevant files
   */
  async scanRepository() {
    const files = [];
    
    const scanDirectory = (dir) => {
      try {
        const items = fs.readdirSync(dir);
        
        for (const item of items) {
          const fullPath = path.join(dir, item);
          const stat = fs.statSync(fullPath);
          
          if (stat.isDirectory() && !item.startsWith('.') && item !== 'node_modules') {
            scanDirectory(fullPath);
          } else if (stat.isFile()) {
            const ext = path.extname(item);
            if (['.md', '.js', '.ts', '.py', '.rs', '.java', '.cpp', '.c', '.h'].includes(ext)) {
              files.push(fullPath);
            }
          }
        }
      } catch (error) {
        // Skip directories we can't read
      }
    };
    
    scanDirectory(this.repoPath);
    return files;
  }

  /**
   * Generate metadata for components
   */
  async generateComponentMetadata(files, repoInfo) {
    const components = [];
    
    // Group files by directory
    const fileGroups = files.reduce((groups, file) => {
      const relativePath = path.relative(this.repoPath, file);
      const dir = path.dirname(relativePath);
      
      if (!groups[dir]) groups[dir] = [];
      groups[dir].push(file);
      
      return groups;
    }, {});

    for (const [dir, dirFiles] of Object.entries(fileGroups)) {
      const component = await this.analyzeComponent(dir, dirFiles, repoInfo);
      if (component) {
        components.push(component);
      }
    }

    return components;
  }

  /**
   * Analyze a single component directory
   */
  async analyzeComponent(dir, files, repoInfo) {
    const relativePath = dir === '.' ? 'root' : dir;
    const component = {
      id: `kernel:${relativePath.replace(/[^a-zA-Z0-9]/g, '-')}`,
      path: relativePath,
      files: files.map(f => path.relative(this.repoPath, f)),
      metadata: {
        type: this.inferComponentType(dir, files),
        layer: this.inferLayer(dir, files),
        complexity: this.calculateComplexity(files),
        mathematical: this.analyzeMathematicalContent(files),
        dependencies: this.extractDependencies(files),
        tests: this.findTestFiles(files),
        documentation: this.findDocumentationFiles(files)
      }
    };

    return component;
  }

  /**
   * Infer component type from files
   */
  inferComponentType(dir, files) {
    const dirLower = dir.toLowerCase();
    const fileNames = files.map(f => path.basename(f).toLowerCase());
    
    if (dirLower.includes('test') || fileNames.some(f => f.includes('.test.') || f.includes('.spec.'))) {
      return 'test';
    }
    if (dirLower.includes('doc') || fileNames.some(f => f.includes('readme'))) {
      return 'documentation';
    }
    if (dirLower.includes('src') || dirLower.includes('lib')) {
      return 'source';
    }
    if (dirLower.includes('config') || fileNames.some(f => f.includes('config'))) {
      return 'configuration';
    }
    if (dirLower.includes('build') || fileNames.some(f => f.includes('webpack') || f.includes('vite'))) {
      return 'build';
    }
    
    return 'component';
  }

  /**
   * Infer layer based on directory and content
   */
  inferLayer(dir, files) {
    const dirLower = dir.toLowerCase();
    
    // Mathematical foundation
    if (dirLower.includes('math') || dirLower.includes('algebra') || dirLower.includes('theory')) {
      return 1;
    }
    
    // Core implementation
    if (dirLower.includes('src') || dirLower.includes('core') || dirLower.includes('lib')) {
      return 2;
    }
    
    // API/Interface
    if (dirLower.includes('api') || dirLower.includes('interface') || dirLower.includes('routes')) {
      return 3;
    }
    
    // Services/Business logic
    if (dirLower.includes('service') || dirLower.includes('business') || dirLower.includes('logic')) {
      return 4;
    }
    
    // Data layer
    if (dirLower.includes('data') || dirLower.includes('model') || dirLower.includes('database')) {
      return 5;
    }
    
    // UI/Presentation
    if (dirLower.includes('ui') || dirLower.includes('view') || dirLower.includes('component')) {
      return 6;
    }
    
    // Tests
    if (dirLower.includes('test') || dirLower.includes('spec')) {
      return 7;
    }
    
    // Documentation
    if (dirLower.includes('doc') || dirLower.includes('readme')) {
      return 8;
    }
    
    return 3; // Default to API layer
  }

  /**
   * Calculate complexity of component
   */
  calculateComplexity(files) {
    let complexity = 0;
    
    for (const file of files) {
      try {
        const content = fs.readFileSync(file, 'utf8');
        const lines = content.split('\n').length;
        
        // Base complexity from lines of code
        complexity += Math.log(lines + 1);
        
        // Add complexity for patterns
        if (content.includes('class ')) complexity += 2;
        if (content.includes('function ')) complexity += 1;
        if (content.includes('async ')) complexity += 1;
        if (content.includes('await ')) complexity += 1;
        if (content.includes('Promise')) complexity += 1;
        
        // Mathematical complexity
        if (content.includes('polynomial')) complexity += 3;
        if (content.includes('algebra')) complexity += 3;
        if (content.includes('theorem')) complexity += 5;
        if (content.includes('proof')) complexity += 5;
        
      } catch (error) {
        // Skip files we can't read
      }
    }
    
    return Math.round(complexity);
  }

  /**
   * Analyze mathematical content
   */
  analyzeMathematicalContent(files) {
    const math = {
      hasMathematical: false,
      concepts: [],
      theorems: [],
      proofs: [],
      formalSystems: []
    };
    
    for (const file of files) {
      try {
        const content = fs.readFileSync(file, 'utf8');
        
        // Check for mathematical concepts
        const concepts = content.match(/\b(polynomial|algebra|theorem|proof|matrix|vector|calculus|geometry|topology|group|ring|field|category|functor|monad)\b/gi);
        if (concepts) {
          math.hasMathematical = true;
          math.concepts.push(...concepts.map(c => c.toLowerCase()));
        }
        
        // Check for theorems
        const theoremMatches = content.match(/theorem[:\s]*([^\n]+)/gi);
        if (theoremMatches) {
          math.theorems.push(...theoremMatches.map(m => m.replace(/theorem[:\s]*/gi, '').trim()));
        }
        
        // Check for formal systems
        if (content.includes('coq') || content.includes('lean') || content.includes('isabelle')) {
          math.formalSystems.push(content.includes('coq') ? 'coq' : 
                                   content.includes('lean') ? 'lean' : 'isabelle');
        }
        
      } catch (error) {
        // Skip files we can't read
      }
    }
    
    math.concepts = [...new Set(math.concepts)];
    math.theorems = [...new Set(math.theorems)];
    math.formalSystems = [...new Set(math.formalSystems)];
    
    return math;
  }

  /**
   * Extract dependencies from files
   */
  extractDependencies(files) {
    const dependencies = [];
    
    for (const file of files) {
      try {
        const content = fs.readFileSync(file, 'utf8');
        
        // Extract import/require statements
        const imports = content.match(/(?:import|require|from)\s+['"]([^'"]+)['"]/g);
        if (imports) {
          dependencies.push(...imports.map(imp => imp.replace(/(?:import|require|from)\s+['"]([^'"]+)['"]/g, '$1')));
        }
        
      } catch (error) {
        // Skip files we can't read
      }
    }
    
    return [...new Set(dependencies)];
  }

  /**
   * Find test files
   */
  findTestFiles(files) {
    return files.filter(file => 
      path.basename(file).includes('.test.') || 
      path.basename(file).includes('.spec.') ||
      path.dirname(file).toLowerCase().includes('test')
    );
  }

  /**
   * Find documentation files
   */
  findDocumentationFiles(files) {
    return files.filter(file => 
      path.basename(file).toLowerCase().includes('readme') ||
      path.extname(file) === '.md' ||
      path.dirname(file).toLowerCase().includes('doc')
    );
  }

  /**
   * Generate relationships between components
   */
  async generateRelationships(components) {
    const relationships = [];
    
    for (const component of components) {
      // Dependency relationships
      for (const dep of component.metadata.dependencies) {
        const targetComponent = components.find(c => 
          c.path === dep || c.files.some(f => f.includes(dep))
        );
        
        if (targetComponent) {
          relationships.push({
            type: 'dependency',
            from: component.id,
            to: targetComponent.id,
            strength: this.calculateDependencyStrength(component, targetComponent)
          });
        }
      }
      
      // Layer relationships
      const sameLayerComponents = components.filter(c => 
        c.metadata.layer === component.metadata.layer && c.id !== component.id
      );
      
      for (const sameLayer of sameLayerComponents) {
        relationships.push({
          type: 'layer-peer',
          from: component.id,
          to: sameLayer.id,
          strength: 0.5
        });
      }
    }
    
    return relationships;
  }

  /**
   * Calculate dependency strength
   */
  calculateDependencyStrength(from, to) {
    // Simple heuristic based on layer difference and complexity
    const layerDiff = Math.abs(from.metadata.layer - to.metadata.layer);
    const complexityRatio = to.metadata.complexity / (from.metadata.complexity + 1);
    
    return Math.max(0.1, 1 - (layerDiff * 0.2) - (complexityRatio * 0.1));
  }

  /**
   * Generate AGENTS.md files for components
   */
  async generateAgentsFiles(components) {
    for (const component of components) {
      const agentsContent = this.generateAgentsContent(component);
      const agentsPath = path.join(this.repoPath, component.path, 'AGENTS.md');
      
      try {
        await fsAsync.writeFile(agentsPath, agentsContent);
        console.log(`  📝 Generated AGENTS.md for ${component.path}`);
      } catch (error) {
        console.warn(`  ⚠️ Failed to generate AGENTS.md for ${component.path}: ${error.message}`);
      }
    }
  }

  /**
   * Generate AGENTS.md content for a component
   */
  generateAgentsContent(component) {
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
    
    return `# 🤖 AGENTS.md - ${component.path}

## 🎯 **Mission Scope**
**Layer**: ${component.metadata.layer} | **Type**: ${component.metadata.type}
**Complexity**: ${component.metadata.complexity} | **Files**: ${component.files.length}

---

## 🏗️ **Component Analysis**

### **File Structure**
${component.files.map(f => `- \`${f}\``).join('\n')}

### **Mathematical Content**
${component.metadata.mathematical.hasMathematical ? 
  `**Concepts**: ${component.metadata.mathematical.concepts.join(', ')}
**Theorems**: ${component.metadata.mathematical.theorems.length}
**Formal Systems**: ${component.metadata.mathematical.formalSystems.join(', ')}` : 
  'No mathematical content detected'
}

### **Dependencies**
${component.metadata.dependencies.length > 0 ? 
  component.metadata.dependencies.map(dep => `- \`${dep}\``).join('\n') : 
  'No external dependencies detected'
}

### **Test Coverage**
${component.metadata.tests.length > 0 ? 
  `**Test Files**: ${component.metadata.tests.length}
**Coverage**: ${Math.round((component.metadata.tests.length / component.files.length) * 100)}%` : 
  'No tests found'
}

---

## 📊 **Development Responsibilities**

### **Code Quality**
- [ ] **Maintainability**: Keep complexity ≤ ${component.metadata.complexity + 10}
- [ ] **Documentation**: Update AGENTS.md when structure changes
- [ ] **Testing**: Ensure test coverage ≥ 80%
- [ ] **Dependencies**: Review and update dependencies regularly

### **${layerNames[component.metadata.layer - 1] || 'General'} Layer**
${this.getLayerResponsibilities(component.metadata.layer)}

---

## 🔗 **Integration Points**

### **Input Dependencies**
${component.metadata.dependencies.map(dep => `- \`${dep}\``).join('\n')}

### **Output Interfaces**
${this.identifyOutputInterfaces(component)}

---

## 📈 **Quality Metrics**

| Metric | Current | Target | Status |
|---------|---------|--------|--------|
| **Complexity** | ${component.metadata.complexity} | ${component.metadata.complexity + 10} | ✅ |
| **Test Coverage** | ${Math.round((component.metadata.tests.length / component.files.length) * 100)}% | 80% | ${component.metadata.tests.length / component.files.length >= 0.8 ? '✅' : '⚠️'} |
| **Documentation** | ${component.metadata.documentation.length > 0 ? '✅' : '❌'} | Complete | ${component.metadata.documentation.length > 0 ? '✅' : '❌'} |

---

> **Last Updated**: ${new Date().toISOString().split('T')[0]}  
> **Component ID**: ${component.id}  
> **Layer**: ${component.metadata.layer} - ${layerNames[component.metadata.layer - 1] || 'Unknown'}

---

*This AGENTS.md file was auto-generated by the MIND-GIT Universal Metadata Kernel*
*Update this file to reflect changes in component structure and responsibilities*
`;
  }

  /**
   * Get layer-specific responsibilities
   */
  getLayerResponsibilities(layer) {
    const responsibilities = {
      1: [
        '- [ ] **Mathematical Rigor**: All operations must be mathematically sound',
        '- [ ] **Formal Verification**: Provide proofs for key properties',
        '- [ ] **Theoretical Foundation**: Establish theoretical underpinnings',
        '- [ ] **Abstraction**: Create clean mathematical abstractions'
      ],
      2: [
        '- [ ] **Core Logic**: Implement fundamental algorithms',
        '- [ ] **Performance**: Optimize for speed and memory',
        '- [ ] **Reliability**: Ensure robust error handling',
        '- [ ] **API Design**: Create clean internal interfaces'
      ],
      3: [
        '- [ ] **API Stability**: Maintain backward compatibility',
        '- [ ] **Documentation**: Keep API docs current',
        '- [ ] **Input Validation**: Validate all inputs',
        '- [ ] **Error Handling**: Provide clear error messages'
      ],
      4: [
        '- [ ] **Business Logic**: Implement domain rules correctly',
        '- [ ] **Data Validation**: Ensure data integrity',
        '- [ ] **State Management**: Manage application state',
        '- [ ] **Integration**: Connect with other services'
      ],
      5: [
        '- [ ] **Data Integrity**: Maintain data consistency',
        '- [ ] **Performance**: Optimize queries and operations',
        '- [ ] **Security**: Protect sensitive data',
        '- [ ] **Migration**: Handle data schema changes'
      ],
      6: [
        '- [ ] **User Experience**: Create intuitive interfaces',
        '- [ ] **Responsive Design**: Support multiple screen sizes',
        '- [ ] **Accessibility**: Follow WCAG guidelines',
        '- [ ] **Performance**: Optimize render times'
      ],
      7: [
        '- [ ] **Test Coverage**: Maintain ≥ 80% coverage',
        '- [ ] **Test Quality**: Write meaningful test cases',
        '- [ ] **Automation**: Automate test execution',
        '- [ ] **CI/CD**: Integrate with deployment pipeline'
      ],
      8: [
        '- [ ] **Clarity**: Write clear, understandable documentation',
        '- [ ] **Completeness**: Document all public interfaces',
        '- [ ] **Examples**: Provide working examples',
        '- [ ] **Maintenance**: Keep docs updated with changes'
      ]
    };
    
    return responsibilities[layer] || [
      '- [ ] **Code Quality**: Follow best practices',
      '- [ ] **Testing**: Write comprehensive tests',
      '- [ ] **Documentation**: Keep documentation current',
      '- [ ] **Maintenance**: Regular updates and improvements'
    ];
  }

  /**
   * Identify output interfaces for a component
   */
  identifyOutputInterfaces(component) {
    const interfaces = [];
    
    // Look for exports in source files
    for (const file of component.files) {
      if (file.endsWith('.js') || file.endsWith('.ts')) {
        try {
          const content = fs.readFileSync(path.join(this.repoPath, file), 'utf8');
          
          // Find export statements
          const exports = content.match(/export\s+(?:const|function|class)\s+(\w+)/g);
          if (exports) {
            interfaces.push(...exports.map(exp => exp.replace(/export\s+(?:const|function|class)\s+/, '')));
          }
          
          // Find module.exports
          const moduleExports = content.match(/module\.exports\s*=\s*(\w+)/g);
          if (moduleExports) {
            interfaces.push(...moduleExports.map(exp => exp.replace(/module\.exports\s*=\s*/, '')));
          }
          
        } catch (error) {
          // Skip files we can't read
        }
      }
    }
    
    return interfaces.length > 0 ? interfaces.map(intf => `- \`${intf}\``).join('\n') : 'No explicit exports found';
  }

  /**
   * Create export system
   */
  async createExportSystem(components) {
    const exportSystem = {
      generated: new Date().toISOString(),
      components: components.map(c => ({
        id: c.id,
        path: c.path,
        type: c.metadata.type,
        layer: c.metadata.layer,
        complexity: c.metadata.complexity,
        mathematical: c.metadata.mathematical,
        files: c.files.length,
        tests: c.metadata.tests.length,
        documentation: c.metadata.documentation.length
      }))
    };
    
    const exportPath = path.join(this.metadataDir, 'components', 'registry.jsonl');
    await fsAsync.writeFile(exportPath, JSON.stringify(exportSystem, null, 2));
    
    console.log(`  📊 Created export system with ${components.length} components`);
  }

  /**
   * Generate CanvasL visualization
   */
  async generateCanvasLVisualization(components) {
    const canvas = {
      nodes: components.map((component, index) => ({
        id: `component-${index}`,
        type: 'file',
        x: (component.metadata.layer - 1) * 200,
        y: (index % 5) * 150,
        width: 180,
        height: 100,
        file: component.path,
        text: `${component.path}\n(Layer ${component.metadata.layer})`
      })),
      edges: []
    };
    
    // Add edges based on dependencies
    for (let i = 0; i < components.length; i++) {
      const component = components[i];
      
      for (const dep of component.metadata.dependencies) {
        const targetIndex = components.findIndex(c => 
          c.path === dep || c.files.some(f => f.includes(dep))
        );
        
        if (targetIndex >= 0) {
          canvas.edges.push({
            id: `edge-${i}-${targetIndex}`,
            fromNode: `component-${i}`,
            toNode: `component-${targetIndex}`
          });
        }
      }
    }
    
    const canvasPath = path.join(this.metadataDir, 'repository-structure.canvas');
    await fsAsync.writeFile(canvasPath, JSON.stringify(canvas, null, 2));
    
    console.log(`  🎨 Generated CanvasL visualization with ${components.length} nodes`);
  }
}

// CLI Interface
const kernel = new UniversalMetadataKernel();

const command = process.argv[2];
const target = process.argv[3];

switch (command) {
  case 'analyze':
    if (!target) {
      console.log('Usage: mind-git-kernel analyze <repository-path>');
      process.exit(1);
    }
    
    const targetKernel = new UniversalMetadataKernel(path.resolve(target));
    targetKernel.analyzeRepository()
      .then(result => {
        console.log('\n🎉 Analysis Complete!');
        console.log(`📁 Metadata kernel created at: ${result.kernelPath}`);
        console.log(`📊 Analyzed ${result.components.length} components`);
        console.log(`🔗 Found ${result.relationships.length} relationships`);
      })
      .catch(error => {
        console.error('❌ Analysis failed:', error.message);
        process.exit(1);
      });
    break;
    
  case 'visualize':
    kernel.analyzeRepository()
      .then(result => {
        console.log('\n🎨 CanvasL Visualization:');
        console.log(`Open: ${path.join(result.kernelPath, 'repository-structure.canvas')}`);
        console.log('This file can be opened in Obsidian or any CanvasL-compatible viewer');
      })
      .catch(error => {
        console.error('❌ Visualization failed:', error.message);
        process.exit(1);
      });
    break;
    
  case 'export':
    kernel.analyzeRepository()
      .then(result => {
        console.log('\n📤 Export Options:');
        console.log(`Components: ${result.components.length}`);
        console.log(`Mathematical: ${result.components.filter(c => c.metadata.mathematical.hasMathematical).length}`);
        console.log(`With Tests: ${result.components.filter(c => c.metadata.tests.length > 0).length}`);
        console.log(`With Documentation: ${result.components.filter(c => c.metadata.documentation.length > 0).length}`);
      })
      .catch(error => {
        console.error('❌ Export failed:', error.message);
        process.exit(1);
      });
    break;
    
  default:
    console.log(`
🧠 MIND-GIT Universal Metadata Kernel

A universal system for understanding and organizing any Git repository through metadata and CanvasL visualizations.

🎯 Commands:
  analyze <path>     Analyze a Git repository and generate metadata kernel
  visualize           Generate CanvasL visualization of current repository
  export              Export metadata analysis of current repository

🔍 What it does:
  • Detects repository type and technologies
  • Analyzes mathematical content and formal systems
  • Generates AGENTS.md development contracts
  • Creates CanvasL visualizations of architecture
  • Builds component relationship maps
  • Exports structured metadata for analysis

📁 Output Structure:
  .metadata-kernel/
  ├── components/           # Component metadata registry
  ├── relationships/        # Component relationships
  ├── exports/             # Generated exports
  ├── templates/           # AGENTS.md templates
  └── repository-structure.canvas  # CanvasL visualization

💡 Use Cases:
  • Understand complex codebases quickly
  • Create development contracts for teams
  • Visualize architecture as spatial diagrams
  • Find mathematical content and formal proofs
  • Generate documentation automatically
  • Onboard new developers efficiently

🚀 Examples:
  mind-git-kernel analyze /path/to/any/repo
  mind-git-kernel visualize
  mind-git-kernel export

This transforms ANY Git repository into an understandable, navigable system through the power of metadata and CanvasL visual programming.
    `);
}