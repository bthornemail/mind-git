const fs = require('fs');
const path = require('path');

class CrossProjectAnalyzer {
  constructor() {
    this.projects = [
      { name: 'mind-git', path: '.', type: 'spatial_compiler' },
      { name: 'hyperdev-ide', path: '../hyperdev-ide', type: 'vr_framework' },
      { name: 'h2gnn-enhanced', path: '../hyperbolic-geometric-neural-network', type: 'ai_intelligence' },
      { name: 'computational-scheme-theory', path: '../computational-scheme-theory', type: 'mathematical' },
      { name: 'meta-log', path: '../meta-log', type: 'orchestrator' }
    ];
    
    this.results = {
      ecosystem: {
        totalProjects: this.projects.length,
        projectTypes: {},
        dependencies: [],
        integrationComplexity: 'medium'
      },
      projects: []
    };
  }

  async analyze() {
    console.log('🌐 Analyzing cross-project ecosystem...');
    
    for (const project of this.projects) {
      console.log(`  📁 Analyzing ${project.name}...`);
      const projectAnalysis = await this.analyzeProject(project);
      this.results.projects.push(projectAnalysis);
      
      // Track project types
      if (!this.results.ecosystem.projectTypes[project.type]) {
        this.results.ecosystem.projectTypes[project.type] = 0;
      }
      this.results.ecosystem.projectTypes[project.type]++;
    }
    
    // Analyze dependencies between projects
    await this.analyzeDependencies();
    
    // Calculate integration complexity
    this.results.ecosystem.integrationComplexity = this.calculateComplexity();
    
    return this.results;
  }

  async analyzeProject(project) {
    const result = {
      name: project.name,
      type: project.type,
      exists: fs.existsSync(project.path),
      hasPackageJson: false,
      language: 'unknown',
      dependencies: [],
      entryPoints: []
    };
    
    if (result.exists) {
      // Check for package.json
      const packagePath = path.join(project.path, 'package.json');
      if (fs.existsSync(packagePath)) {
        result.hasPackageJson = true;
        try {
          const pkg = JSON.parse(fs.readFileSync(packagePath, 'utf8'));
          result.language = 'typescript/javascript';
          result.dependencies = Object.keys(pkg.dependencies || {});
          result.entryPoints = [pkg.main || 'index.js'].filter(Boolean);
        } catch (e) {
          console.warn(`  ⚠️ Could not parse package.json for ${project.name}`);
        }
      }
      
      // Check for Docker
      const dockerPath = path.join(project.path, 'Dockerfile');
      result.hasDocker = fs.existsSync(dockerPath);
      
      // Check for README
      const readmePath = path.join(project.path, 'README.md');
      result.hasReadme = fs.existsSync(readmePath);
    }
    
    return result;
  }

  async analyzeDependencies() {
    // Look for cross-project references
    for (const project of this.results.projects) {
      if (project.exists && project.hasPackageJson) {
        const otherProjects = this.results.projects.filter(p => p.name !== project.name);
        
        for (const otherProject of otherProjects) {
          // Check if this project references the other in dependencies
          const references = project.dependencies.some(dep => 
            dep.includes(otherProject.name.toLowerCase().replace(/-/g, ''))
          );
          
          if (references) {
            this.results.ecosystem.dependencies.push({
              from: project.name,
              to: otherProject.name,
              type: 'package_dependency'
            });
          }
        }
      }
    }
  }

  calculateComplexity() {
    const existingProjects = this.results.projects.filter(p => p.exists).length;
    const totalProjects = this.results.projects.length;
    const coverage = existingProjects / totalProjects;
    
    if (coverage < 0.5) return 'high';
    if (coverage < 0.8) return 'medium';
    return 'low';
  }
}

// Run analysis
const analyzer = new CrossProjectAnalyzer();
analyzer.analyze().then(results => {
  console.log('✅ Cross-project analysis complete!');
  
  console.log('\n📊 Ecosystem Summary:');
  console.log(`- Total projects identified: ${results.ecosystem.totalProjects}`);
  console.log(`- Projects found: ${results.projects.filter(p => p.exists).length}`);
  console.log(`- Integration complexity: ${results.ecosystem.integrationComplexity}`);
  
  console.log('\n🏗️ Project Types:');
  Object.entries(results.ecosystem.projectTypes).forEach(([type, count]) => {
    console.log(`  - ${type}: ${count} project(s)`);
  });
  
  console.log('\n🔗 Dependencies Found:');
  results.ecosystem.dependencies.forEach(dep => {
    console.log(`  - ${dep.from} → ${dep.to}`);
  });
  
  console.log('\n🎯 Integration Priority:');
  console.log('  1. Connect projects that already have dependencies');
  console.log('  2. Focus on TypeScript projects first (easier integration)');
  console.log('  3. Use Docker for isolated services');
  
  // Save results
  fs.writeFileSync(
    './ecosystem-analysis/cross-project-analysis.json',
    JSON.stringify(results, null, 2)
  );
  
  console.log('\n📄 Results saved to ecosystem-analysis/cross-project-analysis.json');
}).catch(error => {
  console.error('❌ Cross-project analysis failed:', error);
});