#!/usr/bin/env node

/**
 * MIND-GIT Demo Runner
 * 
 * Simple script to test and run individual demos
 */

import fs from 'fs/promises';
import path from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

class DemoRunner {
  constructor() {
    this.demosDir = path.join(__dirname, 'demos');
    this.availableDemos = [];
  }

  async initialize() {
    console.log('🚀 Initializing MIND-GIT Demo Runner...');
    
    // Load demo index
    const indexPath = path.join(this.demosDir, 'index.json');
    try {
      const indexData = await fs.readFile(indexPath, 'utf8');
      const index = JSON.parse(indexData);
      this.availableDemos = index.demos;
      console.log(`✅ Loaded ${this.availableDemos.length} demos`);
    } catch (error) {
      console.error('❌ Failed to load demo index:', error.message);
    }
  }

  listDemos() {
    console.log('\n📋 Available Demos:');
    console.log('=' .repeat(60));
    
    this.availableDemos.forEach((demo, index) => {
      console.log(`${index + 1}. ${demo.title}`);
      console.log(`   📁 Category: ${demo.category}`);
      console.log(`   👥 Audience: ${demo.audience}`);
      console.log(`   ⏱️  Time: ${demo.estimatedTime}`);
      console.log(`   📂 Files: ${demo.files.length}`);
      console.log('');
    });
  }

  async runDemo(demoId) {
    const demo = this.availableDemos.find(d => d.id === demoId);
    
    if (!demo) {
      console.error(`❌ Demo not found: ${demoId}`);
      return;
    }

    console.log(`\n🎯 Running Demo: ${demo.title}`);
    console.log('=' .repeat(60));
    
    // Try to find and run the main demo file
    const htmlFile = demo.files.find(f => f.endsWith('.html'));
    const canvasFile = demo.files.find(f => f.endsWith('.canvas'));
    
    if (htmlFile) {
      console.log(`🌐 Opening interactive demo: ${htmlFile}`);
      const fullPath = path.join(this.demosDir, htmlFile);
      console.log(`📂 File path: ${fullPath}`);
      console.log(`\n💡 To run: open ${fullPath} in your browser`);
    }
    
    if (canvasFile) {
      console.log(`📐 Canvas file: ${canvasFile}`);
      const fullPath = path.join(this.demosDir, canvasFile);
      console.log(`📂 File path: ${fullPath}`);
      console.log(`\n💡 To compile: mind-git compile "${fullPath}"`);
    }

    // Show demo details
    console.log(`\n📋 Demo Details:`);
    console.log(`   📝 Description: ${demo.description}`);
    console.log(`   🔧 Functions: ${demo.functions.join(', ')}`);
    console.log(`   📊 Difficulty: ${demo.difficulty}`);
    console.log(`   🎯 Audience: ${demo.audience}`);
  }

  async testCanvas(canvasPath) {
    console.log(`\n🧪 Testing Canvas: ${canvasPath}`);
    
    try {
      const canvasData = await fs.readFile(canvasPath, 'utf8');
      const canvas = JSON.parse(canvasData);
      
      console.log('✅ Canvas JSON is valid');
      console.log(`📊 Nodes: ${canvas.nodes?.length || 0}`);
      console.log(`🔗 Edges: ${canvas.edges?.length || 0}`);
      
      // Validate canvas structure
      if (canvas.nodes && Array.isArray(canvas.nodes)) {
        canvas.nodes.forEach((node, index) => {
          if (!node.id) console.warn(`⚠️  Node ${index} missing ID`);
          if (!node.type) console.warn(`⚠️  Node ${node.id} missing type`);
          if (node.x === undefined || node.y === undefined) {
            console.warn(`⚠️  Node ${node.id} missing coordinates`);
          }
        });
      }
      
      if (canvas.edges && Array.isArray(canvas.edges)) {
        canvas.edges.forEach((edge, index) => {
          if (!edge.id) console.warn(`⚠️  Edge ${index} missing ID`);
          if (!edge.fromNode || !edge.toNode) {
            console.warn(`⚠️  Edge ${index} missing connections`);
          }
        });
      }
      
      console.log('✅ Canvas validation complete');
      
    } catch (error) {
      console.error('❌ Canvas validation failed:', error.message);
    }
  }

  async showDemoInfo(demoId) {
    const demo = this.availableDemos.find(d => d.id === demoId);
    
    if (!demo) {
      console.error(`❌ Demo not found: ${demoId}`);
      return;
    }

    console.log(`\n📋 Demo Information: ${demo.title}`);
    console.log('=' .repeat(60));
    console.log(`📝 Description: ${demo.description}`);
    console.log(`📁 Category: ${demo.category}`);
    console.log(`👥 Audience: ${demo.audience}`);
    console.log(`🎨 Format: ${demo.form}`);
    console.log(`🔧 Functions: ${demo.functions.join(', ')}`);
    console.log(`📊 Difficulty: ${demo.difficulty}`);
    console.log(`⏱️  Estimated Time: ${demo.estimatedTime}`);
    
    if (demo.prerequisites && demo.prerequisites.length > 0) {
      console.log(`\n📚 Prerequisites:`);
      demo.prerequisites.forEach(prereq => console.log(`   • ${prereq}`));
    }
    
    if (demo.learningObjectives && demo.learningObjectives.length > 0) {
      console.log(`\n🎯 Learning Objectives:`);
      demo.learningObjectives.forEach(obj => console.log(`   • ${obj}`));
    }
    
    console.log(`\n📂 Generated Files:`);
    demo.files.forEach(file => {
      const icon = file.endsWith('.html') ? '🌐' : 
                   file.endsWith('.canvas') ? '📐' :
                   file.endsWith('.ipynb') ? '📓' :
                   file.endsWith('.md') ? '📄' : '📁';
      console.log(`   ${icon} ${file}`);
    });
  }
}

// CLI interface
async function main() {
  const args = process.argv.slice(2);
  const runner = new DemoRunner();
  
  await runner.initialize();
  
  if (args.length === 0) {
    runner.listDemos();
    console.log('\n💡 Usage:');
    console.log('  node demo-runner.js list                    # List all demos');
    console.log('  node demo-runner.js run <demo-id>           # Run specific demo');
    console.log('  node demo-runner.js info <demo-id>          # Show demo info');
    console.log('  node demo-runner.js test <canvas-file>       # Test canvas file');
    console.log('\n🎯 Example:');
    console.log('  node demo-runner.js run intro-meaning-repos');
    return;
  }
  
  const command = args[0];
  const target = args[1];
  
  switch (command) {
    case 'list':
      runner.listDemos();
      break;
      
    case 'run':
      if (!target) {
        console.error('❌ Please specify a demo ID');
        process.exit(1);
      }
      await runner.runDemo(target);
      break;
      
    case 'info':
      if (!target) {
        console.error('❌ Please specify a demo ID');
        process.exit(1);
      }
      await runner.showDemoInfo(target);
      break;
      
    case 'test':
      if (!target) {
        console.error('❌ Please specify a canvas file');
        process.exit(1);
      }
      await runner.testCanvas(target);
      break;
      
    default:
      console.error(`❌ Unknown command: ${command}`);
      process.exit(1);
  }
}

// Run if called directly
if (import.meta.url === `file://${process.argv[1]}`) {
  main().catch(console.error);
}

export default DemoRunner;