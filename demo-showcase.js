#!/usr/bin/env node

/**
 * MIND-GIT Demo Showcase
 * 
 * Creates a comprehensive showcase of all demos with sample outputs
 */

import fs from 'fs/promises';
import path from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

class DemoShowcase {
  constructor() {
    this.demosDir = path.join(__dirname, 'demos');
    this.showcaseDir = path.join(__dirname, 'demo-showcase');
  }

  async initialize() {
    console.log('🎨 Creating MIND-GIT Demo Showcase...');
    
    // Create showcase directory
    try {
      await fs.mkdir(this.showcaseDir, { recursive: true });
    } catch (error) {
      // Directory already exists
    }
    
    // Load demo index
    const indexPath = path.join(this.demosDir, 'index.json');
    const indexData = await fs.readFile(indexPath, 'utf8');
    this.demos = JSON.parse(indexData).demos;
    
    console.log(`✅ Loaded ${this.demos.length} demos for showcase`);
  }

  async generateShowcase() {
    // Generate main showcase page
    await this.generateMainShowcase();
    
    // Generate individual demo showcases
    for (const demo of this.demos) {
      await this.generateDemoShowcase(demo);
    }
    
    // Generate assets
    await this.generateAssets();
    
    console.log('🎉 Demo showcase generated successfully!');
    console.log(`📂 Location: ${this.showcaseDir}/index.html`);
  }

  async generateMainShowcase() {
    const html = `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>MIND-GIT Demo Showcase</title>
    <script src="https://cdn.tailwindcss.com"></script>
    <link href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.0.0/css/all.min.css" rel="stylesheet">
    <style>
        .demo-card {
            transition: all 0.3s ease;
            border-left: 4px solid transparent;
        }
        .demo-card:hover {
            transform: translateY(-4px);
            box-shadow: 0 20px 25px -5px rgba(0, 0, 0, 0.1), 0 10px 10px -5px rgba(0, 0, 0, 0.04);
        }
        .demo-card.basic { border-left-color: #3B82F6; }
        .demo-card.verification-focused { border-left-color: #10B981; }
        .demo-card.visual { border-left-color: #8B5CF6; }
        .demo-card.distributed { border-left-color: #F59E0B; }
        .demo-card.applied { border-left-color: #EF4444; }
        .demo-card.advanced-mathematical { border-left-color: #6366F1; }
        
        .difficulty-beginner { background: #DBEAFE; color: #1E40AF; }
        .difficulty-intermediate { background: #FEF3C7; color: #92400E; }
        .difficulty-advanced { background: #FEE2E2; color: #991B1B; }
        .difficulty-expert { background: #F3E8FF; color: #5B21B6; }
        
        .hero-gradient {
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
        }
        
        .math-pattern {
            background-image: url("data:image/svg+xml,%3Csvg width='60' height='60' viewBox='0 0 60 60' xmlns='http://www.w3.org/2000/svg'%3E%3Cg fill='none' fill-rule='evenodd'%3E%3Cg fill='%239C92AC' fill-opacity='0.05'%3E%3Cpath d='M36 34v-4h-2v4h-4v2h4v4h2v-4h4v-2h-4zm0-30V0h-2v4h-4v2h4v4h2V6h4V4h-4zM6 34v-4H4v4H0v2h4v4h2v-4h4v-2H6zM6 4V0H4v4H0v2h4v4h2V6h4V4H6z'/%3E%3C/g%3E%3C/g%3E%3C/svg%3E");
        }
    </style>
</head>
<body class="bg-gray-50 math-pattern">
    <!-- Hero Section -->
    <section class="hero-gradient text-white py-20">
        <div class="container mx-auto px-4">
            <div class="text-center">
                <h1 class="text-5xl font-bold mb-4">MIND-GIT Demo Showcase</h1>
                <p class="text-xl mb-8 text-purple-100">Mathematical Foundation for Self-Evolving Computational Systems</p>
                <div class="flex justify-center space-x-4">
                    <div class="bg-white/20 backdrop-blur-sm rounded-lg px-6 py-3">
                        <i class="fas fa-calculator mr-2"></i>
                        <span>6 Complete Demos</span>
                    </div>
                    <div class="bg-white/20 backdrop-blur-sm rounded-lg px-6 py-3">
                        <i class="fas fa-users mr-2"></i>
                        <span>6 Target Audiences</span>
                    </div>
                    <div class="bg-white/20 backdrop-blur-sm rounded-lg px-6 py-3">
                        <i class="fas fa-code mr-2"></i>
                        <span>Multiple Formats</span>
                    </div>
                </div>
            </div>
        </div>
    </section>

    <!-- Stats Section -->
    <section class="py-12 bg-white">
        <div class="container mx-auto px-4">
            <div class="grid grid-cols-2 md:grid-cols-4 gap-6 text-center">
                <div class="bg-blue-50 rounded-lg p-6">
                    <div class="text-3xl font-bold text-blue-600 mb-2">${this.demos.length}</div>
                    <div class="text-gray-600">Total Demos</div>
                </div>
                <div class="bg-green-50 rounded-lg p-6">
                    <div class="text-3xl font-bold text-green-600 mb-2">${new Set(this.demos.map(d => d.category)).size}</div>
                    <div class="text-gray-600">Categories</div>
                </div>
                <div class="bg-purple-50 rounded-lg p-6">
                    <div class="text-3xl font-bold text-purple-600 mb-2">${new Set(this.demos.map(d => d.audience)).size}</div>
                    <div class="text-gray-600">Audiences</div>
                </div>
                <div class="bg-orange-50 rounded-lg p-6">
                    <div class="text-3xl font-bold text-orange-600 mb-2">${new Set(this.demos.map(d => d.form)).size}</div>
                    <div class="text-gray-600">Formats</div>
                </div>
            </div>
        </div>
    </section>

    <!-- Demos Grid -->
    <section class="py-16">
        <div class="container mx-auto px-4">
            <h2 class="text-3xl font-bold text-center mb-12 text-gray-900">Featured Demos</h2>
            
            <div class="grid md:grid-cols-2 lg:grid-cols-3 gap-8">
                ${this.demos.map(demo => this.generateDemoCard(demo)).join('')}
            </div>
        </div>
    </section>

    <!-- Features Section -->
    <section class="py-16 bg-gray-100">
        <div class="container mx-auto px-4">
            <h2 class="text-3xl font-bold text-center mb-12 text-gray-900">Key Features</h2>
            
            <div class="grid md:grid-cols-2 lg:grid-cols-3 gap-8">
                <div class="bg-white rounded-lg p-6 text-center">
                    <div class="text-4xl text-blue-600 mb-4">
                        <i class="fas fa-shapes"></i>
                    </div>
                    <h3 class="text-xl font-semibold mb-2">Visual Programming</h3>
                    <p class="text-gray-600">CanvasL spatial diagrams compile to executable code with mathematical verification</p>
                </div>
                
                <div class="bg-white rounded-lg p-6 text-center">
                    <div class="text-4xl text-green-600 mb-4">
                        <i class="fas fa-certificate"></i>
                    </div>
                    <h3 class="text-xl font-semibold mb-2">Formal Verification</h3>
                    <p class="text-gray-600">Coq proofs guarantee mathematical correctness of all operations</p>
                </div>
                
                <div class="bg-white rounded-lg p-6 text-center">
                    <div class="text-4xl text-purple-600 mb-4">
                        <i class="fas fa-network-wired"></i>
                    </div>
                    <h3 class="text-xl font-semibold mb-2">P2P Collaboration</h3>
                    <p class="text-gray-600">Real-time synchronization across distributed knowledge networks</p>
                </div>
                
                <div class="bg-white rounded-lg p-6 text-center">
                    <div class="text-4xl text-orange-600 mb-4">
                        <i class="fas fa-square-root-alt"></i>
                    </div>
                    <h3 class="text-xl font-semibold mb-2">Mathematical Foundation</h3>
                    <p class="text-gray-600">Built on 1,400 years of mathematical development</p>
                </div>
                
                <div class="bg-white rounded-lg p-6 text-center">
                    <div class="text-4xl text-red-600 mb-4">
                        <i class="fas fa-robot"></i>
                    </div>
                    <h3 class="text-xl font-semibold mb-2">AI Safety</h3>
                    <p class="text-gray-600">Proof-guaranteed evolution of autonomous systems</p>
                </div>
                
                <div class="bg-white rounded-lg p-6 text-center">
                    <div class="text-4xl text-indigo-600 mb-4">
                        <i class="fas fa-atom"></i>
                    </div>
                    <h3 class="text-xl font-semibold mb-2">Quantum-Inspired</h3>
                    <p class="text-gray-600">Hopf fibrations and octonion algebra for advanced applications</p>
                </div>
            </div>
        </div>
    </section>

    <!-- Getting Started -->
    <section class="py-16 bg-white">
        <div class="container mx-auto px-4">
            <h2 class="text-3xl font-bold text-center mb-12 text-gray-900">Getting Started</h2>
            
            <div class="grid md:grid-cols-2 gap-8">
                <div class="bg-gray-50 rounded-lg p-6">
                    <h3 class="text-xl font-semibold mb-4 text-gray-900">
                        <i class="fas fa-terminal mr-2 text-blue-600"></i>
                        Command Line
                    </h3>
                    <div class="bg-gray-900 text-green-400 p-4 rounded-lg font-mono text-sm">
                        <div># Install MIND-GIT</div>
                        <div>npm install -g mind-git</div>
                        <div class="mt-2"># Run a demo</div>
                        <div>mind-git compile demo.canvas</div>
                    </div>
                </div>
                
                <div class="bg-gray-50 rounded-lg p-6">
                    <h3 class="text-xl font-semibold mb-4 text-gray-900">
                        <i class="fas fa-globe mr-2 text-purple-600"></i>
                        Interactive Web
                    </h3>
                    <p class="text-gray-600 mb-4">
                        Try our interactive demos directly in your browser. No installation required.
                    </p>
                    <div class="flex space-x-4">
                        <a href="demos/web/intro-meaning-repos.html" class="bg-blue-600 text-white px-4 py-2 rounded-lg hover:bg-blue-700 transition">
                            Try Basic Demo
                        </a>
                        <a href="demos/notebooks/verified-computations.ipynb" class="bg-purple-600 text-white px-4 py-2 rounded-lg hover:bg-purple-700 transition">
                            View Notebook
                        </a>
                    </div>
                </div>
            </div>
        </div>
    </section>

    <!-- Footer -->
    <footer class="bg-gray-800 text-white py-12">
        <div class="container mx-auto px-4 text-center">
            <p class="mb-4">© 2025 MIND-GIT - Mathematical Foundation for Self-Evolving Computational Systems</p>
            <div class="flex justify-center space-x-6">
                <a href="https://github.com/bthornemail/mind-git" class="hover:text-blue-400 transition">
                    <i class="fab fa-github text-xl"></i>
                </a>
                <a href="https://www.npmjs.com/package/mind-git" class="hover:text-blue-400 transition">
                    <i class="fab fa-npm text-xl"></i>
                </a>
                <a href="https://bthornemail.github.io/mind-git/" class="hover:text-blue-400 transition">
                    <i class="fas fa-book text-xl"></i>
                </a>
            </div>
        </div>
    </footer>
</body>
</html>`;

    await fs.writeFile(path.join(this.showcaseDir, 'index.html'), html);
  }

  generateDemoCard(demo) {
    const difficultyClass = `difficulty-${demo.difficulty}`;
    const categoryClass = demo.category;
    
    return `
        <div class="demo-card ${categoryClass} bg-white rounded-lg shadow-lg p-6 hover:shadow-xl">
            <div class="flex justify-between items-start mb-4">
                <h3 class="text-xl font-semibold text-gray-900">${demo.title}</h3>
                <span class="px-3 py-1 ${difficultyClass} rounded-full text-sm font-medium">
                    ${demo.difficulty}
                </span>
            </div>
            
            <p class="text-gray-600 mb-4">${demo.description}</p>
            
            <div class="flex flex-wrap gap-2 mb-4">
                <span class="px-2 py-1 bg-gray-100 text-gray-700 rounded text-xs">
                    <i class="fas fa-folder mr-1"></i>${demo.category}
                </span>
                <span class="px-2 py-1 bg-gray-100 text-gray-700 rounded text-xs">
                    <i class="fas fa-users mr-1"></i>${demo.audience}
                </span>
                <span class="px-2 py-1 bg-gray-100 text-gray-700 rounded text-xs">
                    <i class="fas fa-clock mr-1"></i>${demo.estimatedTime}
                </span>
            </div>
            
            <div class="flex justify-between items-center">
                <div class="text-sm text-gray-500">
                    <i class="fas fa-tools mr-1"></i>
                    ${demo.functions.join(', ')}
                </div>
                <a href="demos/web/${demo.id}.html" class="bg-blue-600 text-white px-3 py-1 rounded hover:bg-blue-700 transition text-sm">
                    Try Demo
                </a>
            </div>
        </div>
    `;
  }

  async generateDemoShowcase(demo) {
    // Create individual demo showcase pages
    const demoDir = path.join(this.showcaseDir, 'demos', demo.id);
    try {
      await fs.mkdir(demoDir, { recursive: true });
    } catch (error) {
      // Directory already exists
    }

    // Copy demo files
    for (const file of demo.files) {
      const sourcePath = path.join(this.demosDir, file);
      const destPath = path.join(demoDir, path.basename(file));
      
      try {
        const content = await fs.readFile(sourcePath);
        await fs.writeFile(destPath, content);
      } catch (error) {
        console.warn(`Warning: Could not copy ${sourcePath} to ${destPath}`);
      }
    }
  }

  async generateAssets() {
    // Copy demo assets
    const assetsDir = path.join(this.showcaseDir, 'demos');
    try {
      await fs.mkdir(assetsDir, { recursive: true });
    } catch (error) {
      // Directory already exists
    }

    // Copy demo directories
    const dirsToCopy = ['web', 'notebooks', 'docs', 'basic', 'visual', 'verification-focused', 'distributed', 'applied', 'advanced-mathematical'];
    
    for (const dir of dirsToCopy) {
      const sourceDir = path.join(this.demosDir, dir);
      const destDir = path.join(assetsDir, dir);
      
      try {
        await this.copyDirectory(sourceDir, destDir);
      } catch (error) {
        console.warn(`Warning: Could not copy directory ${dir}`);
      }
    }
  }

  async copyDirectory(source, dest) {
    try {
      await fs.mkdir(dest, { recursive: true });
      const entries = await fs.readdir(source, { withFileTypes: true });
      
      for (const entry of entries) {
        const sourcePath = path.join(source, entry.name);
        const destPath = path.join(dest, entry.name);
        
        if (entry.isDirectory()) {
          await this.copyDirectory(sourcePath, destPath);
        } else {
          const content = await fs.readFile(sourcePath);
          await fs.writeFile(destPath, content);
        }
      }
    } catch (error) {
      // Directory might not exist, which is fine
    }
  }
}

// Run if called directly
if (import.meta.url === `file://${process.argv[1]}`) {
  const showcase = new DemoShowcase();
  showcase.initialize().then(() => {
    return showcase.generateShowcase();
  }).then(() => {
    console.log('\\n🌐 Demo showcase ready!');
    console.log('💡 Open the showcase in your browser to explore all demos');
  }).catch(console.error);
}

export default DemoShowcase;