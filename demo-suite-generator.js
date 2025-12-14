#!/usr/bin/env node

/**
 * MIND-GIT Demo Suite Generator
 * 
 * Comprehensive demo generation system for MIND-GIT capabilities
 * including CanvasL visual programming, AAL verification, and P2P federation.
 */

import fs from 'fs/promises';
import path from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

// Demo configuration schema
const DEMO_CATEGORIES = {
  BASIC: 'basic',
  VERIFICATION: 'verification', 
  VISUAL: 'visual',
  DISTRIBUTED: 'distributed',
  APPLIED: 'applied',
  ADVANCED: 'advanced'
};

const TARGET_AUDIENCES = {
  DEVELOPERS: 'developers',
  RESEARCHERS: 'researchers', 
  ENTERPRISES: 'enterprises',
  AI_ML: 'ai-ml',
  GENERAL: 'general',
  POWER_USERS: 'power-users'
};

const DEMO_FORMS = {
  INTERACTIVE_TUTORIAL: 'interactive-tutorial',
  VIDEO_WALKTHROUGH: 'video-walkthrough',
  CODE_NOTEBOOK: 'code-notebook',
  LIVE_WEBINAR: 'live-webinar',
  STATIC_DOCS: 'static-docs',
  VR_AR: 'vr-ar'
};

const DEMO_FUNCTIONS = {
  NODE_CREATION: 'node-creation',
  FORMAL_PROOF: 'formal-proof',
  VISUAL_COMPILATION: 'visual-compilation',
  MATH_OPERATIONS: 'math-operations',
  FEDERATION_SYNC: 'federation-sync',
  SELF_EVOLUTION: 'self-evolution',
  INTEGRATION: 'integration'
};

class DemoSuiteGenerator {
  constructor() {
    this.outputDir = path.join(__dirname, '..', 'demos');
    this.templates = new Map();
    this.demos = [];
  }

  async initialize() {
    console.log('🚀 Initializing MIND-GIT Demo Suite Generator...');
    
    // Create output directories
    await this.createDirectories();
    
    // Load templates
    await this.loadTemplates();
    
    console.log('✅ Demo Suite Generator initialized');
  }

  async createDirectories() {
    const dirs = [
      'demos',
      'demos/basic',
      'demos/verification', 
      'demos/visual',
      'demos/distributed',
      'demos/applied',
      'demos/advanced',
      'demos/web',
      'demos/notebooks',
      'demos/videos',
      'demos/docs',
      'demos/vr-ar'
    ];

    for (const dir of dirs) {
      const fullPath = path.join(__dirname, '..', dir);
      try {
        await fs.mkdir(fullPath, { recursive: true });
      } catch (error) {
        // Directory already exists
      }
    }
  }

  async loadTemplates() {
    // HTML template for interactive tutorials
    this.templates.set('interactive-tutorial', `
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>{{TITLE}} - MIND-GIT Demo</title>
    <script src="https://cdn.tailwindcss.com"></script>
    <script type="module">
        import { CanvasLCompiler } from 'https://cdn.jsdelivr.net/npm/mind-git@1.1.0/dist/index.js';
        
        window.CanvasLCompiler = CanvasLCompiler;
        window.runDemo = async function(canvasData) {
            const compiler = new CanvasLCompiler();
            try {
                const result = await compiler.compileCanvas(canvasData);
                eval(result.generated_code.javascript_code);
                return { success: true, result };
            } catch (error) {
                return { success: false, error: error.message };
            }
        };
    </script>
</head>
<body class="bg-gray-50 min-h-screen">
    <div class="container mx-auto px-4 py-8">
        <header class="mb-8">
            <h1 class="text-4xl font-bold text-gray-900 mb-2">{{TITLE}}</h1>
            <p class="text-xl text-gray-600">{{DESCRIPTION}}</p>
            <div class="mt-4 flex gap-2">
                <span class="px-3 py-1 bg-blue-100 text-blue-800 rounded-full text-sm">{{CATEGORY}}</span>
                <span class="px-3 py-1 bg-green-100 text-green-800 rounded-full text-sm">{{AUDIENCE}}</span>
                <span class="px-3 py-1 bg-purple-100 text-purple-800 rounded-full text-sm">{{FUNCTIONS}}</span>
            </div>
        </header>

        <main>
            <div class="grid lg:grid-cols-2 gap-8">
                <div class="bg-white rounded-lg shadow-lg p-6">
                    <h2 class="text-2xl font-semibold mb-4">Canvas Editor</h2>
                    <div id="canvas-editor" class="border-2 border-dashed border-gray-300 rounded-lg p-4 min-h-[400px]">
                        {{CANVAS_CONTENT}}
                    </div>
                    <button onclick="runDemoFromEditor()" class="mt-4 bg-blue-600 text-white px-6 py-2 rounded-lg hover:bg-blue-700 transition">
                        Run Demo
                    </button>
                </div>

                <div class="bg-white rounded-lg shadow-lg p-6">
                    <h2 class="text-2xl font-semibold mb-4">Output & Verification</h2>
                    <div id="output" class="bg-gray-900 text-green-400 p-4 rounded-lg font-mono text-sm min-h-[400px] overflow-auto">
                        Ready to execute...
                    </div>
                    <div id="verification" class="mt-4 p-4 bg-yellow-50 rounded-lg">
                        <h3 class="font-semibold text-yellow-800">Mathematical Verification</h3>
                        <div id="verification-details" class="text-sm text-yellow-700 mt-2">
                            Awaiting execution...
                        </div>
                    </div>
                </div>
            </div>

            <div class="mt-8 bg-white rounded-lg shadow-lg p-6">
                <h2 class="text-2xl font-semibold mb-4">Step-by-Step Guide</h2>
                <div class="space-y-4">
                    {{STEP_BY_STEP}}
                </div>
            </div>
        </main>
    </div>

    <script>
        {{DEMO_SCRIPT}}
    </script>
</body>
</html>`);

    // Jupyter notebook template
    this.templates.set('code-notebook', {
      cells: [
        {
          cell_type: 'markdown',
          metadata: {},
          source: [
            `# {{TITLE}}\n\n`,
            `**Category:** {{CATEGORY}}\n`,
            `**Audience:** {{AUDIENCE}}\n`,
            `**Functions:** {{FUNCTIONS}}\n\n`,
            `{{DESCRIPTION}}\n\n`,
            `## Mathematical Foundation\n\n`,
            `{{MATH_FOUNDATION}}`
          ]
        },
        {
          cell_type: 'code',
          execution_count: null,
          metadata: {},
          outputs: [],
          source: [
            '# Install MIND-GIT if needed\n',
            '!npm install -g mind-git\n\n',
            '# Import required modules\n',
            'import json\n',
            'import subprocess\n',
            'import sys\n',
            'from pathlib import Path\n\n',
            'print("✅ MIND-GIT environment ready")'
          ]
        },
        {
          cell_type: 'markdown',
          metadata: {},
          source: [
            '## Demo Implementation\n\n',
            '{{IMPLEMENTATION_GUIDE}}'
          ]
        },
        {
          cell_type: 'code',
          execution_count: null,
          metadata: {},
          outputs: [],
          source: [
            '{{DEMO_CODE}}'
          ]
        },
        {
          cell_type: 'markdown',
          metadata: {},
          source: [
            '## Results & Analysis\n\n',
            '{{RESULTS_ANALYSIS}}'
          ]
        }
      ],
      metadata: {
        kernelspec: {
          display_name: 'Python 3',
          language: 'python',
          name: 'python3'
        },
        language_info: {
          name: 'python',
          version: '3.8+'
        }
      },
      nbformat: 4,
      nbformat_minor: 4
    });
  }

  createDemo(config) {
    const demo = {
      id: config.id || this.generateId(),
      title: config.title,
      description: config.description,
      category: config.category,
      audience: config.audience,
      form: config.form,
      functions: config.functions || [],
      difficulty: config.difficulty || 'intermediate',
      estimatedTime: config.estimatedTime || '15 minutes',
      prerequisites: config.prerequisites || [],
      learningObjectives: config.learningObjectives || [],
      canvasData: config.canvasData || null,
      code: config.code || '',
      steps: config.steps || [],
      verification: config.verification || {},
      created: new Date().toISOString()
    };

    this.demos.push(demo);
    return demo;
  }

  generateId() {
    return `demo-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;
  }

  async generateInteractiveTutorial(demo) {
    const template = this.templates.get('interactive-tutorial');
    
    const stepByStep = demo.steps.map((step, index) => `
      <div class="flex items-start space-x-3">
        <div class="flex-shrink-0 w-8 h-8 bg-blue-600 text-white rounded-full flex items-center justify-center font-semibold">
          ${index + 1}
        </div>
        <div class="flex-1">
          <h3 class="font-semibold text-gray-900">${step.title}</h3>
          <p class="text-gray-600 mt-1">${step.description}</p>
          ${step.code ? `<pre class="bg-gray-100 p-3 rounded mt-2 text-sm overflow-x-auto"><code>${step.code}</code></pre>` : ''}
        </div>
      </div>
    `).join('');

    const html = template
      .replace(/{{TITLE}}/g, demo.title)
      .replace(/{{DESCRIPTION}}/g, demo.description)
      .replace(/{{CATEGORY}}/g, demo.category)
      .replace(/{{AUDIENCE}}/g, demo.audience)
      .replace(/{{FUNCTIONS}}/g, demo.functions.join(', '))
      .replace(/{{CANVAS_CONTENT}}/g, demo.canvasData ? JSON.stringify(demo.canvasData, null, 2) : '<p>Canvas data will be loaded here...</p>')
      .replace(/{{STEP_BY_STEP}}/g, stepByStep)
      .replace(/{{DEMO_SCRIPT}}/g, demo.code || '');

    const filename = `${demo.id}.html`;
    const filepath = path.join(this.outputDir, 'web', filename);
    
    await fs.writeFile(filepath, html);
    return filepath;
  }

  async generateCodeNotebook(demo) {
    const template = JSON.parse(JSON.stringify(this.templates.get('code-notebook')));
    
    // Replace placeholders in notebook cells
    template.cells.forEach(cell => {
      if (cell.cell_type === 'markdown') {
        cell.source = cell.source.map(line => 
          line
            .replace(/{{TITLE}}/g, demo.title)
            .replace(/{{CATEGORY}}/g, demo.category)
            .replace(/{{AUDIENCE}}/g, demo.audience)
            .replace(/{{FUNCTIONS}}/g, demo.functions.join(', '))
            .replace(/{{DESCRIPTION}}/g, demo.description)
            .replace(/{{MATH_FOUNDATION}}/g, demo.verification.mathFoundation || '')
            .replace(/{{IMPLEMENTATION_GUIDE}}/g, demo.steps.map(s => `### ${s.title}\n\n${s.description}`).join('\n\n'))
            .replace(/{{RESULTS_ANALYSIS}}/g, demo.verification.analysis || '')
        );
      } else if (cell.cell_type === 'code' && cell.source.includes('{{DEMO_CODE}}')) {
        cell.source = demo.code.split('\n');
      }
    });

    const filename = `${demo.id}.ipynb`;
    const filepath = path.join(this.outputDir, 'notebooks', filename);
    
    await fs.writeFile(filepath, JSON.stringify(template, null, 2));
    return filepath;
  }

  async generateStaticDocs(demo) {
    const markdown = `# ${demo.title}

${demo.description}

## Demo Information

- **Category:** ${demo.category}
- **Audience:** ${demo.audience}
- **Functions:** ${demo.functions.join(', ')}
- **Difficulty:** ${demo.difficulty}
- **Estimated Time:** ${demo.estimatedTime}

## Prerequisites

${demo.prerequisites.map(prereq => `- ${prereq}`).join('\n')}

## Learning Objectives

${demo.learningObjectives.map(obj => `- ${obj}`).join('\n')}

## Step-by-Step Guide

${demo.steps.map((step, index) => `
### Step ${index + 1}: ${step.title}

${step.description}

${step.code ? `\`\`\`javascript\n${step.code}\n\`\`\`` : ''}
`).join('\n')}

## Canvas Data

\`\`\`json
${JSON.stringify(demo.canvasData, null, 2)}
\`\`\`

## Verification Results

${demo.verification.mathFoundation || 'Mathematical verification details...'}

## Running the Demo

\`\`\`bash
# Install MIND-GIT
npm install -g mind-git

# Compile the canvas
mind-git compile ${demo.id}.canvas

# Run the generated code
node ${demo.id}.js
\`\`\`

## Expected Output

${demo.verification.expectedOutput || 'Output will be shown here...'}

---

*Generated by MIND-GIT Demo Suite Generator*
`;

    const filename = `${demo.id}.md`;
    const filepath = path.join(this.outputDir, 'docs', filename);
    
    await fs.writeFile(filepath, markdown);
    return filepath;
  }

  async generateDemo(demo) {
    const generatedFiles = [];

    switch (demo.form) {
      case DEMO_FORMS.INTERACTIVE_TUTORIAL:
        generatedFiles.push(await this.generateInteractiveTutorial(demo));
        break;
      case DEMO_FORMS.CODE_NOTEBOOK:
        generatedFiles.push(await this.generateCodeNotebook(demo));
        break;
      case DEMO_FORMS.STATIC_DOCS:
        generatedFiles.push(await this.generateStaticDocs(demo));
        break;
      default:
        // Generate static docs as fallback
        generatedFiles.push(await this.generateStaticDocs(demo));
    }

    // Always generate canvas file if data provided
    if (demo.canvasData) {
      const canvasDir = path.join(this.outputDir, demo.category);
      try {
        await fs.mkdir(canvasDir, { recursive: true });
      } catch (error) {
        // Directory already exists
      }
      const canvasFile = path.join(canvasDir, `${demo.id}.canvas`);
      await fs.writeFile(canvasFile, JSON.stringify(demo.canvasData, null, 2));
      generatedFiles.push(canvasFile);
    }

    return generatedFiles;
  }

  async generateSuite(demoConfigs) {
    console.log(`🎯 Generating ${demoConfigs.length} demos...`);
    
    const results = [];
    
    for (const config of demoConfigs) {
      const demo = this.createDemo(config);
      const files = await this.generateDemo(demo);
      
      results.push({
        demo,
        files,
        success: true
      });
      
      console.log(`✅ Generated: ${demo.title} (${files.length} files)`);
    }

    // Generate index
    await this.generateDemoIndex(results);
    
    return results;
  }

  async generateDemoIndex(results) {
    const index = {
      title: 'MIND-GIT Demo Suite',
      description: 'Comprehensive demonstrations of MIND-GIT capabilities including CanvasL visual programming, AAL verification, and P2P federation.',
      generated: new Date().toISOString(),
      totalDemos: results.length,
      categories: {},
      demos: results.map(r => ({
        id: r.demo.id,
        title: r.demo.title,
        description: r.demo.description,
        category: r.demo.category,
        audience: r.demo.audience,
        form: r.demo.form,
        functions: r.demo.functions,
        difficulty: r.demo.difficulty,
        estimatedTime: r.demo.estimatedTime,
        files: r.files.map(f => path.relative(this.outputDir, f))
      }))
    };

    // Group by category
    results.forEach(r => {
      const cat = r.demo.category;
      if (!index.categories[cat]) {
        index.categories[cat] = [];
      }
      index.categories[cat].push(r.demo.id);
    });

    const indexPath = path.join(this.outputDir, 'index.json');
    await fs.writeFile(indexPath, JSON.stringify(index, null, 2));

    // Generate HTML index
    const htmlIndex = this.generateHTMLIndex(index);
    const htmlPath = path.join(this.outputDir, 'index.html');
    await fs.writeFile(htmlPath, htmlIndex);

    console.log(`📚 Demo index generated: ${indexPath}`);
  }

  generateHTMLIndex(index) {
    return `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>${index.title}</title>
    <script src="https://cdn.tailwindcss.com"></script>
</head>
<body class="bg-gray-50 min-h-screen">
    <div class="container mx-auto px-4 py-8">
        <header class="mb-8">
            <h1 class="text-4xl font-bold text-gray-900 mb-2">${index.title}</h1>
            <p class="text-xl text-gray-600">${index.description}</p>
            <p class="text-sm text-gray-500 mt-2">Generated: ${new Date(index.generated).toLocaleString()}</p>
        </header>

        <div class="mb-8">
            <div class="bg-white rounded-lg shadow p-6">
                <h2 class="text-2xl font-semibold mb-4">Quick Stats</h2>
                <div class="grid grid-cols-2 md:grid-cols-4 gap-4">
                    <div class="text-center">
                        <div class="text-3xl font-bold text-blue-600">${index.totalDemos}</div>
                        <div class="text-sm text-gray-600">Total Demos</div>
                    </div>
                    <div class="text-center">
                        <div class="text-3xl font-bold text-green-600">${Object.keys(index.categories).length}</div>
                        <div class="text-sm text-gray-600">Categories</div>
                    </div>
                    <div class="text-center">
                        <div class="text-3xl font-bold text-purple-600">${new Set(index.demos.map(d => d.audience)).size}</div>
                        <div class="text-sm text-gray-600">Audiences</div>
                    </div>
                    <div class="text-center">
                        <div class="text-3xl font-bold text-orange-600">${new Set(index.demos.map(d => d.form)).size}</div>
                        <div class="text-sm text-gray-600">Formats</div>
                    </div>
                </div>
            </div>
        </div>

        <div class="grid gap-6">
            ${index.demos.map(demo => `
                <div class="bg-white rounded-lg shadow-lg p-6 hover:shadow-xl transition-shadow">
                    <div class="flex justify-between items-start mb-4">
                        <h3 class="text-xl font-semibold text-gray-900">${demo.title}</h3>
                        <span class="px-3 py-1 bg-blue-100 text-blue-800 rounded-full text-sm">${demo.difficulty}</span>
                    </div>
                    <p class="text-gray-600 mb-4">${demo.description}</p>
                    <div class="flex flex-wrap gap-2 mb-4">
                        <span class="px-2 py-1 bg-gray-100 text-gray-700 rounded text-xs">${demo.category}</span>
                        <span class="px-2 py-1 bg-gray-100 text-gray-700 rounded text-xs">${demo.audience}</span>
                        <span class="px-2 py-1 bg-gray-100 text-gray-700 rounded text-xs">${demo.form}</span>
                        <span class="px-2 py-1 bg-gray-100 text-gray-700 rounded text-xs">${demo.estimatedTime}</span>
                    </div>
                    <div class="flex gap-2">
                        ${demo.files.map(file => {
                          const ext = file.split('.').pop();
                          const icon = ext === 'html' ? '🌐' : ext === 'ipynb' ? '📓' : ext === 'md' ? '📄' : '📁';
                          return `<a href="${file}" class="px-3 py-1 bg-blue-600 text-white rounded hover:bg-blue-700 transition text-sm">${icon} ${ext.toUpperCase()}</a>`;
                        }).join('')}
                    </div>
                </div>
            `).join('')}
        </div>
    </div>
</body>
</html>`;
  }
}

// Export for use as module
export default DemoSuiteGenerator;

// CLI interface
if (import.meta.url === `file://${process.argv[1]}`) {
  const generator = new DemoSuiteGenerator();
  
  generator.initialize().then(() => {
    console.log('🎉 Demo Suite Generator ready!');
    console.log('Use generateDemoConfigs() to create demo configurations');
  }).catch(console.error);
}