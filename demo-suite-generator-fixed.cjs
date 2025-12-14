#!/usr/bin/env node

/**
 * MIND-GIT Demo Suite Generator
 * 
 * Generates comprehensive demos for MIND-GIT system based on:
 * - Categories (Basic, Verification, Visual, Distributed, Applied, Advanced)
 * - Audiences (Developers, Researchers, Enterprises, AI/ML, General Users, Power Users)
 * - Forms (Interactive, Video, Notebook, Webinar, Documentation, VR/AR)
 * - Functions (Node Creation, Formal Proofs, Visual Compilation, Federation, Evolution, Integration)
 */

const fs = require('fs');
const path = require('path');

console.log('🎯 MIND-GIT Demo Suite Generator');
console.log('='.repeat(80));

// ============================================================================
// DEMO CONFIGURATION TEMPLATES
// ============================================================================

const demoCategories = {
  basic: {
    name: 'Basic/Introductory',
    description: 'Core mechanics without advanced math or distribution',
    complexity: 'beginner',
    duration: '5-10 minutes'
  },
  verification: {
    name: 'Verification-Focused',
    description: 'Formal proofs and mathematical integrity',
    complexity: 'intermediate',
    duration: '10-15 minutes'
  },
  visual: {
    name: 'Visual & Spatial',
    description: 'CanvasL-driven demos with topological diagrams',
    complexity: 'intermediate',
    duration: '10-20 minutes'
  },
  distributed: {
    name: 'Distributed & P2P',
    description: 'Real-time federation, mesh networking, contradiction resolution',
    complexity: 'advanced',
    duration: '15-25 minutes'
  },
  applied: {
    name: 'Applied/Real-World',
    description: 'Industry-specific scenarios',
    complexity: 'advanced',
    duration: '20-30 minutes'
  },
  advanced: {
    name: 'Advanced Mathematical',
    description: 'Deep dives into Pfister identities, Hadamard matrices',
    complexity: 'expert',
    duration: '25-40 minutes'
  }
};

const audiences = {
  developers: {
    name: 'Developers/Engineers',
    focus: 'Hands-on code examples, API integrations, Git-like workflows',
    delivery: ['interactive', 'notebook', 'documentation']
  },
  researchers: {
    name: 'Researchers/Academics',
    focus: 'Proof extraction, theorem verification, mathematical exploration',
    delivery: ['notebook', 'webinar', 'documentation']
  },
  enterprises: {
    name: 'Enterprises/Organizations',
    focus: 'Scalability, security, business integrations',
    delivery: ['webinar', 'documentation', 'interactive']
  },
  ai_ml: {
    name: 'AI/ML Practitioners',
    focus: 'Self-evolving systems, semantic graphs, verifiable reasoning',
    delivery: ['notebook', 'interactive', 'webinar']
  },
  general: {
    name: 'General Users/Educators',
    focus: 'Simplified interfaces for knowledge building and teaching',
    delivery: ['interactive', 'video', 'documentation']
  },
  power_users: {
    name: 'Power Users/Innovators',
    focus: 'Custom extensions, P2P experiments, quantum features',
    delivery: ['vr_ar', 'interactive', 'webinar']
  }
};

const deliveryFormats = {
  interactive: {
    name: 'Interactive Tutorial',
    platform: 'Web-based (GitHub Pages, Streamlit)',
    features: ['Live code execution', 'Step-by-step guidance', 'Real-time feedback']
  },
  video: {
    name: 'Video Walkthrough',
    platform: 'YouTube (5-15 min screencasts)',
    features: ['Visual demonstration', 'Narration', 'Code highlighting']
  },
  notebook: {
    name: 'Code Notebook',
    platform: 'Jupyter/Colab',
    features: ['Runnable cells', 'Experimentation', 'Documentation integration']
  },
  webinar: {
    name: 'Live Webinar/Demo',
    platform: 'Zoom/Teams',
    features: ['Real-time Q&A', 'Live P2P simulation', 'Interactive discussion']
  },
  documentation: {
    name: 'Static Documentation',
    platform: 'Markdown (README.md)',
    features: ['Screenshots', 'Embeddable snippets', 'Offline access']
  },
  vr_ar: {
    name: 'VR/AR Experience',
    platform: 'A-Frame/WebXR',
    features: ['Immersive 3D topology', 'Spatial interaction', 'Quantum visualization']
  }
};

const coreFunctions = {
  node_creation: {
    name: 'Node Creation & Editing',
    description: 'Adding/verifying semantic nodes with polynomial encoding'
  },
  formal_proofs: {
    name: 'Formal Proof Generation',
    description: 'Running LEAN/Coq on AAL nodes, extracting to WebAssembly'
  },
  visual_compilation: {
    name: 'Visual Compilation',
    description: 'Building/Compiling CanvasL diagrams to verified assembly/code'
  },
  federation: {
    name: 'Federation & Sync',
    description: 'P2P connections, real-time updates, voting-based contradiction resolution'
  },
  evolution: {
    name: 'Self-Evolution & Optimization',
    description: 'Applying evolutionary cycles with proof guarantees'
  },
  integration: {
    name: 'Integration & Extensions',
    description: 'API hooks, custom schemas, enterprise workflows'
  }
};

// ============================================================================
// DEMO GENERATOR CLASS
// ============================================================================

class MindGitDemoGenerator {
  constructor() {
    this.demos = [];
    this.outputDir = './demos';
    this.ensureOutputDirectory();
  }

  ensureOutputDirectory() {
    if (!fs.existsSync(this.outputDir)) {
      fs.mkdirSync(this.outputDir, { recursive: true });
    }
  }

  generateDemo(category, audience, format, functions) {
    const demoId = `${category}_${audience}_${format}_${Date.now()}`;
    const demo = {
      id: demoId,
      category: demoCategories[category],
      audience: audiences[audience],
      format: deliveryFormats[format],
      functions: functions.map(f => coreFunctions[f]),
      generated: new Date().toISOString(),
      files: []
    };

    // Generate demo files based on configuration
    this.generateDemoFiles(demo);
    this.demos.push(demo);
    
    return demo;
  }

  generateDemoFiles(demo) {
    const demoDir = path.join(this.outputDir, demo.id);
    fs.mkdirSync(demoDir, { recursive: true });

    // Generate main demo file
    const mainFile = this.generateMainDemoFile(demo);
    fs.writeFileSync(path.join(demoDir, 'index.js'), mainFile);
    demo.files.push('index.js');

    // Generate README
    const readme = this.generateReadme(demo);
    fs.writeFileSync(path.join(demoDir, 'README.md'), readme);
    demo.files.push('README.md');

    // Generate format-specific files
    switch (demo.format.name) {
      case 'Interactive Tutorial':
        this.generateInteractiveFiles(demo, demoDir);
        break;
      case 'Code Notebook':
        this.generateNotebookFiles(demo, demoDir);
        break;
      case 'VR/AR Experience':
        this.generateVRFiles(demo, demoDir);
        break;
      case 'Video Walkthrough':
        this.generateVideoFiles(demo, demoDir);
        break;
      case 'Live Webinar/Demo':
        this.generateWebinarFiles(demo, demoDir);
        break;
      case 'Static Documentation':
        this.generateDocumentationFiles(demo, demoDir);
        break;
    }

    console.log(`✅ Generated demo: ${demo.id} in ${demoDir}`);
  }

  generateMainDemoFile(demo) {
    const functions = demo.functions.map(f => `
  // ${f.name}: ${f.description}
  async function ${f.name.replace(/\s+/g, '_').toLowerCase()}() {
    console.log('🔧 Executing: ${f.name}');
    // Implementation would go here
    return { success: true, message: '${f.name} completed' };
  }`).join('\n');

    return `/**
 * MIND-GIT Demo: ${demo.category.name}
 * Audience: ${demo.audience.name}
 * Format: ${demo.format.name}
 * Generated: ${demo.generated}
 */

const { MindGitSystem } = require('../../mind-git-final-system.cjs');

class DemoRunner {
  constructor() {
    this.mindGit = new MindGitSystem();
    this.results = [];
  }

  async runDemo() {
    console.log('🚀 Starting MIND-GIT Demo');
    console.log('='.repeat(80));
    console.log(`📂 Category: ${demo.category.name}`);
    console.log(`👥 Audience: ${demo.audience.name}`);
    console.log(`📺 Format: ${demo.format.name}`);
    console.log(`🔧 Functions: ${demo.functions.map(f => f.name).join(', ')}`);
    console.log('='.repeat(80));

    try {
      // Initialize MIND-GIT system
      await this.mindGit.initialize();
      
      // Execute demo functions
      ${functions}
      
      // Generate report
      this.generateReport();
      
    } catch (error) {
      console.error('❌ Demo failed:', error.message);
    }
  }

  generateReport() {
    const report = {
      timestamp: new Date().toISOString(),
      demo_id: '${demo.id}',
      category: '${demo.category.name}',
      audience: '${demo.audience.name}',
      format: '${demo.format.name}',
      functions_executed: ${demo.functions.length},
      results: this.results,
      status: 'completed'
    };

    console.log('\n📊 Demo Report');
    console.log('='.repeat(80));
    console.log(JSON.stringify(report, null, 2));
    
    return report;
  }
}

// Run the demo
if (require.main === module) {
  const runner = new DemoRunner();
  runner.runDemo().catch(console.error);
}

module.exports = { DemoRunner, MindGitDemoGenerator };
`;
  }

  generateReadme(demo) {
    return `# ${demo.category.name} Demo

**Audience:** ${demo.audience.name}  
**Format:** ${demo.format.name}  
**Generated:** ${demo.generated}  

## Description
${demo.category.description}

## Target Audience Focus
${demo.audience.focus}

## Format Features
${demo.format.features.map(f => `- ${f}`).join('\n')}

## Functions Demonstrated
${demo.functions.map(f => `- **${f.name}:** ${f.description}`).join('\n')}

## How to Run

### Interactive Tutorial
\`\`\`bash
# Install dependencies
npm install

# Run the demo
node index.js
\`\`\`

### Code Notebook
\`\`\`bash
# Open in Jupyter
jupyter notebook

# Or open in Google Colab
# Upload and run index.ipynb
\`\`\`

### VR/AR Experience
\`\`\`bash
# Serve the VR experience
python -m http.server 8000

# Open in browser
open http://localhost:8000/vr.html
\`\`\`

## Expected Output
The demo will demonstrate:
${demo.functions.map(f => `- ${f.name}`).join('\n')}

## Files
${demo.files.map(f => `- \`${f}\``).join('\n')}

## Support
For issues or questions:
- GitHub: https://github.com/bthornemail/mind-git/issues
- Documentation: https://mind-git.dev/docs
`;
  }

  generateInteractiveFiles(demo, demoDir) {
    const htmlContent = `
<!DOCTYPE html>
<html>
<head>
    <title>MIND-GIT Interactive Demo</title>
    <script src="https://cdn.tailwindcss.com"></script>
</head>
<body class="bg-gray-900 text-white p-8">
    <div class="max-w-4xl mx-auto">
        <h1 class="text-3xl font-bold mb-4">MIND-GIT Interactive Demo</h1>
        <div class="mb-6">
            <h2 class="text-xl mb-2">${demo.category.name}</h2>
            <p class="text-gray-300">${demo.category.description}</p>
        </div>
        
        <div class="grid grid-cols-2 gap-4 mb-6">
            <div class="bg-gray-800 p-4 rounded">
                <h3 class="font-bold mb-2">Functions</h3>
                <ul class="space-y-2">
                    ${demo.functions.map(f => `<li><button onclick="runFunction('${f.name.replace(/\s+/g, '_').toLowerCase()}')" class="bg-blue-600 hover:bg-blue-700 px-3 py-1 rounded">${f.name}</button></li>`).join('')}
                </ul>
            </div>
            <div class="bg-gray-800 p-4 rounded">
                <h3 class="font-bold mb-2">Output</h3>
                <div id="output" class="bg-black p-3 rounded font-mono text-sm h-64 overflow-y-auto"></div>
            </div>
        </div>
    </div>

    <script>
        async function runFunction(functionName) {
            const output = document.getElementById('output');
            output.innerHTML += '<div class="text-green-400">🔧 Running: ' + functionName + '</div>';
            
            try {
                const response = await fetch('/api/' + functionName);
                const result = await response.json();
                output.innerHTML += '<div class="text-blue-400">✅ ' + result.message + '</div>';
            } catch (error) {
                output.innerHTML += '<div class="text-red-400">❌ Error: ' + error.message + '</div>';
            }
        }
    </script>
</body>
</html>`;
    
    fs.writeFileSync(path.join(demoDir, 'interactive.html'), htmlContent);
    demo.files.push('interactive.html');
  }

  generateNotebookFiles(demo, demoDir) {
    const notebookContent = {
      cells: demo.functions.map(f => ({
        cell_type: 'code',
        execution_count: null,
        metadata: {},
        outputs: [],
        source: [
          `# ${f.name}`,
          `# ${f.description}`,
          `# TODO: Implement ${f.name} functionality`,
          `print("🔧 Executing: ${f.name}")`,
          `result = {"success": true, "message": "${f.name} completed"}`,
          `print("✅ Result: " + result['message'] + ")"`
        ].join('\n')
      })),
      metadata: {
        kernelspec: {
          display_name: 'Node.js',
          language: 'javascript',
          name: 'nodejs'
        }
      },
      nbformat: 4,
      nbformat_minor: 5
    };

    fs.writeFileSync(path.join(demoDir, 'demo.ipynb'), JSON.stringify(notebookContent, null, 2));
    demo.files.push('demo.ipynb');
  }

  generateVRFiles(demo, demoDir) {
    const vrContent = `
<!DOCTYPE html>
<html>
<head>
    <title>MIND-GIT VR Experience</title>
    <script src="https://aframe.io/releases/1.3.0/aframe.min.js"></script>
</head>
<body>
    <a-scene background="color: #1a1a2e">
        <a-sky color="#000428"></a-sky>
        
        <!-- MIND-GIT Logo -->
        <a-box position="-2 1.5 -3" rotation="0 45 0" width="1.5" height="1.5" depth="0.1" color="#4CAF50"></a-box>
        <a-text position="-2 2.5 -3" value="MIND-GIT" color="white" width="3"></a-text>
        
        <!-- Function Nodes -->
        ${demo.functions.map((f, i) => `
        <a-sphere position="${i * 2 - 3} 1.5 -3" radius="0.5" color="#2196F3">
            <a-text position="0 0.7 0" value="${f.name}" color="white" width="2" align="center"></a-text>
        </a-sphere>
        `).join('')}
        
        <!-- Connection Lines -->
        ${demo.functions.map((f, i) => {
          if (i < demo.functions.length - 1) {
            return `<a-cylinder position="${i * 2 - 2} 1 -3" radius="0.05" height="1" color="#FFC107"></a-cylinder>`;
          }
          return '';
        }).join('')}
        
        <!-- Camera -->
        <a-camera position="0 1.6 4" look-at="0 1.5 0"></a-camera>
    </a-scene>

    <script>
        // Interactive VR elements
        document.querySelectorAll('a-sphere').forEach((sphere, index) => {
            sphere.addEventListener('click', function() {
                const functionName = '${demo.functions[index].name}';
                console.log('🔧 VR Interaction:', functionName);
                
                // Visual feedback
                sphere.setAttribute('color', '#4CAF50');
                setTimeout(() => {
                    sphere.setAttribute('color', '#2196F3');
                }, 500);
            });
        });
    </script>
</body>
</html>`;
    
    fs.writeFileSync(path.join(demoDir, 'vr.html'), vrContent);
    demo.files.push('vr.html');
  }

  generateVideoFiles(demo, demoDir) {
    const scriptContent = `# MIND-GIT Video Demo Script

## ${demo.category.name} - ${demo.audience.name}

### Video Structure (5-15 minutes)

#### Introduction (1-2 min)
- Welcome to MIND-GIT
- Overview of ${demo.category.description}
- Target audience: ${demo.audience.name}

#### Demo Functions (${demo.functions.length * 2} min)
${demo.functions.map(f => `
#### ${f.name} (2 min)
- Screen recording of ${f.description}
- Code walkthrough
- Expected output demonstration
- Key learning points
`).join('\n')}

#### Conclusion (1-2 min)
- Summary of demonstrated capabilities
- Next steps for learning
- Resources for further exploration

### Recording Instructions

#### Setup
\`\`\`bash
# Start screen recording
# macOS: Cmd + Shift + 5
# Windows: Win + Alt + G
# Linux: Ctrl + Shift + Alt + R

# Run demo in separate terminal
node index.js
\`\`\`

#### Key Points to Emphasize
1. **Mathematical Verification**: Show formal proofs
2. **Real-time P2P**: Demonstrate federation
3. **Visual Programming**: Highlight CanvasL features
4. **Self-Evolution**: Show optimization cycles

#### Post-Production
1. Edit video (add captions, highlights)
2. Upload to YouTube
3. Create GitHub issue with video link
4. Update documentation with video embed

### Sample Commands for Recording
\`\`\`bash
# Clear terminal
clear

# Run with timestamps
node index.js | ts '[%Y-%m-%d %H:%M:%S]'

# Highlight important outputs
grep -E "(✅|❌|🔧)"
\`\`\`
`;
    
    fs.writeFileSync(path.join(demoDir, 'video-script.md'), scriptContent);
    demo.files.push('video-script.md');
  }

  generateWebinarFiles(demo, demoDir) {
    const slidesContent = `# MIND-GIT Webinar Slides

## ${demo.category.name}
### ${demo.audience.name} Webinar

---

### Slide 1: Title Slide
- MIND-GIT: ${demo.category.name}
- ${demo.category.description}
- Duration: ${demo.category.duration}
- Presenter: [Your Name]

### Slide 2: Agenda
- Introduction to MIND-GIT (5 min)
- Live Demo Functions (${demo.functions.length * 3} min)
- Q&A Session (10 min)
- Resources & Next Steps (5 min)

### Slide 3: What is MIND-GIT?
- Git for Meaning: Version control for semantic state
- AAL Verification: Mathematical proofs with LEAN/Coq
- CanvasL Programming: Visual spatial computation
- P2P Federation: Real-time distributed synchronization

${demo.functions.map((f, i) => `
### Slide ${4 + i}: ${f.name}
#### ${f.description}
#### Live Demo:
- Run command: \`node index.js\`
- Show expected output
- Explain mathematical foundation
- Highlight verification results

#### Key Points:
- ${f.name} ensures mathematical correctness
- Formal proofs generated automatically
- Integration with existing workflows
`).join('\n')}

### Slide ${4 + demo.functions.length}: Q&A Preparation
- Common questions about ${demo.category.name}
- Technical deep-dive topics
- Integration scenarios
- Performance considerations

### Slide ${5 + demo.functions.length}: Resources
- Documentation: https://mind-git.dev/docs
- GitHub: https://github.com/bthornemail/mind-git
- Community: Discord/Slack links
- Support: support@mind-git.dev

### Slide ${6 + demo.functions.length}: Thank You
- Contact information
- Follow-up resources
- Next webinar announcement
`;
    
    fs.writeFileSync(path.join(demoDir, 'webinar-slides.md'), slidesContent);
    demo.files.push('webinar-slides.md');
  }

  generateDocumentationFiles(demo, demoDir) {
    const apiDocs = `# MIND-GIT API Documentation

## ${demo.category.name} API Reference

### Overview
This document provides API reference for ${demo.category.description}.

### Installation
\`\`\`bash
npm install mind-git
\`\`\`

### Quick Start
\`\`\`javascript
const { MindGitSystem } = require('mind-git');

const system = new MindGitSystem();
await system.initialize();
\`\`\`

${demo.functions.map(f => `
## ${f.name}

### Description
${f.description}

### API Reference
\`\`\`javascript
// ${f.name} example
const result = await system.${f.name.replace(/\s+/g, '_').toLowerCase()}();
console.log(result.message);
\`\`\`

### Parameters
- \`options\` (Object, optional): Configuration options
- \`callback\` (Function, optional): Completion callback

### Returns
\`\`\`javascript
{
  success: boolean,
  message: string,
  data?: any,
  proof?: string
}
\`\`\`

### Example
\`\`\`javascript
// Basic usage
const result = await system.${f.name.replace(/\s+/g, '_').toLowerCase()}();
if (result.success) {
  console.log('✅', result.message);
} else {
  console.error('❌', result.message);
}
\`\`\`

### Error Handling
\`\`\`javascript
try {
  const result = await system.${f.name.replace(/\s+/g, '_').toLowerCase()}();
} catch (error) {
  console.error('Error:', error.message);
  // Handle error appropriately
}
\`\`\`
`).join('\n')}

## Integration Examples

### Express.js
\`\`\`javascript
const express = require('express');
const { MindGitSystem } = require('mind-git');

const app = express();
const mindGit = new MindGitSystem();

app.post('/api/${demo.functions[0].name.replace(/\s+/g, '_').toLowerCase()}', async (req, res) => {
  try {
    const result = await mindGit.${demo.functions[0].name.replace(/\s+/g, '_').toLowerCase()}(req.body);
    res.json(result);
  } catch (error) {
    res.status(500).json({ error: error.message });
  }
});

app.listen(3000);
\`\`\`

### React Component
\`\`\`jsx
import React, { useState, useEffect } from 'react';
import { MindGitSystem } from 'mind-git';

function MindGitComponent() {
  const [result, setResult] = useState(null);
  const mindGit = new MindGitSystem();

  useEffect(() => {
    mindGit.${demo.functions[0].name.replace(/\s+/g, '_').toLowerCase()}()
      .then(setResult)
      .catch(console.error);
  }, []);

  return (
    <div>
      <h2>MIND-GIT Demo</h2>
      {result && <p>{result.message}</p>}
    </div>
  );
}

export default MindGitComponent;
\`\`\`
`;
    
    fs.writeFileSync(path.join(demoDir, 'api-docs.md'), apiDocs);
    demo.files.push('api-docs.md');
  }

  generateSuite() {
    console.log('\n🎯 Generating Complete Demo Suite...');
    console.log('='.repeat(80));

    // Generate 6 example demos covering all combinations
    const demoConfigs = [
      {
        category: 'basic',
        audience: 'developers',
        format: 'interactive',
        functions: ['node_creation', 'integration']
      },
      {
        category: 'verification',
        audience: 'researchers',
        format: 'notebook',
        functions: ['formal_proofs', 'node_creation']
      },
      {
        category: 'visual',
        audience: 'general',
        format: 'video',
        functions: ['visual_compilation', 'node_creation']
      },
      {
        category: 'distributed',
        audience: 'enterprises',
        format: 'webinar',
        functions: ['federation', 'evolution']
      },
      {
        category: 'applied',
        audience: 'ai_ml',
        format: 'documentation',
        functions: ['evolution', 'integration']
      },
      {
        category: 'advanced',
        audience: 'power_users',
        format: 'vr_ar',
        functions: ['formal_proofs', 'federation', 'visual_compilation']
      }
    ];

    for (const config of demoConfigs) {
      this.generateDemo(
        config.category,
        config.audience,
        config.format,
        config.functions
      );
    }

    // Generate suite index
    this.generateSuiteIndex();

    console.log(`\n✅ Generated ${this.demos.length} demos in ./${this.outputDir}/`);
    console.log('\n📊 Demo Suite Summary:');
    console.log('='.repeat(80));
    
    const summary = {};
    for (const demo of this.demos) {
      const key = `${demo.category.name} → ${demo.audience.name}`;
      if (!summary[key]) summary[key] = [];
      summary[key].push(demo.format.name);
    }

    for (const [key, formats] of Object.entries(summary)) {
      console.log(`${key}: ${formats.join(', ')}`);
    }

    return this.demos;
  }

  generateSuiteIndex() {
    const indexContent = `# MIND-GIT Demo Suite

**Generated:** ${new Date().toISOString()}  
**Total Demos:** ${this.demos.length}

## Quick Start

Choose a demo based on your needs:

### By Category
${Object.entries(demoCategories).map(([key, cat]) => 
  `- **${cat.name}** (${cat.complexity}): ${cat.description}`
).join('\n')}

### By Audience
${Object.entries(audiences).map(([key, aud]) => 
  `- **${aud.name}**: ${aud.focus}`
).join('\n')}

### By Format
${Object.entries(deliveryFormats).map(([key, fmt]) => 
  `- **${fmt.name}**: ${fmt.features.join(', ')}`
).join('\n')}

## Available Demos

${this.demos.map(demo => `
### ${demo.id}

- **Category:** ${demo.category.name}
- **Audience:** ${demo.audience.name}  
- **Format:** ${demo.format.name}
- **Functions:** ${demo.functions.map(f => f.name).join(', ')}
- **Files:** ${demo.files.length} generated
- **Path:** \`./demos/${demo.id}/\`

[Run Demo](./demos/${demo.id}/)
`).join('\n')}

## Running Demos

### Interactive Demos
\`\`\`bash
cd demos/[demo-id]
node index.js
\`\`\`

### Notebook Demos
\`\`\`bash
cd demos/[demo-id]
jupyter notebook demo.ipynb
\`\`\`

### VR/AR Demos
\`\`\`bash
cd demos/[demo-id]
python -m http.server 8000
open http://localhost:8000/vr.html
\`\`\`

### Webinar Presentations
\`\`\`bash
cd demos/[demo-id]
# Use webinar-slides.md for your presentation
\`\`\`

## Contributing

To add new demos:

1. Choose category, audience, format, and functions
2. Run: \`node generate-demo-suite.js\`
3. Test your demo
4. Submit pull request

## Support

- **Issues:** https://github.com/bthornemail/mind-git/issues
- **Documentation:** https://mind-git.dev/docs
- **Community:** https://discord.gg/mind-git
`;

    fs.writeFileSync(path.join(this.outputDir, 'README.md'), indexContent);
  }
}

// ============================================================================
// MAIN EXECUTION
// ============================================================================

async function generateDemoSuite() {
  console.log('🎯 MIND-GIT Demo Suite Generator');
  console.log('='.repeat(80));
  
  const generator = new MindGitDemoGenerator();
  const demos = generator.generateSuite();
  
  console.log('\n🚀 Demo Suite Generation Complete!');
  console.log('='.repeat(80));
  console.log('\n📈 Next Steps:');
  console.log('1. Review generated demos in ./demos/');
  console.log('2. Test each demo for functionality');
  console.log('3. Record video walkthroughs for each demo');
  console.log('4. Set up interactive web hosting');
  console.log('5. Schedule webinar sessions');
  console.log('6. Publish to GitHub Pages');
  console.log('7. Promote through community channels');
  
  console.log('\n💡 Tips for Success:');
  console.log('- Start with basic demos before advancing');
  console.log('- Tailor content to specific audience needs');
  console.log('- Include real-world use cases');
  console.log('- Demonstrate formal verification prominently');
  console.log('- Show P2P federation in action');
  console.log('- Highlight mathematical guarantees');
  console.log('- Provide clear next steps for learning');
  
  return demos;
}

// ============================================================================
// EXECUTE GENERATOR
// ============================================================================

if (require.main === module) {
  generateDemoSuite().catch(error => {
    console.error('\n❌ Error generating demo suite:', error.message);
    process.exit(1);
  });
}

module.exports = { MindGitDemoGenerator, generateDemoSuite };