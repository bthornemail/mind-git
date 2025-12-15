#!/usr/bin/env node

/**
 * MIND-GIT CLI with Metadata Integration
 */

const { Command } = require('commander');
const { execSync } = require('child_process');
const path = require('path');

const program = new Command();

program
  .name('mind-git')
  .description('MIND-GIT Mathematical Foundation & Metadata Framework')
  .version('1.1.0');

// Original compile command
program
  .command('compile')
  .description('Compile CanvasL files to executable code')
  .argument('<canvas-file>', 'CanvasL file to compile')
  .option('-o, --output <path>', 'Output directory', 'dist')
  .option('-f, --format <format>', 'Output format (js, ts, racket)', 'js')
  .action((canvasFile, options) => {
    console.log(`🔧 Compiling ${canvasFile}...`);
    // Delegate to existing CLI
    try {
      execSync(`node ${path.join(__dirname, '../bin/mind-git-simple.cjs')} ${canvasFile}`, { stdio: 'inherit' });
    } catch (error) {
      console.error('❌ Compilation failed:', error.message);
      process.exit(1);
    }
  });

// New metadata commands
program
  .command('metadata')
  .description('Metadata management commands')
  .addHelpCommand(true);

program
  .command('metadata:update')
  .description('Update metadata for all components')
  .action(() => {
    console.log('🔄 Updating metadata...');
    try {
      execSync('cd metadata && node scripts/integrate-metadata-simple.js', { stdio: 'inherit' });
    } catch (error) {
      console.error('❌ Metadata update failed:', error.message);
      process.exit(1);
    }
  });

program
  .command('metadata:export')
  .description('Export documentation with metadata filtering')
  .argument('<target>', 'Export target (docs, api, npm, research, all)')
  .option('--min-completeness <number>', 'Minimum completeness percentage')
  .option('--only-verified', 'Only include formally verified components')
  .option('--layers <numbers>', 'Only include specific layers (comma-separated)')
  .action((target, options) => {
    console.log(`📤 Exporting ${target}...`);
    
    let command = `cd metadata && node scripts/export-system-simple.js export ${target}`;
    
    if (options.minCompleteness) {
      command += ` --min-completeness ${options.minCompleteness}`;
    }
    if (options.onlyVerified) {
      command += ` --only-verified`;
    }
    if (options.layers) {
      command += ` --layers ${options.layers}`;
    }
    
    try {
      execSync(command, { stdio: 'inherit' });
    } catch (error) {
      console.error('❌ Export failed:', error.message);
      process.exit(1);
    }
  });

program
  .command('metadata:status')
  .description('Show metadata system status')
  .action(() => {
    console.log('📊 MIND-GIT Metadata Status');
    console.log('='.repeat(50));
    
    try {
      execSync('cd metadata && node scripts/cli.js status', { stdio: 'inherit' });
    } catch (error) {
      console.error('❌ Status check failed:', error.message);
      process.exit(1);
    }
  });

program
  .command('metadata:generate-agents')
  .description('Generate AGENTS.md for a directory')
  .argument('<path>', 'Directory path')
  .option('-t, --template <type>', 'Template type', 'documentation')
  .action((dirPath, options) => {
    console.log(`🤖 Generating AGENTS.md for ${dirPath}...`);
    try {
      execSync(`cd metadata && node scripts/cli.js generate-agents ${dirPath} --template ${options.template}`, { stdio: 'inherit' });
    } catch (error) {
      console.error('❌ AGENTS.md generation failed:', error.message);
      process.exit(1);
    }
  });

// Universal Kernel Commands
program
  .command('kernel:analyze')
  .description('Analyze any Git repository with Universal Metadata Kernel')
  .argument('[path]', 'Repository path (defaults to current directory)', '.')
  .action((repoPath) => {
    console.log(`🧠 Analyzing repository with Universal Metadata Kernel...`);
    try {
      execSync(`node ${path.join(__dirname, '../universal-metadata-kernel.js')} analyze ${repoPath}`, { stdio: 'inherit' });
    } catch (error) {
      console.error('❌ Kernel analysis failed:', error.message);
      process.exit(1);
    }
  });

program
  .command('kernel:visualize')
  .description('Generate CanvasL visualization of repository')
  .argument('[path]', 'Repository path (defaults to current directory)', '.')
  .action((repoPath) => {
    console.log(`🎨 Generating CanvasL visualization...`);
    try {
      execSync(`node ${path.join(__dirname, '../universal-metadata-kernel.js')} visualize ${repoPath}`, { stdio: 'inherit' });
    } catch (error) {
      console.error('❌ Visualization failed:', error.message);
      process.exit(1);
    }
  });

program
  .command('kernel:export')
  .description('Export repository metadata to federated formats')
  .argument('[path]', 'Repository path (defaults to current directory)', '.')
  .option('--format <format>', 'Export format (all, json, jsonld, markdown, rdf, ipfs, federation)', 'export')
  .option('--layers <layers>', 'Filter by layers (e.g., 1,2,3)')
  .option('--only-mathematical', 'Only export mathematical components')
  .option('--max-complexity <num>', 'Maximum complexity threshold')
  .action((repoPath, options) => {
    console.log(`📤 Exporting repository metadata...`);
    try {
      const kernelPath = path.join(repoPath, '.metadata-kernel');

      // Default to 'export' (all formats)
      const format = options.format === 'all' ? 'export' : options.format;

      let command = `node ${path.join(__dirname, '../universal-exporter.js')} ${format} ${kernelPath}`;

      if (options.layers) command += ` --layers ${options.layers}`;
      if (options.onlyMathematical) command += ` --only-mathematical`;
      if (options.maxComplexity) command += ` --max-complexity ${options.maxComplexity}`;

      execSync(command, { stdio: 'inherit' });
    } catch (error) {
      console.error('❌ Export failed:', error.message);
      process.exit(1);
    }
  });

// Pfister Inference Commands
program
  .command('kernel:connect')
  .description('Connect two repositories with Pfister 32 semantic inference')
  .argument('<repo-a>', 'First repository path')
  .argument('<repo-b>', 'Second repository path')
  .option('--export <dir>', 'Export results to directory', './pfister-results')
  .action((repoA, repoB, options) => {
    console.log(`🧮 Connecting repositories with Pfister 32 inference...`);
    try {
      let command = `node ${path.join(__dirname, '../pfister-inference-engine.js')} connect ${repoA} ${repoB}`;

      if (options.export) {
        command += ` --export ${options.export}`;
      }

      execSync(command, { stdio: 'inherit' });
    } catch (error) {
      console.error('❌ Connection analysis failed:', error.message);
      process.exit(1);
    }
  });

// Help command
program
  .command('help')
  .description('Show help information')
  .action(() => {
    console.log(`
🧠 MIND-GIT Mathematical Foundation & Metadata Framework

🎯 Core Commands:
  mind-git compile <canvas-file>     Compile CanvasL to executable code
  mind-git metadata:update            Update all component metadata
  mind-git metadata:export <target>   Export filtered documentation
  mind-git metadata:status           Show metadata system status

🧠 Universal Kernel Commands:
  mind-git kernel:analyze [path]     Analyze any Git repository
  mind-git kernel:visualize [path]   Generate CanvasL visualization
  mind-git kernel:export [path]      Export repository metadata
  mind-git kernel:connect <a> <b>    Pfister 32 semantic inference

📤 Export Targets:
  docs        - General documentation export
  api         - API reference export
  npm         - NPM package export
  research    - Research papers export
  all         - Export all components

🏷️ Export Options:
  --min-completeness <num>   Minimum completeness percentage
  --only-verified             Only formally verified components
  --layers <1,2,3>          Only specific layers

📁 Metadata Structure:
  .metadata/                    - Hidden metadata directory
  ├── index.jsonl              - Global component index
  ├── relationships.jsonl       - Component relationships
  ├── exports/                  - Generated exports
  └── .hidden/                 - Runtime metadata cache

🔗 Integration:
  - CanvasL visual programming
  - Mathematical foundation tracking
  - Formal verification status
  - AGENTS.md development directives

Examples:
  # Compile CanvasL
  mind-git compile example.canvas

  # Metadata operations
  mind-git metadata:update
  mind-git metadata:export docs --min-completeness 80
  mind-git metadata:export research --only-verified
  mind-git metadata:status

  # Universal Kernel (works on any repository!)
  mind-git kernel:analyze .
  mind-git kernel:analyze /path/to/react
  mind-git kernel:visualize /path/to/any-repo
  mind-git kernel:export . --format json

  # Pfister 32 Semantic Inference (NEW!)
  mind-git kernel:connect /path/to/repo-a /path/to/repo-b
  mind-git kernel:connect ~/lodash ~/flask --export ./results

🌟 The Universal Kernel works on ANY Git repository:
  - JavaScript/TypeScript (Node.js, React, Vue, etc.)
  - Python (Flask, Django, FastAPI, etc.)
  - Rust, Go, Java, C++, and more!
  - Automatically detects language and framework
  - Generates AGENTS.md development contracts
  - Creates CanvasL visualizations for Obsidian

🧮 Pfister 32 Semantic Inference (Mathematical Composition):
  - Connects TWO repositories with norm-preserving composition
  - 32-dimensional semantic space (8 layers × 4 features)
  - Finds integration points and emergent patterns
  - Mathematically guaranteed: ||A ⊗ B|| = ||A|| × ||B||
  - Based on Pfister's 32-square identity (1967)

For more information, see: metadata/README.md
    `);
  });

program.parse();