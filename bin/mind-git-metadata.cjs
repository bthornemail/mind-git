#!/usr/bin/env node

/**
 * MIND-GIT CLI with Metadata Integration
 */

import { Command } from 'commander';
import { execSync } from 'child_process';
import path from 'path';

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
  mind-git compile example.canvas
  mind-git metadata:update
  mind-git metadata:export docs --min-completeness 80
  mind-git metadata:export research --only-verified
  mind-git metadata:status

For more information, see: metadata/README.md
    `);
  });

program.parse();