#!/usr/bin/env node

/**
 * MIND-GIT CLI with Metadata Integration (CommonJS)
 */

const { Command } = require('commander');
const { execSync } = require('child_process');
const path = require('path');

const program = new Command();

program
  .name('mind-git-metadata')
  .description('MIND-GIT Metadata Framework CLI')
  .version('1.0.0');

// Metadata update command
program
  .command('update')
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

// Export command
program
  .command('export')
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

// Status command
program
  .command('status')
  .description('Show metadata system status')
  .action(() => {
    console.log('📊 MIND-GIT Metadata Status');
    console.log('='.repeat(50));
    
    const metadataPath = path.join(process.cwd(), '.metadata');
    const fs = require('fs');
    
    // Check metadata directory
    if (fs.existsSync(metadataPath)) {
      console.log('✅ Metadata directory exists');
      
      // Check index
      const indexPath = path.join(metadataPath, 'index.jsonl');
      if (fs.existsSync(indexPath)) {
        const content = fs.readFileSync(indexPath, 'utf8');
        const entries = content.split('\n').filter(line => line.trim()).length;
        console.log(`✅ Index contains ${entries} components`);
      } else {
        console.log('❌ Index file missing');
      }
      
      // Check exports
      const exportsPath = path.join(metadataPath, 'exports');
      if (fs.existsSync(exportsPath)) {
        const exports = fs.readdirSync(exportsPath);
        console.log(`✅ Exports directory contains ${exports.length} files`);
      } else {
        console.log('⚠️ Exports directory missing');
      }
    } else {
      console.log('❌ Metadata directory missing');
      console.log('💡 Run "mind-git-metadata update" to initialize');
    }
  });

// List export targets
program
  .command('list')
  .description('List available export targets')
  .action(() => {
    console.log('Available export targets:');
    console.log('  docs     - General documentation');
    console.log('  api      - API reference');
    console.log('  npm      - NPM package export');
    console.log('  research - Research papers');
    console.log('  all      - All components');
  });

// Help command
program
  .command('help')
  .description('Show help information')
  .action(() => {
    console.log(`
🧠 MIND-GIT Metadata Framework

🎯 Commands:
  update                    Update all component metadata
  export <target>           Export filtered documentation
  status                    Show metadata system status
  list                      List available export targets

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

Examples:
  mind-git-metadata update
  mind-git-metadata export docs --min-completeness 80
  mind-git-metadata export research --only-verified
  mind-git-metadata status

For more information, see: metadata/README.md
    `);
  });

program.parse();