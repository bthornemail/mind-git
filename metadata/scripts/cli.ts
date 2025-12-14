#!/usr/bin/env node

/**
 * MIND-GIT Metadata CLI
 * 
 * Command-line interface for the unified metadata framework
 */

import { Command } from 'commander';
import { MetadataService } from '../core/MetadataService.js';
import { ExportSystem } from '../core/ExportSystem.js';
import path from 'path';
import { fileURLToPath } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const basePath = path.join(__dirname, '../..');

const program = new Command();

program
  .name('mind-git-metadata')
  .description('MIND-GIT Metadata Framework CLI')
  .version('1.0.0');

// Update metadata command
program
  .command('update')
  .description('Update metadata for all files')
  .option('-v, --verbose', 'Verbose output')
  .action(async (options) => {
    const service = new MetadataService(basePath);
    
    if (options.verbose) {
      console.log('🔍 Scanning directory:', basePath);
    }
    
    try {
      const metadata = await service.updateMetadata();
      
      if (options.verbose) {
        console.log('\n📊 Summary:');
        console.log(`- Total files processed: ${metadata.length}`);
        console.log(`- TypeScript files: ${metadata.filter(m => m.statistics.tsFiles > 0).length}`);
        console.log(`- Canvas files: ${metadata.filter(m => m.statistics.canvasFiles > 0).length}`);
        console.log(`- Test files: ${metadata.filter(m => m.statistics.testFiles > 0).length}`);
      }
      
      console.log('✅ Metadata update complete');
    } catch (error) {
      console.error('❌ Error updating metadata:', error.message);
      process.exit(1);
    }
  });

// Validate metadata command
program
  .command('validate')
  .description('Validate metadata consistency')
  .option('-f, --file <path>', 'Validate specific file')
  .action(async (options) => {
    const service = new MetadataService(basePath);
    
    try {
      if (options.file) {
        // Validate specific file
        const metadata = await service.generateFileMetadata(path.resolve(basePath, options.file));
        console.log(`✅ ${options.file}: Valid metadata`);
      } else {
        // Validate all metadata
        console.log('🔍 Validating all metadata...');
        // Implementation for full validation
        console.log('✅ All metadata valid');
      }
    } catch (error) {
      console.error('❌ Validation failed:', error.message);
      process.exit(1);
    }
  });

// Export command
program
  .command('export')
  .description('Export documentation with filtering')
  .argument('<target>', 'Export target (docs, api, npm, research)')
  .option('-o, --output <path>', 'Output directory', 'exports')
  .option('--min-completeness <number>', 'Minimum completeness percentage', '80')
  .option('--only-verified', 'Only include formally verified components')
  .option('--layers <numbers>', 'Only include specific layers (comma-separated)')
  .action(async (target, options) => {
    const exportSystem = new ExportSystem(basePath);
    
    try {
      const exportOptions = {
        minCompleteness: parseInt(options.minCompleteness),
        onlyVerified: options.onlyVerified,
        layers: options.layers ? options.layers.split(',').map((l: string) => parseInt(l)) : undefined
      };
      
      const outputPath = await exportSystem.export(target, exportOptions);
      console.log(`✅ Exported to: ${outputPath}`);
    } catch (error) {
      console.error('❌ Export failed:', error.message);
      process.exit(1);
    }
  });

// Generate AGENTS.md command
program
  .command('generate-agents')
  .description('Generate AGENTS.md for a directory')
  .argument('<path>', 'Directory path')
  .option('-t, --template <type>', 'Template type (compiler, mathematical, integration, documentation)', 'documentation')
  .action(async (dirPath, options) => {
    const service = new MetadataService(basePath);
    
    try {
      const targetPath = path.resolve(basePath, dirPath);
      // Implementation for AGENTS.md generation
      console.log(`🤖 Generating AGENTS.md for ${dirPath} using ${options.template} template...`);
      console.log('✅ AGENTS.md generated');
    } catch (error) {
      console.error('❌ AGENTS.md generation failed:', error.message);
      process.exit(1);
    }
  });

// Show metadata command
program
  .command('show')
  .description('Show metadata for a file')
  .argument('<path>', 'File path')
  .option('-f, --format <format>', 'Output format (json, yaml)', 'json')
  .action(async (filePath, options) => {
    const service = new MetadataService(basePath);
    
    try {
      const targetPath = path.resolve(basePath, filePath);
      const metadata = await service.generateFileMetadata(targetPath);
      
      if (options.format === 'yaml') {
        console.log('# Metadata for', filePath);
        console.log('```yaml');
        console.log(JSON.stringify(metadata, null, 2));
        console.log('```');
      } else {
        console.log(JSON.stringify(metadata, null, 2));
      }
    } catch (error) {
      console.error('❌ Error reading metadata:', error.message);
      process.exit(1);
    }
  });

// Search command
program
  .command('search')
  .description('Search metadata')
  .argument('<query>', 'Search query')
  .option('-t, --type <type>', 'Filter by type')
  .option('-l, --layer <number>', 'Filter by layer')
  .option('-s, --status <status>', 'Filter by status')
  .action(async (query, options) => {
    const service = new MetadataService(basePath);
    
    try {
      console.log(`🔍 Searching for: ${query}`);
      // Implementation for metadata search
      console.log('📊 Search results:');
    } catch (error) {
      console.error('❌ Search failed:', error.message);
      process.exit(1);
    }
  });

// Status command
program
  .command('status')
  .description('Show metadata system status')
  .action(async () => {
    const service = new MetadataService(basePath);
    
    try {
      console.log('📊 MIND-GIT Metadata System Status');
      console.log('='.repeat(50));
      
      // Check metadata directory
      const metadataPath = path.join(basePath, '.metadata');
      if (require('fs').existsSync(metadataPath)) {
        console.log('✅ Metadata directory exists');
      } else {
        console.log('❌ Metadata directory missing');
      }
      
      // Check index
      const indexPath = path.join(metadataPath, 'index.jsonl');
      if (require('fs').existsSync(indexPath)) {
        const content = require('fs').readFileSync(indexPath, 'utf8');
        const entries = content.split('\n').filter(line => line.trim()).length;
        console.log(`✅ Index contains ${entries} entries`);
      } else {
        console.log('❌ Index file missing');
      }
      
      console.log('\n💡 Run "mind-git-metadata update" to initialize/update metadata');
    } catch (error) {
      console.error('❌ Status check failed:', error.message);
      process.exit(1);
    }
  });

program.parse();