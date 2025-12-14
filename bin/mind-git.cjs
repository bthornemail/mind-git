#!/usr/bin/env node

/**
 * @domain DIGITAL
 * @purpose CLI interface for CanvasL visual compiler
 * @warning This compiles virtual structures only; no claims about physical reality
 */

const { program } = require('commander');
const { readFile, writeFile } = require('fs/promises');
const { resolve } = require('path');

program
  .name('mind-git')
  .description('CanvasL visual compiler - spatial diagrams to executable code')
  .version('1.1.0');

program
  .command('compile')
  .description('Compile a .canvas file to executable JavaScript')
  .argument('<canvas-file>', 'Path to .canvas file')
  .option('-o, --output <file>', 'Output JavaScript file', 'output.js')
  .option('-t, --target <lang>', 'Target language (js, ts)', 'js')
  .action(async (canvasFile, options) => {
    try {
      console.log(`🎯 Compiling ${canvasFile}...`);
      
      const canvasPath = resolve(canvasFile);
      const canvasData = await readFile(canvasPath, 'utf-8');
      const canvas = JSON.parse(canvasData);
      
      // Dynamic import for ES module
      const { CanvasLCompiler } = await import('../logos-system/dist/index.js');
      const compiler = new CanvasLCompiler();
      const result = await compiler.compileCanvas(canvas);
      
      if (result.success) {
        console.log('✅ Compilation successful!');
        console.log(`📄 Generated ${options.target.toUpperCase()} code:`);
        console.log('─'.repeat(50));
        console.log(result.generated_code.javascript_code);
        console.log('─'.repeat(50));
        
        // Write to output file if specified
        if (options.output !== 'output.js') {
          await writeFile(options.output, result.generated_code.javascript_code);
          console.log(`💾 Saved to ${options.output}`);
        }
      } else {
        console.error('❌ Compilation failed:');
        console.error(result.errors);
        process.exit(1);
      }
    } catch (error) {
      console.error('❌ Error:', error.message);
      process.exit(1);
    }
  });

program
  .command('test')
  .description('Run built-in test suite')
  .action(async () => {
    try {
      console.log('🧪 Running CanvasL test suite...');
      const { execSync } = await import('child_process');
      execSync('npm test', { stdio: 'inherit', cwd: 'logos-system' });
    } catch (error) {
      console.error('❌ Tests failed');
      process.exit(1);
    }
  });

program
  .command('version')
  .description('Show version and system info')
  .action(() => {
    console.log('🚀 MindGit v1.1.0');
    console.log('📐 CanvasL Visual Compiler');
    console.log('🔬 Mathematical Foundation: Complete');
    console.log('✅ Status: Production Ready');
  });

program.parse();