/**
 * Simple example: Compile spatial-hello-world.json and run the output
 */

import { CanvasLCompiler } from '../logos-system/src/compiler';
import { readFileSync, writeFileSync } from 'fs';
import { join } from 'path';

async function main() {
  // Load the canvas file
  const canvasPath = join(__dirname, 'spatial-hello-world.json');
  const canvasJSON = JSON.parse(readFileSync(canvasPath, 'utf-8'));

  console.log('🎨 Compiling spatial-hello-world.json to JavaScript...\n');

  // Create compiler
  const compiler = new CanvasLCompiler({
    target_languages: ['javascript'],
    target_platform: 'javascript',
    optimization_level: 0,
    include_comments: true,
    include_debug_info: false,
    hopf_optimization: false,
    polynomial_optimization: false,
    include_proofs: false,
    enable_verification: false,
    generate_visualization: false,
    include_profiling: false,
    error_recovery_mode: 'lenient'
  });

  // Compile
  const result = await compiler.compileCanvas(canvasJSON);

  if (!result.success) {
    console.error('❌ Compilation failed!');
    result.errors.forEach(err => console.error(`  - ${err.message}`));
    process.exit(1);
  }

  const jsCode = result.generated_code?.javascript_code;

  if (!jsCode) {
    console.error('❌ No JavaScript code generated!');
    process.exit(1);
  }

  console.log('\n📜 Generated JavaScript:\n');
  console.log('━'.repeat(60));
  console.log(jsCode);
  console.log('━'.repeat(60));

  // Write to file
  const outputPath = join(__dirname, 'spatial-hello-world.js');
  writeFileSync(outputPath, jsCode);
  console.log(`\n✅ Saved to: ${outputPath}\n`);

  // Execute the generated code
  console.log('▶️  Executing generated code:\n');
  console.log('━'.repeat(60));
  eval(jsCode);
  console.log('━'.repeat(60));

  console.log('\n✨ Success!\n');
}

main().catch(console.error);
