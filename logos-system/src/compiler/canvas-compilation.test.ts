/**
 * Canvas → JavaScript Compilation Tests
 *
 * Tests the complete pipeline: Canvas JSON → Parser → AST → JavaScript
 */

import { CanvasLCompiler } from './index';
import { readFileSync } from 'fs';
import { join } from 'path';

describe('Canvas → JavaScript Compilation', () => {

  test('compiles spatial-hello-world canvas to working JavaScript', async () => {
    // Load the example canvas
    const canvasPath = join(__dirname, '../../../examples/spatial-hello-world.json');
    const canvasJSON = JSON.parse(readFileSync(canvasPath, 'utf-8'));

    // Create compiler with JavaScript target
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

    // Compile the canvas
    const result = await compiler.compileCanvas(canvasJSON);

    // Check compilation succeeded
    expect(result.success).toBe(true);
    expect(result.errors.length).toBe(0);

    // Check JavaScript code was generated
    expect(result.generated_code).not.toBeNull();
    expect(result.generated_code?.javascript_code).toBeDefined();

    const jsCode = result.generated_code!.javascript_code!;

    // Verify the generated JavaScript contains expected elements
    expect(jsCode).toContain('console.log');
    expect(jsCode).toContain('Hello from spatial programming');

    // Log the generated code for inspection
    console.log('\n📜 Generated JavaScript:\n');
    console.log(jsCode);
    console.log('\n');

    // Optionally: Execute the generated JavaScript (in a safe way)
    // For now, just verify it's valid syntax by attempting to create a Function
    expect(() => {
      new Function(jsCode);
    }).not.toThrow();
  });

  test('canvas parser recognizes different node types', async () => {
    const canvasPath = join(__dirname, '../../../examples/spatial-hello-world.json');
    const canvasJSON = JSON.parse(readFileSync(canvasPath, 'utf-8'));

    const compiler = new CanvasLCompiler({
      target_languages: ['javascript'],
      target_platform: 'javascript',
      optimization_level: 0,
      include_comments: false,
      include_debug_info: false,
      hopf_optimization: false,
      polynomial_optimization: false,
      include_proofs: false,
      enable_verification: false,
      generate_visualization: false,
      include_profiling: false,
      error_recovery_mode: 'lenient'
    });

    const result = await compiler.compileCanvas(canvasJSON);

    // Verify AST was generated with nodes
    expect(result.ast).not.toBeNull();
    expect(result.ast?.nodes.length).toBeGreaterThan(0);

    // Verify canvas was parsed
    expect(result.canvas).not.toBeNull();
    expect(result.canvas?.metadata.total_nodes).toBeGreaterThan(0);
  });

});
