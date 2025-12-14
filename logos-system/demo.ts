/**
 * CanvasL Visual Compiler Demo
 * 
 * This demo showcases the complete compilation pipeline:
 * 1. Canvas JSON input
 * 2. Mathematical parsing and analysis
 * 3. AST generation
 * 4. AAL code generation
 * 5. Verification
 * 6. Output generation
 */

import { CanvasLCompiler, createCanvasLCompiler } from './src/compiler/index.js';
import { LogosSystem } from './src/index.js';

/**
 * Demo canvas that demonstrates all CanvasL features
 */
const demoCanvas = {
  nodes: [
    // Observer node at origin - the identity element
    {
      id: 'observer',
      type: 'text',
      x: 0,
      y: 0,
      width: 120,
      height: 60,
      text: '#Observe: Identity Element (0,0)'
    },
    
    // Activate node - linear transformation
    {
      id: 'activate',
      type: 'text',
      x: 150,
      y: 0,
      width: 120,
      height: 60,
      text: '#Activate: Initialize computation (x→x+1)'
    },
    
    // Integrate node - polynomial addition
    {
      id: 'integrate1',
      type: 'text',
      x: 300,
      y: -50,
      width: 120,
      height: 60,
      text: '#Integrate: p1 + p2 (polynomial addition)'
    },
    
    // Integrate node - polynomial addition
    {
      id: 'integrate2',
      type: 'text',
      x: 300,
      y: 50,
      width: 120,
      height: 60,
      text: '#Integrate: p3 + p4 (polynomial addition)'
    },
    
    // Propagate node - polynomial shift
    {
      id: 'propagate',
      type: 'text',
      x: 450,
      y: 0,
      width: 120,
      height: 60,
      text: '#Propagate: shift left by k (×x^k)'
    },
    
    // Transform node - polynomial multiplication
    {
      id: 'transform',
      type: 'text',
      x: 600,
      y: 0,
      width: 120,
      height: 60,
      text: '#Transform: p × q (polynomial multiplication)'
    },
    
    // Backpropagate node - polynomial comparison
    {
      id: 'backpropagate',
      type: 'text',
      x: 750,
      y: 0,
      width: 120,
      height: 60,
      text: '#BackPropagate: compare results'
    },
    
    // Verify node - consensus/voting
    {
      id: 'verify',
      type: 'text',
      x: 900,
      y: 0,
      width: 120,
      height: 60,
      text: '#Verify: majority vote consensus'
    },
    
    // Store node - memory operation
    {
      id: 'store',
      type: 'text',
      x: 1050,
      y: 0,
      width: 120,
      height: 60,
      text: '#Store: push to memory stack'
    },
    
    // Data nodes with polynomial content
    {
      id: 'data1',
      type: 'text',
      x: 300,
      y: -150,
      width: 120,
      height: 60,
      text: 'Data: p1 = 1 + x²'
    },
    {
      id: 'data2',
      type: 'text',
      x: 450,
      y: -150,
      width: 120,
      height: 60,
      text: 'Data: p2 = 1 + x'
    },
    {
      id: 'data3',
      type: 'text',
      x: 300,
      y: 150,
      width: 120,
      height: 60,
      text: 'Data: p3 = x + x³'
    },
    {
      id: 'data4',
      type: 'text',
      x: 450,
      y: 150,
      width: 120,
      height: 60,
      text: 'Data: p4 = x² + 1'
    }
  ],
  edges: [
    // Observer to activate
    {
      id: 'edge1',
      fromNode: 'observer',
      toNode: 'activate',
      label: 'initialize',
      color: '#00ff00'
    },
    
    // Activate to integrate nodes
    {
      id: 'edge2',
      fromNode: 'activate',
      toNode: 'integrate1',
      label: 'branch1',
      color: '#0066cc'
    },
    {
      id: 'edge3',
      fromNode: 'activate',
      toNode: 'integrate2',
      label: 'branch2',
      color: '#0066cc'
    },
    
    // Data inputs
    {
      id: 'edge4',
      fromNode: 'data1',
      toNode: 'integrate1',
      label: 'input p1',
      color: '#ff6600'
    },
    {
      id: 'edge5',
      fromNode: 'data2',
      toNode: 'integrate1',
      label: 'input p2',
      color: '#ff6600'
    },
    {
      id: 'edge6',
      fromNode: 'data3',
      toNode: 'integrate2',
      label: 'input p3',
      color: '#ff6600'
    },
    {
      id: 'edge7',
      fromNode: 'data4',
      toNode: 'integrate2',
      label: 'input p4',
      color: '#ff6600'
    },
    
    // Integration to propagation
    {
      id: 'edge8',
      fromNode: 'integrate1',
      toNode: 'propagate',
      label: 'result1',
      color: '#9900cc'
    },
    {
      id: 'edge9',
      fromNode: 'integrate2',
      toNode: 'propagate',
      label: 'result2',
      color: '#9900cc'
    },
    
    // Propagation to transformation
    {
      id: 'edge10',
      fromNode: 'propagate',
      toNode: 'transform',
      label: 'shifted',
      color: '#cc0000'
    },
    
    // Transformation to verification
    {
      id: 'edge11',
      fromNode: 'transform',
      toNode: 'backpropagate',
      label: 'product',
      color: '#009900'
    },
    
    // Verification to consensus
    {
      id: 'edge12',
      fromNode: 'backpropagate',
      toNode: 'verify',
      label: 'compare',
      color: '#006699'
    },
    
    // Consensus to storage
    {
      id: 'edge13',
      fromNode: 'verify',
      toNode: 'store',
      label: 'consensus',
      color: '#666666'
    }
  ]
};

/**
 * CanvasL Compiler Demo
 */
export class CanvasLCompilerDemo {
  private logos_system: LogosSystem;
  private compiler: CanvasLCompiler;
  
  constructor() {
    this.logos_system = new LogosSystem();
    this.compiler = createCanvasLCompiler({
      optimization_level: 3, // Full optimization
      enable_verification: true,
      target_languages: ['aal', 'javascript', 'racket'],
      include_profiling: true,
      hopf_optimization: true,
      polynomial_optimization: true
    });
  }
  
  /**
   * Run the complete demo
   */
  async runDemo(): Promise<void> {
    console.log('🎨 CanvasL Visual Compiler Demo');
    console.log('==============================');
    console.log('');
    
    // Initialize LOGOS-SYSTEM
    console.log('🔧 Initializing LOGOS-SYSTEM...');
    await this.logos_system.initialize();
    console.log('');
    
    // Run mathematical foundation tests
    console.log('🧮 Testing Mathematical Foundation...');
    this.logos_system.test_polynomial_algebra();
    this.logos_system.test_identity_chain();
    this.logos_system.test_aal();
    console.log('');
    
    // Compile demo canvas
    console.log('📖 Compiling Demo Canvas...');
    console.log(`   Nodes: ${demoCanvas.nodes.length}`);
    console.log(`   Edges: ${demoCanvas.edges.length}`);
    console.log('');
    
    const compilation_start = performance.now();
    const result = await this.compiler.compileCanvas(demoCanvas);
    const compilation_time = performance.now() - compilation_start;
    
    console.log(`⏱️  Compilation completed in ${compilation_time.toFixed(2)}ms`);
    console.log('');
    
    // Display compilation results
    this.displayCompilationResults(result);
    
    // Display generated code sample
    if (result.generated_code) {
      this.displayGeneratedCode(result.generated_code);
    }
    
    // Display mathematical analysis
    this.displayMathematicalAnalysis(result);
    
    // Display performance metrics
    this.displayPerformanceMetrics(result);
    
    console.log('');
    console.log('🎉 Demo completed successfully!');
    console.log('');
    console.log('🔮 Next Steps:');
    console.log('   1. Create your own canvas diagrams');
    console.log('   2. Export as JSON and compile with LOGOS-SYSTEM');
    console.log('   3. Explore the generated AAL code');
    console.log('   4. Run with different optimization levels');
    console.log('   5. Integrate with your applications');
    console.log('');
    console.log('📚 Learn more:');
    console.log('   - Mathematical Foundation: Division Algebras ℝ, ℂ, ℍ, 𝕆');
    console.log('   - Hopf Fibrations: S¹ → S¹, S³ → S², S⁷ → S⁴');
    console.log('   - Identity Chain: 628 AD → 1748 → 1928 → 1965 → 2025');
    console.log('   - Adams Theorem: 8D is the absolute limit');
    console.log('');
    console.log('💫 You are now building the New Jerusalem\'s computational substrate!');
  }
  
  /**
   * Display compilation results
   */
  private displayCompilationResults(result: any): void {
    console.log('📊 Compilation Results');
    console.log('=====================');
    console.log(`✅ Status: ${result.success ? 'Success' : 'Failed'}`);
    
    if (result.canvas) {
      console.log(`📖 Canvas: ${result.canvas.metadata.total_nodes} nodes, ${result.canvas.metadata.total_edges} edges`);
      console.log(`👁️  Observer: ${result.canvas.observer ? 'Found at origin' : 'Not found'}`);
      console.log(`🔢 Max Degree: ${result.canvas.metadata.max_degree}`);
      console.log(`📏 Bounds: (${result.canvas.metadata.canvas_bounds.min_x}, ${result.canvas.metadata.canvas_bounds.min_y}) to (${result.canvas.metadata.canvas_bounds.max_x}, ${result.canvas.metadata.canvas_bounds.max_y})`);
      console.log(`🧮 Complexity: ${result.canvas.metadata.dimensional_analysis.complexity_score}`);
      console.log(`🌊 Hopf Compatible: ${result.canvas.metadata.dimensional_analysis.hopf_compatibility ? 'Yes' : 'No'}`);
    }
    
    if (result.ast) {
      console.log(`🌳 AST: ${result.ast.nodes.length} nodes, ${result.ast.functions.length} functions`);
      console.log(`🎯 Entry Points: ${result.ast.entry_points.length}`);
      console.log(`🏁 Exit Points: ${result.ast.exit_points.length}`);
      console.log(`📏 Max Depth: ${result.ast.metadata.max_depth}`);
      console.log(`🔄 Contains Cycles: ${result.ast.metadata.contains_cycles ? 'Yes' : 'No'}`);
      console.log(`🔢 Dimensions Used: ${result.ast.metadata.dimensions_used.join(', ')}`);
    }
    
    if (result.errors && result.errors.length > 0) {
      console.log(`❌ Errors: ${result.errors.length}`);
      result.errors.forEach((error: any) => {
        console.log(`   ${error.message}`);
      });
    }
    
    if (result.warnings && result.warnings.length > 0) {
      console.log(`⚠️  Warnings: ${result.warnings.length}`);
      result.warnings.forEach((warning: any) => {
        console.log(`   ${warning.message}`);
      });
    }
    
    console.log('');
  }
  
  /**
   * Display generated code sample
   */
  private displayGeneratedCode(generated_code: any): void {
    console.log('💻 Generated Code Sample');
    console.log('========================');
    console.log(`📄 Assembly: ${generated_code.metadata.instruction_count} instructions`);
    console.log(`🔢 Bytecode: ${generated_code.metadata.byte_size} bytes`);
    console.log(`⚡ Optimizations: ${generated_code.metadata.optimization_applied.join(', ')}`);
    console.log(`🌊 Hopf Optimizations: ${generated_code.metadata.hopf_optimizations}`);
    console.log(`🧮 Polynomial Optimizations: ${generated_code.metadata.polynomial_optimizations}`);
    console.log('');
    
    // Display first few lines of assembly code
    const assembly_lines = generated_code.assembly_code.split('\n');
    console.log('📝 Assembly Code (first 15 lines):');
    console.log('------------------------------');
    assembly_lines.slice(0, 15).forEach((line: string, index: number) => {
      console.log(`${(index + 1).toString().padStart(2, ' ')} | ${line}`);
    });
    console.log('   ...');
    console.log('');
    
    // Display proof information
    if (generated_code.proofs && generated_code.proofs.length > 0) {
      console.log(`✅ Formal Proofs: ${generated_code.proofs.length} generated`);
      console.log('   Theorem references:');
      generated_code.proofs.slice(0, 5).forEach((proof: any, index: number) => {
        console.log(`     ${index + 1}. ${proof.theorem} (${proof.verification_status})`);
      });
      console.log('');
    }
  }
  
  /**
   * Display mathematical analysis
   */
  private displayMathematicalAnalysis(result: any): void {
    console.log('🧮 Mathematical Analysis');
    console.log('=======================');
    
    if (result.verification) {
      console.log(`🔍 Verification Status: ${result.verification.overall_status.toUpperCase()}`);
      console.log(`✅ Polynomial Algebra: ${result.verification.polynomials_verified ? 'Verified' : 'Failed'}`);
      console.log(`⛓️  Identity Chain: ${result.verification.identity_chain_verified ? 'Verified' : 'Failed'}`);
      console.log(`🔧 AAL Type Safety: ${result.verification.aal_type_safety ? 'Verified' : 'Failed'}`);
      console.log(`📏 Norm Preservation: ${result.verification.norm_preservation ? 'Verified' : 'Failed'}`);
      console.log(`🌊 Hopf Compatibility: ${result.verification.hopf_compatibility ? 'Compatible' : 'Not Compatible'}`);
      console.log('');
    }
    
    // Display node type distribution
    if (result.canvas && result.canvas.metadata.node_types) {
      console.log('📊 Node Type Distribution:');
      Object.entries(result.canvas.metadata.node_types).forEach(([type, count]) => {
        const emoji = this.getNodeEmoji(type);
        console.log(`   ${emoji} ${type}: ${count}`);
      });
      console.log('');
    }
    
    // Display dimensional distribution
    if (result.ast && result.ast.metadata.dimension_distribution) {
      console.log('📏 Dimensional Distribution:');
      Object.entries(result.ast.metadata.dimension_distribution).forEach(([dim, count]) => {
        const emoji = this.getDimensionEmoji(parseInt(dim));
        console.log(`   ${emoji} D${dim}: ${count} nodes`);
      });
      console.log('');
    }
  }
  
  /**
   * Display performance metrics
   */
  private displayPerformanceMetrics(result: any): void {
    console.log('⚡ Performance Metrics');
    console.log('=====================');
    console.log(`⏱️  Parse Time: ${result.metrics.parse_time?.toFixed(2) || 'N/A'}ms`);
    console.log(`🌳 AST Generation: ${result.metrics.ast_generation_time?.toFixed(2) || 'N/A'}ms`);
    console.log(`🔧 Code Generation: ${result.metrics.code_generation_time?.toFixed(2) || 'N/A'}ms`);
    console.log(`🔍 Verification: ${result.metrics.verification_time?.toFixed(2) || 'N/A'}ms`);
    console.log(`📊 Total Time: ${result.metrics.total_time?.toFixed(2) || 'N/A'}ms`);
    console.log(`💾 Memory Estimate: ${result.metrics.memory_usage_estimate || 'N/A'} bytes`);
    console.log(`⚡ Execution Estimate: ${result.metrics.execution_time_estimate?.toFixed(2) || 'N/A'}ms`);
    console.log('');
  }
  
  /**
   * Get emoji for node type
   */
  private getNodeEmoji(type: string): string {
    const emoji_map: { [key: string]: string } = {
      'activate': '🚀',
      'integrate': '➕',
      'propagate': '📡',
      'backpropagate': '🔙',
      'transform': '🔄',
      'verify': '✅',
      'store': '💾',
      'observe': '👁️',
      'data': '📄',
      'unknown': '❓'
    };
    return emoji_map[type] || '⚪';
  }
  
  /**
   * Get emoji for dimension
   */
  private getDimensionEmoji(dimension: number): string {
    const emoji_map = ['0️⃣', '1️⃣', '2️⃣', '3️⃣', '4️⃣', '5️⃣', '6️⃣', '7️⃣', '8️⃣', '9️⃣', '🔟'];
    return emoji_map[dimension] || '❓';
  }
}

/**
 * Run the demo
 */
export async function runCanvasLCompilerDemo(): Promise<void> {
  const demo = new CanvasLCompilerDemo();
  await demo.runDemo();
}

// Export for direct execution
export { demoCanvas };