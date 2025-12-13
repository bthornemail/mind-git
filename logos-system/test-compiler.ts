/**
 * CanvasL Visual Compiler Test Suite
 * 
 * Comprehensive tests for the complete compilation pipeline:
 * Canvas JSON → Parser → AST → AAL Code → Verification
 */

import { CanvasLCompiler, createCanvasLCompiler } from '../src/compiler';
import { CanvasJSON } from '../src/json.canvas';

/**
 * Test canvas data
 */
const testCanvas: CanvasJSON = {
  nodes: [
    // Observer node at origin (identity element)
    {
      id: 'observer',
      type: 'text',
      x: 0,
      y: 0,
      width: 100,
      height: 50,
      text: '#Observe: Identity Element'
    },
    
    // Activate node (JMP)
    {
      id: 'activate1',
      type: 'text',
      x: 100,
      y: 0,
      width: 100,
      height: 50,
      text: '#Activate: Start computation'
    },
    
    // Integrate node (ADD)
    {
      id: 'integrate1',
      type: 'text',
      x: 250,
      y: 0,
      width: 100,
      height: 50,
      text: '#Integrate: data + value'
    },
    
    // Propagate node (SHL)
    {
      id: 'propagate1',
      type: 'text',
      x: 400,
      y: 0,
      width: 100,
      height: 50,
      text: '#Propagate: shift left'
    },
    
    // Transform node (MUL)
    {
      id: 'transform1',
      type: 'text',
      x: 550,
      y: 0,
      width: 100,
      height: 50,
      text: '#Transform: multiply'
    },
    
    // Verify node (VOTE)
    {
      id: 'verify1',
      type: 'text',
      x: 700,
      y: 0,
      width: 100,
      height: 50,
      text: '#Verify: consensus check'
    },
    
    // Data node
    {
      id: 'data1',
      type: 'text',
      x: 200,
      y: 100,
      width: 100,
      height: 50,
      text: 'Initial data: 42'
    },
    
    // Store node (PUSH)
    {
      id: 'store1',
      type: 'text',
      x: 400,
      y: 100,
      width: 100,
      height: 50,
      text: '#Store: result'
    }
  ],
  edges: [
    {
      id: 'edge1',
      fromNode: 'observer',
      toNode: 'activate1',
      label: 'activate'
    },
    {
      id: 'edge2',
      fromNode: 'activate1',
      toNode: 'integrate1',
      label: 'data flow'
    },
    {
      id: 'edge3',
      fromNode: 'integrate1',
      toNode: 'propagate1',
      label: 'transform'
    },
    {
      id: 'edge4',
      fromNode: 'propagate1',
      toNode: 'transform1',
      label: 'compute'
    },
    {
      id: 'edge5',
      fromNode: 'transform1',
      toNode: 'verify1',
      label: 'validate'
    },
    {
      id: 'edge6',
      fromNode: 'data1',
      toNode: 'integrate1',
      label: 'input'
    },
    {
      id: 'edge7',
      fromNode: 'verify1',
      toNode: 'store1',
      label: 'output'
    }
  ]
};

/**
 * Test suite runner
 */
export class CanvasLCompilerTestSuite {
  private compiler: CanvasLCompiler;
  private test_results: TestResult[] = [];
  
  constructor() {
    this.compiler = createCanvasLCompiler({
      optimization_level: 2,
      enable_verification: true,
      target_languages: ['aal', 'javascript']
    });
  }
  
  /**
   * Run all tests
   */
  async runAllTests(): Promise<TestSuiteResult> {
    console.log('🧪 CanvasL Visual Compiler Test Suite');
    console.log('====================================');
    
    const test_methods = [
      this.testBasicCompilation.bind(this),
      this.testParserFunctionality.bind(this),
      this.testASTGeneration.bind(this),
      this.testAALCodeGeneration.bind(this),
      this.testMathematicalVerification.bind(this),
      this.testOptimizationLevels.bind(this),
      this.testErrorHandling.bind(this),
      this.testComplexCanvas.bind(this)
    ];
    
    const results = await Promise.allSettled(test_methods.map(async (test, index) => {
      const test_name = this.getTestName(test, index);
      console.log(`\n📋 Running test: ${test_name}`);
      
      try {
        const start_time = performance.now();
        await test();
        const duration = performance.now() - start_time;
        
        const result: TestResult = {
          name: test_name,
          passed: true,
          duration,
          message: 'Test passed successfully'
        };
        
        console.log(`✅ ${test_name} (${duration.toFixed(2)}ms)`);
        this.test_results.push(result);
        return result;
        
      } catch (error) {
        const duration = performance.now() - start_time;
        
        const result: TestResult = {
          name: test_name,
          passed: false,
          duration,
          message: error.message
        };
        
        console.log(`❌ ${test_name} (${duration.toFixed(2)}ms): ${error.message}`);
        this.test_results.push(result);
        return result;
      }
    }));
    
    const passed_tests = this.test_results.filter(r => r.passed).length;
    const total_tests = this.test_results.length;
    
    console.log('\n📊 Test Suite Results');
    console.log('=====================');
    console.log(`✅ Passed: ${passed_tests}/${total_tests}`);
    console.log(`❌ Failed: ${total_tests - passed_tests}/${total_tests}`);
    console.log(`⏱️  Total time: ${this.test_results.reduce((sum, r) => sum + r.duration, 0).toFixed(2)}ms`);
    
    return {
      total_tests,
      passed_tests,
      failed_tests: total_tests - passed_tests,
      success_rate: passed_tests / total_tests,
      results: this.test_results
    };
  }
  
  /**
   * Test basic compilation functionality
   */
  private async testBasicCompilation(): Promise<void> {
    const result = await this.compiler.compileCanvas(testCanvas);
    
    if (!result.success) {
      throw new Error('Basic compilation failed');
    }
    
    if (!result.canvas) {
      throw new Error('Canvas parsing failed');
    }
    
    if (!result.ast) {
      throw new Error('AST generation failed');
    }
    
    if (!result.aal_program) {
      throw new Error('AAL program generation failed');
    }
    
    if (!result.generated_code) {
      throw new Error('Code generation failed');
    }
    
    // Verify basic structure
    if (result.canvas.metadata.total_nodes !== 8) {
      throw new Error(`Expected 8 nodes, got ${result.canvas.metadata.total_nodes}`);
    }
    
    if (result.canvas.metadata.total_edges !== 7) {
      throw new Error(`Expected 7 edges, got ${result.canvas.metadata.total_edges}`);
    }
    
    if (result.generated_code.metadata.instruction_count === 0) {
      throw new Error('No instructions generated');
    }
  }
  
  /**
   * Test parser functionality
   */
  private async testParserFunctionality(): Promise<void> {
    const result = await this.compiler.compileCanvas(testCanvas);
    
    if (!result.canvas) {
      throw new Error('Canvas parsing failed');
    }
    
    // Test observer node detection
    if (!result.canvas.observer) {
      throw new Error('Observer node not detected');
    }
    
    if (result.canvas.observer.id !== 'observer') {
      throw new Error(`Expected observer node ID 'observer', got '${result.canvas.observer.id}'`);
    }
    
    // Test node classification
    const activate_node = result.canvas.nodes.find(n => n.id === 'activate1');
    if (!activate_node || activate_node.classification !== 'activate') {
      throw new Error('Activate node not properly classified');
    }
    
    const integrate_node = result.canvas.nodes.find(n => n.id === 'integrate1');
    if (!integrate_node || integrate_node.classification !== 'integrate') {
      throw new Error('Integrate node not properly classified');
    }
    
    // Test polynomial encoding
    result.canvas.nodes.forEach(node => {
      if (node.polynomial.length === 0) {
        throw new Error(`Node ${node.id} has empty polynomial`);
      }
    });
  }
  
  /**
   * Test AST generation
   */
  private async testASTGeneration(): Promise<void> {
    const result = await this.compiler.compileCanvas(testCanvas);
    
    if (!result.ast) {
      throw new Error('AST generation failed');
    }
    
    // Test AST structure
    if (result.ast.nodes.length === 0) {
      throw new Error('AST has no nodes');
    }
    
    if (result.ast.functions.length === 0) {
      throw new Error('AST has no functions');
    }
    
    if (result.ast.metadata.contains_cycles) {
      throw new Error('AST should not contain cycles');
    }
    
    // Test entry points
    if (result.ast.entry_points.length === 0) {
      throw new Error('AST has no entry points');
    }
    
    // Test dimensional analysis
    if (result.ast.metadata.dimensions_used.length === 0) {
      throw new Error('AST has no dimensions used');
    }
  }
  
  /**
   * Test AAL code generation
   */
  private async testAALCodeGeneration(): Promise<void> {
    const result = await this.compiler.compileCanvas(testCanvas);
    
    if (!result.generated_code) {
      throw new Error('Code generation failed');
    }
    
    // Test assembly code
    if (!result.generated_code.assembly_code || result.generated_code.assembly_code.length === 0) {
      throw new Error('No assembly code generated');
    }
    
    // Test bytecode
    if (!result.generated_code.bytecode || result.generated_code.bytecode.length === 0) {
      throw new Error('No bytecode generated');
    }
    
    // Test instruction count
    if (result.generated_code.metadata.instruction_count === 0) {
      throw new Error('No instructions in generated code');
    }
    
    // Test metadata
    if (result.generated_code.metadata.byte_size === 0) {
      throw new Error('Invalid byte size in metadata');
    }
    
    // Test proofs
    if (result.generated_code.proofs.length === 0) {
      throw new Error('No proofs generated');
    }
  }
  
  /**
   * Test mathematical verification
   */
  private async testMathematicalVerification(): Promise<void> {
    const result = await this.compiler.compileCanvas(testCanvas);
    
    if (!result.verification) {
      throw new Error('No verification result');
    }
    
    // Test verification status
    if (result.verification.overall_status === 'failed') {
      throw new Error('Mathematical verification failed');
    }
    
    // Test AAL type safety
    if (!result.verification.aal_type_safety) {
      throw new Error('AAL type safety verification failed');
    }
    
    // Test Hopf compatibility
    if (!result.verification.hopf_compatible) {
      console.warn('Hopf compatibility warning (expected for test)');
    }
  }
  
  /**
   * Test optimization levels
   */
  private async testOptimizationLevels(): Promise<void> {
    const optimization_levels: (0 | 1 | 2 | 3)[] = [0, 1, 2, 3];
    
    for (const level of optimization_levels) {
      const compiler = createCanvasLCompiler({ optimization_level: level });
      const result = await compiler.compileCanvas(testCanvas);
      
      if (!result.success) {
        throw new Error(`Compilation failed at optimization level ${level}`);
      }
      
      if (!result.generated_code) {
        throw new Error(`No code generated at optimization level ${level}`);
      }
      
      // Higher optimization levels should produce better results
      const has_optimizations = result.generated_code.metadata.optimization_applied.length > 0;
      if (level >= 2 && !has_optimizations) {
        console.warn(`Expected optimizations at level ${level}`);
      }
    }
  }
  
  /**
   * Test error handling
   */
  private async testErrorHandling(): Promise<void> {
    // Test invalid canvas
    const invalid_canvas = {
      nodes: [],
      edges: []
    } as CanvasJSON;
    
    const result = await this.compiler.compileCanvas(invalid_canvas);
    
    if (!result.success) {
      // Expected to fail, but should handle gracefully
      if (result.errors.length === 0) {
        throw new Error('Expected errors for invalid canvas');
      }
    } else {
      // If it succeeds, should have warnings
      if (result.warnings.length === 0) {
        console.warn('Expected warnings for empty canvas');
      }
    }
  }
  
  /**
   * Test complex canvas
   */
  private async testComplexCanvas(): Promise<void> {
    // Create a more complex canvas for stress testing
    const complex_canvas: CanvasJSON = {
      nodes: [
        // Observer
        {
          id: 'observer',
          type: 'text',
          x: 0, y: 0, width: 100, height: 50,
          text: '#Observe: Complex test'
        },
        // Main computation nodes
        ...Array.from({ length: 20 }, (_, i) => ({
          id: `node${i}`,
          type: 'text',
          x: (i + 1) * 50,
          y: Math.floor(i / 5) * 60,
          width: 100,
          height: 50,
          text: `#Node${i}: computation ${i}`
        }))
      ],
      edges: Array.from({ length: 19 }, (_, i) => ({
        id: `edge${i}`,
        fromNode: `node${i}`,
        toNode: `node${i + 1}`,
        label: `data flow ${i}`
      }))
    };
    
    const result = await this.compiler.compileCanvas(complex_canvas);
    
    if (!result.success) {
      throw new Error('Complex canvas compilation failed');
    }
    
    if (!result.generated_code) {
      throw new Error('No code generated for complex canvas');
    }
    
    // Should generate more instructions for larger canvas
    if (result.generated_code.metadata.instruction_count < 10) {
      throw new Error('Expected more instructions for complex canvas');
    }
    
    // Should have higher complexity score
    if (result.metrics.complexity_score < 100) {
      console.warn('Complex canvas should have higher complexity score');
    }
  }
  
  /**
   * Helper to get test name
   */
  private getTestName(test: Function, index: number): string {
    return test.name || `Test ${index + 1}`;
  }
}

/**
 * Test result interfaces
 */
export interface TestResult {
  name: string;
  passed: boolean;
  duration: number;
  message: string;
}

export interface TestSuiteResult {
  total_tests: number;
  passed_tests: number;
  failed_tests: number;
  success_rate: number;
  results: TestResult[];
}

/**
 * Run tests if this file is executed directly
 */
export async function runCanvasLCompilerTests(): Promise<TestSuiteResult> {
  const test_suite = new CanvasLCompilerTestSuite();
  return await test_suite.runAllTests();
}

// Export for use in other modules
export { testCanvas, CanvasLCompilerTestSuite };