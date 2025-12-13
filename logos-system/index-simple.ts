/**
 * Simple build of core LOGOS-SYSTEM components
 */

// Core mathematical components
export { PolyF2, type Polynomial } from './src/core/polynomial';
export { IdentityChain, type Vector8D } from './src/core/identity-chain';
export { AAL, type AALInstruction, type Dimension, AssemblyOp } from './src/core/aal';

// Canvas compiler
export { CanvasLCompiler, type CompilationResult } from './src/compiler';