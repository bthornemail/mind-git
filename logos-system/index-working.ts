/**
 * Simple working build of LOGOS-SYSTEM core modules
 */

// Core mathematical components
export { PolyF2, type Polynomial } from './src/core/polynomial';
export { IdentityChain, type Vector8D } from './src/core/identity-chain';
export { AAL, type AALInstruction, type Dimension, AssemblyOp } from './src/core/aal';

// Canvas JSON types
export type { CanvasJSON, Node, Edge } from './src/json.canvas';