/**
 * AAL-Enhanced CanvasL AST Node Schema
 * 
 * Bridges visual programming with formally verified Assembly-Algebra Language
 * Each CanvasL node maps to AAL instruction with polynomial semantics
 */

import type { CanvasJSON, Node, Edge } from '../../json.canvas';
import { AssemblyOp, Dimension, AALInstruction, ProofHash } from '../../core/aal';
import { Polynomial } from '../../core/polynomial';

/**
 * Enhanced Canvas Node with AAL integration
 */
export interface AALEnhancedCanvasNode extends Node {
  // Existing CanvasL fields
  id: string;
  type: string;
  x: number;
  y: number;
  width: number;
  height: number;
  text: string;
  color?: string;
  
  // AAL-specific fields
  aal?: {
    mnemonic: AssemblyOp;           // AAL instruction mnemonic
    grade: Dimension;               // D0-D10 dimension
    polynomial?: Polynomial;         // F₂[x] polynomial encoding
    form?: QuadForm;                // Geometric representation (D9)
    proofHash?: ProofHash;          // Coq verification proof
    operands?: string[];             // Extracted operands
  };
  
  // Mathematical verification
  verification?: {
    coqProof: boolean;              // Formally verified in Coq
    normPreserved: boolean;         // ||a × b|| = ||a|| × ||b||
    geometricValid: boolean;         // Valid Fano conic
    hammingCorrect: boolean;         // Hamming code properties
    typeSafe: boolean;              // Dimensional type safety
  };
  
  // Dynamic classification (from enhanced parser)
  classification?: string;
  dependencies?: string[];
  dependents?: string[];
}

/**
 * Enhanced Canvas Edge with AAL semantics
 */
export interface AALEnhancedCanvasEdge extends Edge {
  // Existing CanvasL fields
  id: string;
  fromNode: string;
  toNode: string;
  fromSide?: string;
  toSide?: string;
  label?: string;
  color?: string;
  
  // AAL-specific fields
  aal?: {
    dataFlow: boolean;             // Data flow edge
    controlFlow: boolean;           // Control flow edge
    dependency: boolean;            // Dependency edge
    feedback: boolean;              // Feedback loop edge
    entanglement: boolean;         // Quantum entanglement edge
    polynomial?: Polynomial;        // Edge polynomial encoding
    weight: number;                // Edge weight for algebraic operations
  };
}

/**
 * Enhanced Canvas JSON with AAL integration
 */
export interface AALEnhancedCanvasJSON extends CanvasJSON {
  nodes: AALEnhancedCanvasNode[];
  edges: AALEnhancedCanvasEdge[];
  
  // AAL metadata
  aal?: {
    version: string;                // AAL version
    verificationLevel: 'none' | 'basic' | 'full' | 'production';
    targetDimensions: Dimension[];   // Target dimensions for compilation
    optimizationLevel: number;       // 0-3 optimization level
    proofStrategy: 'auto' | 'manual' | 'interactive';
  };
  
  // Compilation results
  compilation?: {
    timestamp: number;
    aalInstructions: AALInstruction[];
    verificationResults: VerificationResult;
    generatedCode: CodeGenerationResult;
    diagnostics: Diagnostic[];
  };
}

/**
 * Quadratic Form for D9 geometric representation
 */
export interface QuadForm {
  // Coefficients for ternary quadratic form ax² + by² + cz² + dxy + exz + fyz
  cxx: boolean;   // x² coefficient
  cyy: boolean;   // y² coefficient  
  czz: boolean;   // z² coefficient
  cxy: boolean;   // xy coefficient
  cxz: boolean;   // xz coefficient
  cyz: boolean;   // yz coefficient
  
  // Geometric properties
  nonDegenerate: boolean;    // Non-degenerate conic
  rank: number;              // Matrix rank (1-3)
  determinant: number;       // Determinant over F₂
  fanoPoints: string[];      // Points on Fano plane
}

/**
 * Verification results for AAL compilation
 */
export interface VerificationResult {
  // Core mathematical properties
  normPreservation: {
    verified: boolean;
    violations: string[];
    confidence: number;
  };
  
  // Geometric consistency
  geometricConsistency: {
    verified: boolean;
    fanoPlaneValid: boolean;
    conicType: 'ellipse' | 'hyperbola' | 'parabola' | 'degenerate';
    violations: string[];
  };
  
  // Type safety
  typeSafety: {
    verified: boolean;
    dimensionViolations: DimensionViolation[];
    gradeWeakeningValid: boolean;
  };
  
  // Error correction
  hammingCode: {
    verified: boolean;
    distance: number;
    correctionCapability: number;
    encodedCorrectly: boolean;
  };
  
  // Coq formal verification
  coqProofs: {
    totalTheorems: number;
    provenTheorems: number;
    admittedTheorems: number;
    proofObligations: string[];
  };
}

/**
 * Dimension violation for type safety
 */
export interface DimensionViolation {
  nodeId: string;
  expectedDimension: Dimension;
  actualDimension: Dimension;
  violationType: 'grade_weakening' | 'dimension_mismatch' | 'modal_violation';
  severity: 'error' | 'warning' | 'info';
}

/**
 * Code generation results
 */
export interface CodeGenerationResult {
  javascript: {
    code: string;
    size: number;
    executionTime: number;
    memoryUsage: number;
  };
  
  webassembly: {
    code: ArrayBuffer;
    size: number;
    compilationTime: number;
    verified: boolean;
  };
  
  racket: {
    code: string;
    size: number;
    typeChecked: boolean;
  };
  
  coq: {
    code: string;
    extracted: boolean;
    verified: boolean;
  };
}

/**
 * Compilation diagnostic
 */
export interface Diagnostic {
  id: string;
  nodeId?: string;
  edgeId?: string;
  severity: 'error' | 'warning' | 'info' | 'hint';
  code: string;
  message: string;
  category: 'parsing' | 'typing' | 'verification' | 'generation' | 'optimization';
  suggestions: string[];
  relatedNodes: string[];
}

/**
 * AAL compilation configuration
 */
export interface AALCompilationConfig {
  // Verification settings
  verifyNormPreservation: boolean;
  verifyGeometricConsistency: boolean;
  verifyTypeSafety: boolean;
  verifyHammingCode: boolean;
  
  // Optimization settings
  enableHopfOptimization: boolean;
  enablePolynomialOptimization: boolean;
  enableDimensionalOptimization: boolean;
  optimizationLevel: 0 | 1 | 2 | 3;
  
  // Target settings
  targetLanguages: ('javascript' | 'webassembly' | 'racket' | 'coq')[];
  targetDimensions: Dimension[];
  
  // Proof settings
  generateCoqProofs: boolean;
  proofAutomation: 'none' | 'auto' | 'interactive';
  proofTimeout: number;  // milliseconds
}

/**
 * AAL-CanvasL compilation result
 */
export interface AALCanvasCompilationResult {
  // Input canvas
  canvas: AALEnhancedCanvasJSON;
  
  // Parsed structure
  ast: AALEnhancedCanvasNode[];
  edges: AALEnhancedCanvasEdge[];
  
  // AAL compilation
  aalInstructions: AALInstruction[];
  
  // Verification
  verification: VerificationResult;
  
  // Code generation
  generatedCode: CodeGenerationResult;
  
  // Metadata
  metadata: {
    compilationTime: number;
    nodeCount: number;
    edgeCount: number;
    instructionCount: number;
    maxDimension: Dimension;
    complexity: number;
    hopfCompatible: boolean;
  };
  
  // Diagnostics
  diagnostics: Diagnostic[];
  
  // Success status
  success: boolean;
  errors: string[];
  warnings: string[];
}