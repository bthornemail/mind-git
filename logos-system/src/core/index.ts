// Core functionality for mind-git spatial programming system
// Mathematical foundations and computational primitives

export * from './aal';
export * from './cryptography';
export * from './identity-chain';
export * from './mindgit';
export * from './multiverse';
export * from './polynomial';
export * from '../scheme-theory';
export * from '../ai';

// Core version and metadata
export const CORE_VERSION = '1.2.0';
export const MATHEMATICAL_FOUNDATION = 'F₂[x] polynomial algebra';
export const DIMENSIONAL_LIMITS = [1, 2, 4, 8]; // Adams' theorem

// Core capabilities
export const CORE_CAPABILITIES = {
  POLYNOMIAL_ALGEBRA: true,
  IDENTITY_CHAIN: true,
  CRYPTOGRAPHIC_OPERATIONS: true,
  FORMAL_VERIFICATION: true,
  TOPOLOGICAL_ANALYSIS: true,
  SPATIAL_COMPILATION: true
} as const;