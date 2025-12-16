// AAL Types for the Assembly-Algebra Language

export interface AALType {
  type: string;
  dimension: number;
  properties: any[];
}

// Re-export from main types to maintain consistency
export { ProofHash } from '../../types';