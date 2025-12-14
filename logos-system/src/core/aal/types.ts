// AAL Types for the Assembly-Algebra Language

export interface AALType {
  type: string;
  dimension: number;
  properties: any[];
}

export interface ProofHash {
  hash: string;
  theorem_reference: string;
  security_level: 'safe' | 'degraded' | 'compromised';
}