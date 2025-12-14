// Core type definitions for the LOGOS System

export interface ProofHash {
  hash: string;
  theorem_reference: string;
  security_level: 'safe' | 'degraded' | 'compromised';
}

export interface CommitProof {
  instruction: {
    opcode: string;
    operands: any[];
    polynomial?: boolean[];
    verification: {
      theorem_reference: string;
      security_level: 'safe' | 'degraded' | 'compromised';
    };
  };
  polynomial?: boolean[];
  verification: {
    theorem_reference: string;
    security_level: 'safe' | 'degraded' | 'compromised';
  };
}

export interface SovereignIdentity {
  did: string;
  cubic_keypair: {
    private_cubic: { coeffs: Map<string, any> };
    public_cubic: { coeffs: Map<string, any> };
    tensor_seed?: number;
  };
  multiverse_keys: {
    sedenion_public: { components: number[] };
    trigintaduonion_private: { components: number[] };
  };
  claims: Map<string, any>;
  created_at: number;
  updated_at: number;
}

export interface DNAManifestEntry {
  '@canvasl': 'manifest';
  version: string;
  organism: string;
  created_at: number;
  timestamp: number;
}

export interface DNAGenerationEntry {
  '@canvasl': 'generation';
  version: string;
  generation: number;
  polynomial: boolean[];
  hash_chain: string;
  commit_id: string;
  parent_ids: string[];
  author_cubic_key: any;
  aal_proof: ProofHash;
  fitness: number;
  diversity: number;
  mutation_rate: number;
  timestamp: number;
}

export interface DNABranchEntry {
  '@canvasl': 'branch';
  version: string;
  branch_name: string;
  sedenion_address: any;
  owner_key: any;
  from_commit_id: string;
  timestamp: number;
}

export interface DNAMergeEntry {
  '@canvasl': 'merge';
  version: string;
  generation: number;
  polynomial: boolean[];
  parent_ids: string[];
  merge_strategy: any;
  merge_proof: ProofHash;
  author_cubic_key: any;
  aal_proof: ProofHash;
  timestamp: number;
}

export interface DNAIdentityEntry {
  '@canvasl': 'identity';
  version: string;
  operation: 'create' | 'update' | 'revoke';
  did: string;
  cubic_public_key: any;
  sedenion_address: any;
  claims: Map<string, any>;
  timestamp: number;
}

export interface IdentityCommitMetadata {
  mergeType?: string;
  mergePolicy?: any;
}

export type IdentityBranch = string;

export interface VerificationConstraints {
  requiredClaims?: string[];
  [key: string]: any;
}

export interface VerifiableCredential {
  id?: string;
  [key: string]: any;
}

export interface TokenType {
  type: string;
}

export interface BudgetMetadata {
  department?: string;
  project?: string;
  costCenter?: string;
  manager?: string;
  reviewers: string[];
  tags: string[];
  notes: string;
}

export interface Attachment {
  [key: string]: any;
}

// Re-export types from other modules
export * from './core/polynomial/polynomial';
export * from './core/aal/types';
export * from './core/cryptography/cubic-signature';
export * from './core/cryptography/production-crypto';