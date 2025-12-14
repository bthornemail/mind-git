/**
 * MindGit Core Types and Interfaces
 *
 * === MINDGIT CONCEPT ===
 * Git-like version control for "computational organisms" evolving in CanvasL
 * 
 * === CORE PRINCIPLES ===
 * - DNA Logging: Append-only JSONL logs recording every evolutionary generation
 * - Cryptographic Provenance: Hash chains, Merkle trees, cubic signatures
 * - Polynomial Merge Resolution: GCD-based conflict resolution using F₂ algebra
 * - Deterministic Replay: Perfect state reconstruction from genesis
 * - Sovereign Identity: Polynomial-based identity with cubic keypair authentication
 * - Multiverse Branching: Sedenion (16D) public addresses, trigintaduonion (32D) private ownership
 */

import { TernaryCubicForm } from '../cryptography';
import { Sedenion, Trigintaduonion } from '../multiverse';
import { ProofHash } from '../aal';

/**
 * CanvasL State - The computational organism state
 *
 * Represents the complete state of a CanvasL computational organism
 * at a specific generation in its evolutionary timeline.
 */
export interface CanvasLState {
  /** Polynomial representation over F₂ */
  polynomial: boolean[];
  
  /** Evolutionary generation number */
  generation: number;
  
  /** Fitness score for evolutionary selection */
  fitness: number;
  
  /** Diversity measure for population health */
  diversity?: number;
  
  /** Mutation rate for evolutionary dynamics */
  mutation_rate?: number;
  
  /** Additional metadata */
  metadata?: Record<string, any>;
}

/**
 * MindGit Commit - Immutable evolutionary record
 *
 * Each commit represents one evolutionary step with full cryptographic
 * provenance and formal verification.
 */
export interface MindGitCommit {
  /** SHA-256 hash of commit content */
  id: string;
  
  /** Parent commit IDs (1 for normal, 2+ for merges) */
  parent_ids: string[];
  
  /** Content-addressed tree ID */
  tree_id: string;
  
  /** Author information with cryptographic identity */
  author: {
    /** Post-quantum cubic public key (40 bytes) */
    cubic_public_key: TernaryCubicForm;
    
    /** 16D universe address for multiverse branching */
    sedenion_address: Sedenion;
    
    /** Unix timestamp of commit */
    timestamp: number;
    
    /** Evolutionary generation index */
    generation: number;
  };
  
  /** Cryptographic signatures and proofs */
  signatures: {
    /** Post-quantum cubic signature */
    cubic_signature: Uint8Array;
    
    /** Merkle root of tree content */
    merkle_root: string;
    
    /** Hash chain: H_n = SHA256(H_{n-1} + JSON_n) */
    hash_chain: string;
  };
  
  /** Formal AAL proof certificate */
  aal_proof: ProofHash;
  
  /** Human-readable commit message */
  message: string;
  
  /** Evolutionary metadata */
  metadata: {
    fitness?: number;
    diversity?: number;
    mutation_rate?: number;
  };
}

/**
 * MindGit Branch - Multiverse branch with sovereign ownership
 *
 * Each branch exists in its own universe with 16D public addressing
 * and 32D private ownership keys.
 */
export interface MindGitBranch {
  /** Human-readable branch name (e.g., "main") */
  name: string;
  
  /** 16D public universe address */
  sedenion_address: Sedenion;
  
  /** 32D private ownership key */
  owner_key: Trigintaduonion;
  
  /** Current head commit ID */
  head_commit_id: string;
  
  /** Optional upstream remote configuration */
  upstream?: {
    remote_name: string;
    remote_sedenion: Sedenion;
  };
  
  /** Branch creation timestamp */
  created_at: number;
  
  /** Last update timestamp */
  last_updated: number;
}

/**
 * MindGit Repository - Complete repository state
 *
 * Contains all branches, commits, and evolutionary history for a computational organism.
 */
export interface MindGitRepository {
  /** Repository name (organism name) */
  name: string;
  
  /** Repository configuration */
  config: {
    /** MindGit version */
    version: string;
    
    /** Default merge strategy */
    default_merge_strategy: MergeStrategy;
    
    /** Repository metadata */
    metadata: Record<string, any>;
  };
  
  /** Current branch (HEAD pointer) */
  head_branch: string;
  
  /** All branches by name */
  branches: Map<string, MindGitBranch>;
  
  /** All commits by ID */
  commits: Map<string, MindGitCommit>;
  
  /** DNA log file path */
  dna_log_path: string;
  
  /** Repository creation timestamp */
  created_at: number;
}

/**
 * Sovereign Identity - Complete cryptographic identity
 *
 * Combines cubic cryptography with multiverse addressing for
 * post-quantum sovereign identity management.
 */
export interface SovereignIdentity {
  /** Decentralized identifier */
  did: string;
  
  /** Cubic cryptographic keypair */
  cubic_keypair: {
    private_cubic: TernaryCubicForm;
    public_cubic: TernaryCubicForm;
    tensor_seed: number;
  };
  
  /** Multiverse addressing keys */
  multiverse_keys: {
    /** 16D public sedenion address */
    sedenion_public: Sedenion;
    
    /** 32D private trigintaduonion key */
    trigintaduonion_private: Trigintaduonion;
  };
  
  /** Identity claims and attestations */
  claims: Map<string, any>;
  
  /** Identity creation timestamp */
  created_at: number;
  
  /** Last updated timestamp */
  updated_at: number;
}

/**
 * Merge Strategy Types
 *
 * Different strategies for resolving conflicts between evolutionary branches.
 */
export type MergeStrategy =
  /** GCD of conflicting polynomials (default) */
  | 'polynomial_gcd'
  
  /** Weight by fitness scores */
  | 'fitness_weighted'
  
  /** Fano plane projection (D9 verification) */
  | 'geometric_fano'
  
  /** Timestamp-based selection */
  | 'choose_latest'
  
  /** Preserve Pfister 16-square norm */
  | 'norm_preserving'
  
  /** Quantum error correction (v3.0) */
  | 'quantum_stabilizer';

/**
 * DNA Log Entry Types
 *
 * Different types of entries in the JSONL DNA log.
 */
export type DNAEntryType = 
  /** Repository manifest */
  | 'manifest'
  
  /** Evolutionary generation */
  | 'generation'
  
  /** Branch creation */
  | 'branch'
  
  /** Merge operation */
  | 'merge'
  
  /** Identity operation */
  | 'identity';

/**
 * DNA Log Entry - Base interface for all log entries
 *
 * All DNA log entries share common structure for type safety
 * and evolutionary tracking.
 */
export interface DNAEntry {
  /** Entry type discriminator */
  '@canvasl': DNAEntryType;
  
  /** Entry version for compatibility */
  version: string;
  
  /** Unix timestamp */
  timestamp: number;
}

/**
 * DNA Manifest Entry
 *
 * First entry in any DNA log, establishes repository metadata.
 */
export interface DNAManifestEntry extends DNAEntry {
  '@canvasl': 'manifest';
  version: string;
  organism: string;
  created_at: number;
}

/**
 * DNA Generation Entry
 *
 * Records one evolutionary generation with full state and provenance.
 */
export interface DNAGenerationEntry extends DNAEntry {
  '@canvasl': 'generation';
  generation: number;
  polynomial: boolean[];
  hash_chain: string;
  commit_id: string;
  parent_ids?: string[];
  author_cubic_key: TernaryCubicForm;
  aal_proof: ProofHash;
  fitness?: number;
  diversity?: number;
  mutation_rate?: number;
}

/**
 * DNA Branch Entry
 *
 * Records branch creation with multiverse addressing.
 */
export interface DNABranchEntry extends DNAEntry {
  '@canvasl': 'branch';
  branch_name: string;
  sedenion_address: Sedenion;
  owner_key: Trigintaduonion;
  from_commit_id?: string;
}

/**
 * DNA Merge Entry
 *
 * Records merge operations with strategy and resolution.
 */
export interface DNAMergeEntry extends DNAEntry {
  '@canvasl': 'merge';
  generation: number;
  polynomial: boolean[];
  parent_ids: string[];
  merge_strategy: MergeStrategy;
  merge_proof: ProofHash;
  author_cubic_key: TernaryCubicForm;
  aal_proof: ProofHash;
}

/**
 * DNA Identity Entry
 *
 * Records identity operations and key management.
 */
export interface DNAIdentityEntry extends DNAEntry {
  '@canvasl': 'identity';
  operation: 'create' | 'update' | 'revoke';
  did: string;
  cubic_public_key: TernaryCubicForm;
  sedenion_address: Sedenion;
  claims?: Record<string, any>;
}

/**
 * Content-Addressed Storage Object
 *
 * Base interface for all content-addressed objects.
 */
export interface StorageObject {
  /** SHA-256 hash (content address) */
  hash: string;
  
  /** Object type */
  type: 'blob' | 'tree' | 'commit';
  
  /** Object data */
  data: any;
  
  /** Size in bytes */
  size: number;
  
  /** Creation timestamp */
  created_at: number;
}

/**
 * Tree Object - Directory structure
 *
 * Represents a directory/tree in the content-addressed storage.
 */
export interface TreeObject extends StorageObject {
  type: 'tree';
  data: Map<string, string>; // filename -> hash
}

/**
 * Blob Object - File content
 *
 * Represents file content in the content-addressed storage.
 */
export interface BlobObject extends StorageObject {
  type: 'blob';
  data: Uint8Array;
}

/**
 * Merge Result - Result of merge operation
 *
 * Contains the merged state along with proof and metadata.
 */
export interface MergeResult {
  /** Merged CanvasL state */
  state: CanvasLState;
  
  /** Merge strategy used */
  strategy: MergeStrategy;
  
  /** AAL proof of merge correctness */
  proof: ProofHash;
  
  /** Conflict resolution details */
  conflicts: {
    count: number;
    resolved: number;
    method: string;
  };
  
  /** Merge metadata */
  metadata: {
    duration: number;
    success: boolean;
    security_level: 'safe' | 'degraded' | 'compromised';
  };
}

/**
 * Replay Options - Configuration for state replay
 *
 * Controls how DNA log is replayed to reconstruct state.
 */
export interface ReplayOptions {
  /** Target generation (default: latest) */
  target_generation?: number;
  
  /** Verify AAL proofs during replay */
  verify_proofs?: boolean;
  
  /** Include merge metadata in replay */
  include_metadata?: boolean;
  
  /** Stop on first error */
  strict_mode?: boolean;
}

/**
 * Repository Options - Configuration for repository operations
 *
 * Controls repository creation and management behavior.
 */
export interface RepositoryOptions {
  /** Repository name */
  name: string;
  
  /** Initial state */
  initial_state?: CanvasLState;
  
  /** Default branch name */
  default_branch?: string;
  
  /** Enable DNA logging */
  enable_dna_log?: boolean;
  
  /** Storage backend */
  storage_backend?: 'filesystem' | 'memory' | 'distributed';
  
  /** Repository metadata */
  metadata?: Record<string, any>;
}

/**
 * Export formats for repository data
 */
export type ExportFormat = 
  /** Complete JSON export */
  | 'json'
  
  /** DNA log only */
  | 'jsonl'
  
  /** Compressed archive */
  | 'tar.gz'
  
  /** CanvasL native format */
  | 'canvasl';

/**
 * MindGit Statistics - Repository and system statistics
 *
 * Provides comprehensive analytics for repository health and usage.
 */
export interface MindGitStatistics {
  /** Repository statistics */
  repository: {
    total_commits: number;
    total_branches: number;
    total_generations: number;
    dna_log_size: number;
    storage_usage: number;
  };
  
  /** Evolution statistics */
  evolution: {
    average_fitness: number;
    fitness_trend: 'improving' | 'stable' | 'declining';
    diversity_score: number;
    mutation_rate: number;
  };
  
  /** Security statistics */
  security: {
    verified_commits: number;
    failed_verifications: number;
    cryptographic_health: 'excellent' | 'good' | 'degraded' | 'compromised';
  };
  
  /** Performance statistics */
  performance: {
    average_commit_time: number;
    average_merge_time: number;
    average_replay_time: number;
    storage_operations: number;
  };
}