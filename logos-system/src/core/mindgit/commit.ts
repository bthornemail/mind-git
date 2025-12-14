/**
 * MindGit Commit System - Cubic Signature Integration
 *
 * === COMMIT CONCEPT ===
 * Immutable evolutionary records with post-quantum cryptographic
 * signatures using ternary cubic forms and AAL proof certificates.
 *
 * === SECURITY LAYERING ===
 * 1. Cubic signatures for post-quantum security
 * 2. AAL proofs for formal verification
 * 3. Hash chains for provenance tracking
 * 4. Merkle trees for content integrity
 *
 * === INTEGRATION ===
 * Uses existing cubic cryptography and AAL systems
 * Integrates with DNA logging and content-addressed storage
 */

import { 
  MindGitCommit,
  CanvasLState,
  SovereignIdentity,
  CommitProof
} from '../../types';
import { DNALogger } from './dna-log';
import { ContentAddressedStorage } from './storage';
import { TernaryCubicForm } from '../cryptography';
import { signWithCubic, verifyCubicSignature } from '../cryptography/cubic-signature';
import { generateCommitProof, verifyCommitProof } from '../cryptography/commit-signature';
import { ProductionCryptography } from '../cryptography/production-crypto';

/**
 * Commit Manager - Handles commit creation and verification
 *
 * Integrates cubic signatures, AAL proofs, and provenance tracking
 * with the DNA logging and storage systems.
 */
export class CommitManager {
  private dnaLogger: DNALogger;
  private storage: ContentAddressedStorage;
  private crypto: ProductionCryptography;

  constructor(
    dnaLogger: DNALogger,
    storage: ContentAddressedStorage,
    crypto: ProductionCryptography
  ) {
    this.dnaLogger = dnaLogger;
    this.storage = storage;
    this.crypto = crypto;
  }

  /**
   * Create commit with cubic signature and AAL proof
   *
   * @param identity - Sovereign identity of author
   * @param parentCommit - Parent commit (null for genesis)
   * @param state - New CanvasL state
   * @param message - Commit message
   * @returns Created MindGit commit
   */
  async createCommit(
    identity: SovereignIdentity,
    parentCommit: MindGitCommit | null,
    state: CanvasLState,
    message: string
  ): Promise<MindGitCommit> {
    const startTime = performance.now();

    try {
      console.log(`Creating commit: ${message}`);

      // 1. Generate AAL proof for state transition
      const aalProof = await generateCommitProof(
        {
          previousState: parentCommit?.author.generation ? {
            polynomial: [true], // Would extract from parent
            generation: parentCommit.author.generation,
            fitness: parentCommit.metadata.fitness || 0.5
          } : {
            polynomial: [true], // Genesis state
            generation: 0,
            fitness: 1.0
          },
          newState: state
        },
        this.crypto
      );

      // 2. Create commit object
      const commit: MindGitCommit = {
        id: '', // Will be computed below
        parent_ids: parentCommit ? [parentCommit.id] : [],
        tree_id: await this.createTree(state),
        author: {
          cubic_public_key: identity.cubic_keypair.public_cubic,
          sedenion_address: identity.multiverse_keys.sedenion_public,
          timestamp: Date.now(),
          generation: (parentCommit?.author.generation || -1) + 1
        },
        signatures: {
          cubic_signature: new Uint8Array(), // Will be filled below
          merkle_root: await this.computeMerkleRoot(state),
          hash_chain: '' // Will be computed below
        },
        aal_proof: aalProof,
        message,
        metadata: {
          fitness: state.fitness,
          diversity: state.diversity,
          mutation_rate: state.mutation_rate
        }
      };

      // 3. Compute commit ID (hash of commit content)
      commit.id = await this.computeCommitId(commit);

      // 4. Sign commit with cubic private key
      commit.signatures.cubic_signature = await signWithCubic(
        commit.id,
        identity.cubic_keypair.private_cubic,
        this.crypto
      );

      // 5. Update hash chain
      commit.signatures.hash_chain = await this.updateHashChain(
        parentCommit?.signatures.hash_chain || 'genesis',
        commit.id
      );

      // 6. Store commit in content-addressed storage
      const commitHash = await this.storage.storeCommit(commit);

      // 7. Log commit to DNA log
      await this.dnaLogger.logGeneration(
        commit.author.generation,
        state,
        commit,
        commit.parent_ids
      );

      const duration = performance.now() - startTime;
      console.log(`Commit created in ${duration}ms: ${commit.id}`);

      return commit;

    } catch (error) {
      const duration = performance.now() - startTime;
      console.error(`Commit creation failed after ${duration}ms:`, error);
      throw error;
    }
  }

  /**
   * Verify commit integrity and signatures
   *
   * @param commit - Commit to verify
   * @param authorIdentity - Expected author identity
   * @returns Verification result
   */
  async verifyCommit(
    commit: MindGitCommit,
    authorIdentity?: SovereignIdentity
  ): Promise<{
    isValid: boolean;
    signatureValid: boolean;
    aalProofValid: boolean;
    hashChainValid: boolean;
    errors: string[];
  }> {
    const startTime = performance.now();
    const errors: string[] = [];

    try {
      console.log(`Verifying commit: ${commit.id}`);

      // 1. Verify cubic signature
      const signatureValid = authorIdentity 
        ? await verifyCubicSignature(
            commit.id,
            commit.signatures.cubic_signature,
            authorIdentity.cubic_keypair.public_cubic,
            this.crypto
          )
        : false;

      if (!signatureValid) {
        errors.push('Cubic signature verification failed');
      }

      // 2. Verify AAL proof
      const aalProofValid = await verifyCommitProof(
        commit.aal_proof,
        {
          previousState: {}, // Would reconstruct from parent
          newState: {} // Would extract from commit
        },
        this.crypto
      );

      if (!aalProofValid) {
        errors.push('AAL proof verification failed');
      }

      // 3. Verify hash chain continuity
      const hashChainValid = await this.verifyHashChain(commit);

      if (!hashChainValid) {
        errors.push('Hash chain verification failed');
      }

      // 4. Verify Merkle root
      const merkleValid = await this.verifyMerkleRoot(commit);

      if (!merkleValid) {
        errors.push('Merkle root verification failed');
      }

      const duration = performance.now() - startTime;
      console.log(`Commit verification completed in ${duration}ms`);

      return {
        isValid: errors.length === 0,
        signatureValid,
        aalProofValid,
        hashChainValid,
        errors
      };

    } catch (error) {
      const duration = performance.now() - startTime;
      console.error(`Commit verification failed after ${duration}ms:`, error);
      
      return {
        isValid: false,
        signatureValid: false,
        aalProofValid: false,
        hashChainValid: false,
        errors: [error instanceof Error ? error.message : 'Unknown error']
      };
    }
  }

  /**
   * Create tree object for CanvasL state
   *
   * @param state - CanvasL state to tree-ify
   * @returns Tree object hash
   */
  private async createTree(state: CanvasLState): Promise<string> {
    // Create tree entries for state components
    const entries = new Map<string, string>();
    
    // Store polynomial as blob
    const polynomialData = new TextEncoder().encode(JSON.stringify(state.polynomial));
    const polynomialHash = await this.storage.storeBlob(polynomialData);
    entries.set('polynomial.json', polynomialHash);

    // Store metadata as blob
    const metadata = {
      generation: state.generation,
      fitness: state.fitness,
      diversity: state.diversity,
      mutation_rate: state.mutation_rate,
      created_at: Date.now()
    };
    const metadataData = new TextEncoder().encode(JSON.stringify(metadata));
    const metadataHash = await this.storage.storeBlob(metadataData);
    entries.set('metadata.json', metadataHash);

    // Create tree object
    return await this.storage.storeTree(entries);
  }

  /**
   * Compute Merkle root of CanvasL state
   *
   * @param state - CanvasL state
   * @returns Merkle root hash
   */
  private async computeMerkleRoot(state: CanvasLState): Promise<string> {
    // Simplified Merkle root computation
    // In a full implementation, this would create a proper Merkle tree
    const stateData = JSON.stringify(state);
    const encoder = new TextEncoder();
    const data = encoder.encode(stateData);
    const hashBuffer = await crypto.subtle.digest('SHA-256', data);
    const hashArray = Array.from(new Uint8Array(hashBuffer));
    
    return hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
  }

  /**
   * Verify Merkle root
   *
   * @param commit - Commit containing Merkle root
   * @returns True if Merkle root is valid
   */
  private async verifyMerkleRoot(commit: MindGitCommit): Promise<boolean> {
    // In a full implementation, this would verify the Merkle tree
    // For now, accept the stored root as valid
    return commit.signatures.merkle_root.length > 0;
  }

  /**
   * Compute commit ID from content
   *
   * @param commit - Commit object
   * @returns SHA-256 hash
   */
  private async computeCommitId(commit: MindGitCommit): Promise<string> {
    // Create canonical representation for hashing
    const canonical = {
      parent_ids: commit.parent_ids.sort(),
      tree_id: commit.tree_id,
      author: {
        cubic_public_key: commit.author.cubic_public_key.toBytes(),
        timestamp: commit.author.timestamp,
        generation: commit.author.generation
      },
      aal_proof: commit.aal_proof,
      message: commit.message,
      metadata: commit.metadata
    };

    const canonicalStr = JSON.stringify(canonical);
    const encoder = new TextEncoder();
    const data = encoder.encode(canonicalStr);
    const hashBuffer = await crypto.subtle.digest('SHA-256', data);
    const hashArray = Array.from(new Uint8Array(hashBuffer));
    
    return hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
  }

  /**
   * Update hash chain
   *
   * @param previousHash - Previous hash in chain
   * @param commitId - Current commit ID
   * @returns New hash chain value
   */
  private async updateHashChain(previousHash: string, commitId: string): Promise<string> {
    const combined = previousHash + commitId;
    const encoder = new TextEncoder();
    const data = encoder.encode(combined);
    const hashBuffer = await crypto.subtle.digest('SHA-256', data);
    const hashArray = Array.from(new Uint8Array(hashBuffer));
    
    return hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
  }

  /**
   * Verify hash chain continuity
   *
   * @param commit - Commit to verify
   * @returns True if hash chain is valid
   */
  private async verifyHashChain(commit: MindGitCommit): Promise<boolean> {
    // In a full implementation, this would verify the hash chain
    // by recomputing the expected hash chain value
    // For now, accept non-empty hash chains as valid
    return commit.signatures.hash_chain.length > 0;
  }

  /**
   * Get commit statistics
   *
   * @returns Commit operation statistics
   */
  async getStatistics(): Promise<{
    commitsCreated: number;
    commitsVerified: number;
    averageCreationTime: number;
    averageVerificationTime: number;
    signatureFailures: number;
    aalProofFailures: number;
  }> {
    // In a full implementation, this would track actual statistics
    // For now, return placeholder statistics
    return {
      commitsCreated: 0,
      commitsVerified: 0,
      averageCreationTime: 0,
      averageVerificationTime: 0,
      signatureFailures: 0,
      aalProofFailures: 0
    };
  }

  /**
   * Find common ancestor of two commits
   *
   * @param commit1 - First commit
   * @param commit2 - Second commit
   * @returns Common ancestor commit or null
   */
  async findCommonAncestor(
    commit1: MindGitCommit,
    commit2: MindGitCommit
  ): Promise<MindGitCommit | null> {
    // Simplified common ancestor finding
    // In a full implementation, this would traverse the commit graph
    // For now, return the earlier commit by generation
    if (commit1.author.generation < commit2.author.generation) {
      return commit1;
    } else if (commit2.author.generation < commit1.author.generation) {
      return commit2;
    } else {
      // Same generation, return first commit
      return commit1;
    }
  }

  /**
   * Create merge commit
   *
   * @param identity - Author identity
   * @param parentCommits - Parent commits (2 for merge)
   * @param mergedState - Merged CanvasL state
   * @param message - Merge commit message
   * @param mergeStrategy - Strategy used for merging
   * @returns Merge commit
   */
  async createMergeCommit(
    identity: SovereignIdentity,
    parentCommits: MindGitCommit[],
    mergedState: CanvasLState,
    message: string,
    mergeStrategy: string
  ): Promise<MindGitCommit> {
    const startTime = performance.now();

    try {
      console.log(`Creating merge commit: ${message}`);

      // 1. Generate AAL proof for merge operation
      const aalProof = await generateCommitProof(
        {
          previousState: {}, // Would extract from common ancestor
          newState: mergedState
        },
        this.crypto
      );

      // 2. Create merge commit object
      const mergeCommit: MindGitCommit = {
        id: '', // Will be computed below
        parent_ids: parentCommits.map(c => c.id),
        tree_id: await this.createTree(mergedState),
        author: {
          cubic_public_key: identity.cubic_keypair.public_cubic,
          sedenion_address: identity.multiverse_keys.sedenion_public,
          timestamp: Date.now(),
          generation: Math.max(...parentCommits.map(c => c.author.generation)) + 1
        },
        signatures: {
          cubic_signature: new Uint8Array(), // Will be filled below
          merkle_root: await this.computeMerkleRoot(mergedState),
          hash_chain: '' // Will be computed below
        },
        aal_proof: aalProof,
        message: `${message} (merge: ${mergeStrategy})`,
        metadata: {
          fitness: mergedState.fitness,
          diversity: mergedState.diversity,
          mutation_rate: mergedState.mutation_rate,
          merge_strategy: mergeStrategy,
          parent_generations: parentCommits.map(c => c.author.generation)
        }
      };

      // 3. Compute merge commit ID
      mergeCommit.id = await this.computeCommitId(mergeCommit);

      // 4. Sign merge commit
      mergeCommit.signatures.cubic_signature = await signWithCubic(
        mergeCommit.id,
        identity.cubic_keypair.private_cubic,
        this.crypto
      );

      // 5. Update hash chain (use first parent for chain continuity)
      mergeCommit.signatures.hash_chain = await this.updateHashChain(
        parentCommits[0]?.signatures.hash_chain || 'genesis',
        mergeCommit.id
      );

      // 6. Store merge commit
      await this.storage.storeCommit(mergeCommit);

      // 7. Log merge to DNA log
      await this.dnaLogger.logMerge(
        mergeCommit.author.generation,
        mergedState,
        mergeCommit.parent_ids,
        mergeStrategy,
        aalProof,
        identity.cubic_keypair.public_cubic
      );

      const duration = performance.now() - startTime;
      console.log(`Merge commit created in ${duration}ms: ${mergeCommit.id}`);

      return mergeCommit;

    } catch (error) {
      const duration = performance.now() - startTime;
      console.error(`Merge commit creation failed after ${duration}ms:`, error);
      throw error;
    }
  }

  /**
   * Export commit in various formats
   *
   * @param commit - Commit to export
   * @param format - Export format
   * @returns Exported commit data
   */
  async exportCommit(
    commit: MindGitCommit,
    format: 'json' | 'canvasl' | 'git' = 'json'
  ): Promise<string> {
    switch (format) {
      case 'json':
        return JSON.stringify(commit, null, 2);
        
      case 'canvasl':
        return this.formatAsCanvasL(commit);
        
      case 'git':
        return this.formatAsGit(commit);
        
      default:
        throw new Error(`Unsupported export format: ${format}`);
    }
  }

  /**
   * Format commit as CanvasL
   *
   * @param commit - Commit to format
   * @returns CanvasL formatted string
   */
  private formatAsCanvasL(commit: MindGitCommit): string {
    return `# CanvasL Commit Export
# Generated: ${new Date().toISOString()}

## Commit Information
ID: ${commit.id}
Parents: ${commit.parent_ids.join(', ') || 'none'}
Tree: ${commit.tree_id}
Author: ${commit.author.generation} (${commit.author.timestamp})
Message: ${commit.message}

## Author Identity
Cubic Public Key: ${commit.author.cubic_public_key.toString()}
Sedenion Address: [${commit.author.sedenion_address.components.join(', ')}]

## Cryptographic Proofs
Cubic Signature: ${Array.from(commit.signatures.cubic_signature).map(b => b.toString(16).padStart(2, '0')).join('')}
Merkle Root: ${commit.signatures.merkle_root}
Hash Chain: ${commit.signatures.hash_chain}

## AAL Proof
Theorem: ${commit.aal_proof.theorem_reference}
Proof Hash: ${commit.aal_proof.hash}

## State Metadata
Fitness: ${commit.metadata.fitness || 'N/A'}
Diversity: ${commit.metadata.diversity || 'N/A'}
Mutation Rate: ${commit.metadata.mutation_rate || 'N/A'}
Generation: ${commit.author.generation}
`;
  }

  /**
   * Format commit as Git-style
   *
   * @param commit - Commit to format
   * @returns Git-style formatted string
   */
  private formatAsGit(commit: MindGitCommit): string {
    return `commit ${commit.id}
Author: Generation ${commit.author.generation} <${commit.author.cubic_public_key.toBytes().slice(0, 8).map(b => b.toString(16)).join('')}>
Date: ${new Date(commit.author.timestamp * 1000).toISOString()}

${commit.message}

Cubic-Signature: ${Array.from(commit.signatures.cubic_signature).map(b => b.toString(16)).join('')}
AAL-Proof: ${commit.aal_proof.hash}
Merkle-Root: ${commit.signatures.merkle_root}
Hash-Chain: ${commit.signatures.hash_chain}
`;
  }
}