/**
 * DNA Logging System - Append-Only JSONL Evolutionary Records
 *
 * === DNA LOG CONCEPT ===
 * Append-only JSONL logs recording every evolutionary generation
 * of a CanvasL computational organism with full cryptographic provenance.
 *
 * === IMMUTABILITY PRINCIPLE ===
 * DNA logs are never modified or deleted, only appended.
 * Each entry is cryptographically linked to previous entries.
 *
 * === FORMAT ===
 * JSONL (JSON Lines) - one JSON object per line
 * Each line starts with @canvasl discriminator
 */

import { 
  DNAEntry, 
  DNAEntryType, 
  DNAManifestEntry, 
  DNAGenerationEntry, 
  DNABranchEntry, 
  DNAMergeEntry, 
  DNAIdentityEntry,
  CanvasLState,
  MindGitCommit,
  MindGitBranch,
  SovereignIdentity
} from './types';
import { TernaryCubicForm } from '../cryptography';
import { Sedenion, Trigintaduonion } from '../multiverse';
import { ProofHash } from '../aal';
import { ProductionCryptography } from '../cryptography/production-crypto';

/**
 * DNA Logger - Append-only evolutionary record keeper
 *
 * Manages DNA log files with atomic appends, cryptographic
 * linking, and integrity verification.
 */
export class DNALogger {
  private filePath: string;
  private fileHandle: FileSystemFileHandle | null = null;
  private crypto: ProductionCryptography;
  private writeQueue: string[] = [];
  private isWriting: boolean = false;

  /**
   * Create DNA logger for repository
   *
   * @param filePath - Path to DNA log file (.canvasl)
   * @param crypto - Production cryptography instance
   */
  constructor(filePath: string, crypto: ProductionCryptography) {
    this.filePath = filePath;
    this.crypto = crypto;
  }

  /**
   * Initialize DNA log with manifest entry
   *
   * @param organismName - Name of computational organism
   * @param version - MindGit version
   */
  async initialize(organismName: string, version: string = '3.0'): Promise<void> {
    const manifest: DNAManifestEntry = {
      '@canvasl': 'manifest',
      version,
      organism: organismName,
      created_at: Date.now()
    };

    await this.appendEntry(manifest);
    await this.flush();
  }

  /**
   * Log evolutionary generation
   *
   * @param generation - Generation number
   * @param state - CanvasL state
   * @param commit - MindGit commit with proofs
   * @param parentIds - Parent commit IDs
   */
  async logGeneration(
    generation: number,
    state: CanvasLState,
    commit: MindGitCommit,
    parentIds?: string[]
  ): Promise<void> {
    const entry: DNAGenerationEntry = {
      '@canvasl': 'generation',
      generation,
      polynomial: state.polynomial,
      hash_chain: commit.signatures.hash_chain,
      commit_id: commit.id,
      parent_ids: parentIds || [],
      author_cubic_key: commit.author.cubic_public_key,
      aal_proof: commit.aal_proof,
      fitness: state.fitness,
      diversity: state.diversity,
      mutation_rate: state.mutation_rate
    };

    await this.appendEntry(entry);
  }

  /**
   * Log branch creation
   *
   * @param branch - MindGit branch
   * @param fromCommitId - Optional parent commit
   */
  async logBranch(branch: MindGitBranch, fromCommitId?: string): Promise<void> {
    const entry: DNABranchEntry = {
      '@canvasl': 'branch',
      branch_name: branch.name,
      sedenion_address: branch.sedenion_address,
      owner_key: branch.owner_key,
      from_commit_id: fromCommitId
    };

    await this.appendEntry(entry);
  }

  /**
   * Log merge operation
   *
   * @param generation - Result generation
   * @param state - Merged CanvasL state
   * @param parentIds - Parent commit IDs
   * @param strategy - Merge strategy used
   * @param proof - AAL proof of merge
   * @param authorKey - Author's cubic public key
   */
  async logMerge(
    generation: number,
    state: CanvasLState,
    parentIds: string[],
    strategy: string,
    proof: ProofHash,
    authorKey: TernaryCubicForm
  ): Promise<void> {
    const entry: DNAMergeEntry = {
      '@canvasl': 'merge',
      generation,
      polynomial: state.polynomial,
      parent_ids: parentIds,
      merge_strategy: strategy as any,
      merge_proof: proof,
      author_cubic_key: authorKey
    };

    await this.appendEntry(entry);
  }

  /**
   * Log identity operation
   *
   * @param operation - Identity operation type
   * @param identity - Sovereign identity
   * @param did - Decentralized identifier
   */
  async logIdentity(
    operation: 'create' | 'update' | 'revoke',
    identity: SovereignIdentity,
    did: string
  ): Promise<void> {
    const entry: DNAIdentityEntry = {
      '@canvasl': 'identity',
      operation,
      did,
      cubic_public_key: identity.cubic_keypair.public_cubic,
      sedenion_address: identity.multiverse_keys.sedenion_public,
      claims: identity.claims
    };

    await this.appendEntry(entry);
  }

  /**
   * Append entry to DNA log (atomic operation)
   *
   * @param entry - DNA entry to append
   */
  private async appendEntry(entry: DNAEntry): Promise<void> {
    const jsonLine = JSON.stringify(entry) + '\n';
    this.writeQueue.push(jsonLine);

    // Auto-flush if queue gets too large
    if (this.writeQueue.length >= 10) {
      await this.flush();
    }
  }

  /**
   * Flush write queue to file (atomic append)
   */
  async flush(): Promise<void> {
    if (this.writeQueue.length === 0 || this.isWriting) {
      return;
    }

    this.isWriting = true;
    const linesToWrite = [...this.writeQueue];
    this.writeQueue = [];

    try {
      // Get file handle for atomic append
      if (!this.fileHandle) {
        this.fileHandle = await this.getFileHandle();
      }

      // Append all queued lines atomically
      await this.atomicAppend(linesToWrite.join(''));

    } catch (error) {
      // Re-queue lines on failure
      this.writeQueue.unshift(...linesToWrite);
      throw error;
    } finally {
      this.isWriting = false;
    }
  }

  /**
   * Get file handle for DNA log
   */
  private async getFileHandle(): Promise<FileSystemFileHandle> {
    try {
      // Try to open existing file
      return await (navigator.storage?.getDirectory() as any)?.getFileHandle(this.filePath);
    } catch (error) {
      // File doesn't exist, create new
      const dir = await (navigator.storage?.getDirectory() as any)?.getDirectoryHandle('.');
      return await dir.getFileHandle(this.filePath, { create: true });
    }
  }

  /**
   * Atomic append operation
   *
   * @param data - Data to append
   */
  private async atomicAppend(data: string): Promise<void> {
    if (!this.fileHandle) {
      throw new Error('No file handle available');
    }

    const writable = await this.fileHandle.createWritable({ keepExistingData: true });
    await writable.seek(writable.getSize() || 0);
    await writable.write(new TextEncoder().encode(data));
    await writable.close();
  }

  /**
   * Read DNA log entries (streaming)
   *
   * @param entryType - Optional entry type filter
   * @param limit - Maximum entries to read
   * @returns Async generator of DNA entries
   */
  async *readEntries<T extends DNAEntry>(
    entryType?: DNAEntryType,
    limit?: number
  ): AsyncGenerator<T> {
    if (!this.fileHandle) {
      this.fileHandle = await this.getFileHandle();
    }

    const file = await this.fileHandle.getFile();
    const text = await file.text();
    const lines = text.split('\n').filter(line => line.trim() !== '');

    let count = 0;
    for (const line of lines) {
      if (limit && count >= limit) break;

      try {
        const entry = JSON.parse(line) as T;
        
        // Filter by entry type if specified
        if (!entryType || entry['@canvasl'] === entryType) {
          yield entry;
          count++;
        }
      } catch (error) {
        console.warn('Failed to parse DNA log entry:', line, error);
      }
    }
  }

  /**
   * Verify DNA log integrity
   *
   * @returns Integrity verification result
   */
  async verifyIntegrity(): Promise<{
    isValid: boolean;
    errors: string[];
    statistics: {
      totalEntries: number;
      entryTypes: Map<string, number>;
      hashChain: {
        broken: boolean;
        breakPoint?: string;
      };
    };
  }> {
    const errors: string[] = [];
    const entryTypes = new Map<string, number>();
    let totalEntries = 0;
    let lastHashChain = 'genesis';
    let hashChainBroken = false;
    let hashChainBreakPoint: string | undefined;

    // Read all entries and verify
    for await (const entry of this.readEntries()) {
      totalEntries++;
      
      // Count entry types
      const type = entry['@canvasl'];
      entryTypes.set(type, (entryTypes.get(type) || 0) + 1);

      // Verify hash chain for generation and merge entries
      if ((type === 'generation' || type === 'merge') && 'hash_chain' in entry) {
        const currentHashChain = (entry as any).hash_chain;
        
        // Verify hash chain continuity
        const expectedHashChain = await this.computeHashChain(lastHashChain, entry);
        if (currentHashChain !== expectedHashChain) {
          hashChainBroken = true;
          hashChainBreakPoint = (entry as any).commit_id || 'unknown';
          errors.push(`Hash chain broken at entry ${(entry as any).commit_id || 'unknown'}`);
        }
        
        lastHashChain = currentHashChain;
      }
    }

    return {
      isValid: errors.length === 0,
      errors,
      statistics: {
        totalEntries,
        entryTypes,
        hashChain: {
          broken: hashChainBroken,
          breakPoint: hashChainBreakPoint
        }
      }
    };
  }

  /**
   * Compute hash chain entry
   *
   * @param previousHash - Previous hash in chain
   * @param entry - Current entry
   * @returns Computed hash chain value
   */
  private async computeHashChain(previousHash: string, entry: DNAEntry): Promise<string> {
    const entryData = JSON.stringify(entry);
    const combined = previousHash + entryData;
    
    // Use production cryptography for secure hashing
    const encoder = new TextEncoder();
    const data = encoder.encode(combined);
    const hashBuffer = await crypto.subtle.digest('SHA-256', data);
    const hashArray = Array.from(new Uint8Array(hashBuffer));
    
    return hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
  }

  /**
   * Get DNA log statistics
   *
   * @returns Comprehensive log statistics
   */
  async getStatistics(): Promise<{
    fileSize: number;
    entryCount: number;
    entryTypes: Map<string, number>;
    lastModified: number;
  }> {
    if (!this.fileHandle) {
      this.fileHandle = await this.getFileHandle();
    }

    const file = await this.fileHandle.getFile();
    const text = await file.text();
    const lines = text.split('\n').filter(line => line.trim() !== '');
    
    const entryTypes = new Map<string, number>();
    for (const line of lines) {
      try {
        const entry = JSON.parse(line);
        const type = entry['@canvasl'];
        entryTypes.set(type, (entryTypes.get(type) || 0) + 1);
      } catch (error) {
        // Skip invalid lines
      }
    }

    return {
      fileSize: file.size || 0,
      entryCount: lines.length,
      entryTypes,
      lastModified: file.lastModified || Date.now()
    };
  }

  /**
   * Export DNA log in different formats
   *
   * @param format - Export format
   * @param outputPath - Output file path
   */
  async exportLog(format: 'json' | 'jsonl' | 'canvasl', outputPath: string): Promise<void> {
    const entries: DNAEntry[] = [];
    
    // Read all entries
    for await (const entry of this.readEntries()) {
      entries.push(entry);
    }

    let exportData: string;
    let fileName: string;

    switch (format) {
      case 'json':
        exportData = JSON.stringify(entries, null, 2);
        fileName = `${outputPath}.json`;
        break;
        
      case 'jsonl':
        exportData = entries.map(entry => JSON.stringify(entry)).join('\n');
        fileName = `${outputPath}.jsonl`;
        break;
        
      case 'canvasl':
        // Custom CanvasL format with metadata
        exportData = this.formatAsCanvasL(entries);
        fileName = `${outputPath}.canvasl`;
        break;
        
      default:
        throw new Error(`Unsupported export format: ${format}`);
    }

    // Write export file
    const blob = new Blob([exportData], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = fileName;
    a.click();
    URL.revokeObjectURL(url);
  }

  /**
   * Format entries as CanvasL native format
   *
   * @param entries - DNA entries
   * @returns CanvasL formatted string
   */
  private formatAsCanvasL(entries: DNAEntry[]): string {
    const manifest = entries.find(e => e['@canvasl'] === 'manifest');
    const generations = entries.filter(e => e['@canvasl'] === 'generation');
    const branches = entries.filter(e => e['@canvasl'] === 'branch');
    const merges = entries.filter(e => e['@canvasl'] === 'merge');
    const identities = entries.filter(e => e['@canvasl'] === 'identity');

    return `# CanvasL DNA Log Export
# Generated: ${new Date().toISOString()}

## Manifest
${JSON.stringify(manifest, null, 2)}

## Generations (${generations.length})
${generations.map(g => JSON.stringify(g, null, 2)).join('\n')}

## Branches (${branches.length})
${branches.map(b => JSON.stringify(b, null, 2)).join('\n')}

## Merges (${merges.length})
${merges.map(m => JSON.stringify(m, null, 2)).join('\n')}

## Identities (${identities.length})
${identities.map(i => JSON.stringify(i, null, 2)).join('\n')}
`;
  }

  /**
   * Close DNA logger and flush remaining writes
   */
  async close(): Promise<void> {
    await this.flush();
    this.fileHandle = null;
    this.writeQueue = [];
  }

  /**
   * Force flush of pending writes
   */
  async forceFlush(): Promise<void> {
    await this.flush();
  }
}