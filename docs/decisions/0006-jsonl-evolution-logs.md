# ADR 0006: Use JSONL for Append-Only Evolution Logs

## Status

Accepted

## Context

How should we store the evolution history of genomes (state changes, mutations, dimensional expansions)? Requirements:

- **Cryptographic replay**: Verify entire history
- **Append-only**: Never overwrite past states
- **Streamable**: Process large histories incrementally
- **Human-readable**: Debug and audit trails
- **Merkle tree compatible**: Provenance verification

## Decision

**Use JSONL (JSON Lines) format for `.canvasl` evolution log files**. Each line = one event, append-only, cryptographically linked via Merkle tree.

Format: One JSON object per line, newline-delimited.

## Rationale

### Why JSONL?

**Append-only by design**:
- Each event is a new line
- Never modify existing lines
- File grows monotonically

**Streamable**:
```javascript
// Process line-by-line without loading entire file
const stream = fs.createReadStream('genome.canvasl');
for await (const line of stream) {
  const event = JSON.parse(line);
  processEvent(event);
}
```

**Merkle tree construction**:
```
Event 1 → hash₁ ──┐
Event 2 → hash₂ ──┼→ hash₁₂ ──┐
Event 3 → hash₃ ──┤            ├→ root_hash
Event 4 → hash₄ ──┘            │
```

**Human-readable**:
- Standard JSON format
- Grep-able (`grep "mutation" genome.canvasl`)
- Diff-able (`diff genome1.canvasl genome2.canvasl`)

### Format Specification

```jsonl
{"event":"genome_created","time":1704067200,"genome":[1,0,0,0,0,0,0,0],"hash":"abc123"}
{"event":"mutation","time":1704067201,"diff":[0,1,0,0,0,0,0,0],"prev_hash":"abc123","hash":"def456"}
{"event":"dimension_expand","time":1704067202,"from":8,"to":16,"reason":"sync","hash":"ghi789"}
{"event":"dimension_reduce","time":1704067203,"from":16,"to":8,"hash":"jkl012"}
```

Each line:
- Self-contained JSON object
- Timestamp for ordering
- Hash linking to previous event (Merkle chain)
- Event-specific data

## Consequences

### Positive

- ✅ Cryptographic replay (Merkle tree verification)
- ✅ Append-only (immutable history)
- ✅ Streamable (process incrementally)
- ✅ Human-readable (JSON format)
- ✅ Git-friendly (line-based diffs)
- ✅ Simple implementation (no database required)

### Negative

- ❌ Grows without bound (need pruning strategy)
- ❌ No random access (must scan sequentially)
- ❌ Larger than binary formats

### Neutral

- ⚪ Compression via gzip works well
- ⚪ Periodic snapshots for faster replay
- ⚪ Archive old events to separate files

## Compliance

### File Structure

```
genome-{id}.canvasl        # Evolution log
genome-{id}.canvasl.gz     # Compressed archive
genome-{id}-snapshot.json  # Periodic snapshot (optional)
```

### Implementation

```typescript
class EvolutionLog {
  private filepath: string;
  private merkleTree: MerkleTree;

  async append(event: LogEntry): Promise<void> {
    // 1. Compute hash linking to previous
    const prevHash = this.merkleTree.root();
    const hash = sha256(JSON.stringify(event) + prevHash);

    // 2. Add to Merkle tree
    this.merkleTree.addLeaf(hash);

    // 3. Append to file (never overwrites)
    const line = JSON.stringify({ ...event, hash, prev_hash: prevHash });
    await fs.appendFile(this.filepath, line + '\n');
  }

  async replay(): Promise<Genome> {
    const stream = fs.createReadStream(this.filepath);
    let state = null;

    for await (const line of stream) {
      const event = JSON.parse(line);

      // Verify hash chain
      if (!this.verifyHash(event)) {
        throw new Error('Corrupted evolution log');
      }

      // Apply event
      state = this.applyEvent(state, event);
    }

    return state;
  }

  async verify(index: number): Promise<boolean> {
    // Cryptographic proof of history
    return this.merkleTree.verify(index);
  }
}
```

### Event Types

**Standard events**:
- `genome_created` - Initial genome
- `mutation` - Polynomial coefficient change
- `dimension_expand` - 8D → 16D (for sync)
- `dimension_reduce` - 16D → 8D (after sync)
- `merge` - GCD merge with another genome
- `fork` - Branch into alternate evolution path

### Merkle Tree Verification

```typescript
// Verify entire history without replaying
async function verifyHistory(filepath: string): Promise<boolean> {
  const events = await readAllEvents(filepath);
  const hashes = events.map(e => e.hash);

  const tree = MerkleTree.fromLeaves(hashes);
  const rootHash = tree.root();

  // Compare with committed root hash
  const committed = await getCommittedRootHash();
  return rootHash === committed;
}
```

## Documentation

- `dev-docs/MindGit/MindGit Technical Specification v3.0.md`
- **DESIGN_PRINCIPLES.md** - Principle #10: Append-Only Evolution

## References

- JSONL Specification: https://jsonlines.org/
- Merkle Trees: R. Merkle (1987)
- Git object storage (similar append-only model)

## Author

Initial: 2024-12
Updated: 2025-12
