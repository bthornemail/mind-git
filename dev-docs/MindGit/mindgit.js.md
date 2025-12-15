---
id: "mind-git:development:mindgit-js"
title: "Mindgit.Js"
type: ["development"]
category: development
layer: 7
dimensions: [8, 16]
mathematicalFoundation: ["division-algebras"]
hopfCompatible: false
normPreserving: false
status: "complete"
completeness: 70
tags: ["development","documentation","canvasl","ast","api"]
keywords: ["canvasl","ast","octonion"]
lastUpdate: "2025-12-15"

---

```js
// mindgit.js

// Git-like branching + merging for CanvasL minds

// Zero dependencies. Works in browsers and workers.

// Integrates with CanvasLDNALayer JSONL DNA logs.

  

export class MindGit {

  constructor() {

    // central commit store: array of commit objects { id, record }

    this.commits = [];

    // branches: map name -> { name, head: commitId or null, commits: [commitId...] }

    this.branches = {};

    // current branch name

    this.head = null;

    // staging area to create commit from in-memory generation

    this.staging = null;

    // simple deterministic id generator (sha-like but not crypto)

    this._idCounter = 0;

  }

  

  // ---------------------------

  // Utilities

  // ---------------------------

  _newId(prefix = "c") {

    this._idCounter += 1;

    const time = Date.now().toString(36);

    return `${prefix}${time}.${this._idCounter}`;

  }

  

  _clone(obj) { return JSON.parse(JSON.stringify(obj)); }

  

  // Parse a JSONL string into commit objects (accepts many record types, filters generations)

  static parseJSONL(jsonlText) {

    const lines = jsonlText.split(/\r?\n/).filter(Boolean);

    const parsed = [];

    for (const l of lines) {

      try {

        parsed.push(JSON.parse(l));

      } catch (e) {

        // skip invalid lines

        console.warn("MindGit: skipping invalid JSONL line");

      }

    }

    return parsed;

  }

  

  // ---------------------------

  // Repository creation

  // ---------------------------

  // import existing DNA JSONL content and create commits for each generation

  importFromDNAJsonl(jsonlText, opts = { branch: "main" }) {

    const parsed = MindGit.parseJSONL(jsonlText);

    // filter generation records

    const gens = parsed.filter(r => r && r["@canvasl"] === "generation");

    for (const g of gens) {

      const id = this._newId("c");

      this.commits.push({ id, record: this._clone(g) });

    }

    // create branch and point head to last commit if exists

    const branchName = opts.branch || "main";

    if (!this.branches[branchName]) {

      this.branches[branchName] = { name: branchName, head: null, commits: [] };

    }

    for (const c of this.commits) {

      this.branches[branchName].commits.push(c.id);

      this.branches[branchName].head = c.id;

    }

    if (this.head === null) this.head = branchName;

    return this.branches[branchName];

  }

  

  // create empty repository + initial branch

  init(branch = "main") {

    this.commits = [];

    this.branches = {};

    this.head = branch;

    this.branches[branch] = { name: branch, head: null, commits: [] };

  }

  

  // ---------------------------

  // Commit / Stage / Checkout

  // ---------------------------

  // Stage a generation (object in same format as DNA record)

  stageGeneration(generationRecord) {

    this.staging = this._clone(generationRecord);

  }

  

  // Commit staged generation to current branch

  commit(message = "") {

    if (!this.head) throw new Error("No branch checked out");

    if (!this.staging) throw new Error("Nothing staged");

    const id = this._newId("c");

    const commit = { id, record: this._clone(this.staging), meta: { message, time: new Date().toISOString() } };

    this.commits.push(commit);

    // update branch

    const b = this.branches[this.head];

    b.commits.push(id);

    b.head = id;

    // clear staging

    this.staging = null;

    return commit;

  }

  

  // Create a new branch from existing branch or commit id

  createBranch(name, from = null) {

    if (this.branches[name]) throw new Error(`Branch ${name} already exists`);

    // determine starting commit ids

    let startCommits = [];

    if (!from) {

      // from current head branch

      startCommits = this.branches[this.head].commits.slice();

    } else if (typeof from === "string") {

      // if from is an existing branch

      if (this.branches[from]) startCommits = this.branches[from].commits.slice();

      else {

        // from may be a commit id

        const idx = this.commits.findIndex(c => c.id === from);

        if (idx === -1) throw new Error("Invalid from commit id");

        // include all commits up to idx

        startCommits = this.commits.slice(0, idx + 1).map(c => c.id);

      }

    } else {

      throw new Error("Invalid 'from' parameter");

    }

    this.branches[name] = { name, head: startCommits.length ? startCommits[startCommits.length - 1] : null, commits: startCommits };

    return this.branches[name];

  }

  

  // Checkout a branch

  checkout(branchName) {

    if (!this.branches[branchName]) throw new Error(`No such branch: ${branchName}`);

    this.head = branchName;

    return this.branches[branchName];

  }

  

  // List branches

  listBranches() {

    return Object.keys(this.branches).map(n => ({ name: n, head: this.branches[n].head }));

  }

  

  // Get commit by id

  getCommit(id) {

    return this.commits.find(c => c.id === id) || null;

  }

  

  // Get branch head commit object

  headCommit(branchName = null) {

    const name = branchName || this.head;

    const b = this.branches[name];

    if (!b || !b.head) return null;

    return this.getCommit(b.head);

  }

  

  // Log commits for a branch (most recent first)

  log(branchName = null) {

    const name = branchName || this.head;

    const b = this.branches[name];

    if (!b) throw new Error("No such branch");

    // map commit ids to commit objects

    return b.commits.slice().reverse().map(id => this.getCommit(id));

  }

  

  // ---------------------------

  // Diff utilities

  // ---------------------------

  // Diff two octonion tables (raw)

  static diffOctTables(aTable, bTable) {

    // produce list of changed cells as { i, j, a, b }

    const diffs = [];

    const rows = Math.max(aTable.length, bTable.length);

    for (let i = 0; i < rows; i++) {

      const aRow = aTable[i] || [];

      const bRow = bTable[i] || [];

      const cols = Math.max(aRow.length, bRow.length);

      for (let j = 0; j < cols; j++) {

        const aCell = (aRow[j] === undefined) ? null : aRow[j];

        const bCell = (bRow[j] === undefined) ? null : bRow[j];

        // stringify for deep-eq

        const as = JSON.stringify(aCell);

        const bs = JSON.stringify(bCell);

        if (as !== bs) diffs.push({ i, j, a: aCell, b: bCell });

      }

    }

    return diffs;

  }

  

  // Diff two commits (by id)

  diffCommits(idA, idB) {

    const ca = this.getCommit(idA);

    const cb = this.getCommit(idB);

    if (!ca || !cb) throw new Error("Invalid commit id(s)");

    const tA = ca.record.octonion_table_raw;

    const tB = cb.record.octonion_table_raw;

    return MindGit.diffOctTables(tA, tB);

  }

  

  // ---------------------------

  // Merge strategies

  // ---------------------------

  // main merge API:

  // merge(branchSource, branchTarget, strategy)

  // returns { success, mergedCommit, report }

  async merge(branchA, branchB, strategy = "choose-latest", opts = {}) {

    // merge branchA into branchB (branchB is the target; head moves to merged commit)

    if (!this.branches[branchA]) throw new Error(`Missing branch ${branchA}`);

    if (!this.branches[branchB]) throw new Error(`Missing branch ${branchB}`);

  

    const commitA = this.headCommit(branchA);

    const commitB = this.headCommit(branchB);

    if (!commitA || !commitB) throw new Error("One of the branches has no commits");

  

    const recA = commitA.record;

    const recB = commitB.record;

  

    // choose strategy

    let mergedRecord;

    let report = { strategy, conflicts: [], decisions: [] };

  

    if (strategy === "choose-latest") {

      // choose the generation with higher timestamp

      const timeA = new Date(recA.timestamp).getTime();

      const timeB = new Date(recB.timestamp).getTime();

      mergedRecord = timeA >= timeB ? this._clone(recA) : this._clone(recB);

      report.decisions.push({ reason: "timestamp", chosen: timeA >= timeB ? commitA.id : commitB.id });

    } else if (strategy === "fitness-weighted") {

      // choose cell-by-cell by fitness weighting

      mergedRecord = this._clone(recB); // start with target

      const tableA = recA.octonion_table_raw;

      const tableB = recB.octonion_table_raw;

      const mergedTable = [];

      const rows = Math.max(tableA.length, tableB.length);

      for (let i = 0; i < rows; i++) {

        const rowA = tableA[i] || [];

        const rowB = tableB[i] || [];

        const cols = Math.max(rowA.length, rowB.length);

        const mergedRow = [];

        for (let j = 0; j < cols; j++) {

          const aCell = rowA[j] === undefined ? null : rowA[j];

          const bCell = rowB[j] === undefined ? null : rowB[j];

          if (JSON.stringify(aCell) === JSON.stringify(bCell)) {

            mergedRow[j] = this._clone(aCell);

            continue;

          }

          // pick based on fitness

          const pickA = recA.fitness >= recB.fitness;

          mergedRow[j] = pickA ? this._clone(aCell) : this._clone(bCell);

          report.decisions.push({ i, j, chosen: pickA ? "A" : "B" });

        }

        mergedTable.push(mergedRow);

      }

      mergedRecord.octonion_table_raw = mergedTable;

      report.decisions.push({ reason: "fitness", fitnessA: recA.fitness, fitnessB: recB.fitness });

    } else if (strategy === "crossover") {

      // simple deterministic crossover: even-indexed cells from A, odd from B

      mergedRecord = this._clone(recB); // base

      const tableA = recA.octonion_table_raw;

      const tableB = recB.octonion_table_raw;

      const mergedTable = [];

      const rows = Math.max(tableA.length, tableB.length);

      for (let i = 0; i < rows; i++) {

        const rowA = tableA[i] || [];

        const rowB = tableB[i] || [];

        const cols = Math.max(rowA.length, rowB.length);

        const mergedRow = [];

        for (let j = 0; j < cols; j++) {

          const useA = ((i + j) % 2 === 0);

          const aCell = rowA[j] === undefined ? null : rowA[j];

          const bCell = rowB[j] === undefined ? null : rowB[j];

          if (JSON.stringify(aCell) === JSON.stringify(bCell)) {

            mergedRow[j] = this._clone(aCell);

          } else {

            mergedRow[j] = this._clone(useA ? aCell : bCell);

            report.decisions.push({ i, j, chosen: useA ? "A" : "B" });

          }

        }

        mergedTable.push(mergedRow);

      }

      mergedRecord.octonion_table_raw = mergedTable;

      report.decisions.push({ reason: "crossover", pattern: "even=A odd=B" });

    } else {

      throw new Error("Unknown merge strategy");

    }

  

    // Validate that mergedRecord looks sane (has generation number, fitness etc.)

    mergedRecord = mergedRecord || {};

    mergedRecord.generation = (Math.max(recA.generation || 0, recB.generation || 0) + 1);

    mergedRecord.timestamp = new Date().toISOString();

    // merge metadata

    mergedRecord.fitness = Math.max(recA.fitness || 0, recB.fitness || 0);

    mergedRecord.mutation_rate = (recA.mutation_rate + recB.mutation_rate) / 2 || 0;

    mergedRecord.diversity = (recA.diversity + recB.diversity) / 2 || 0;

    mergedRecord.observations = (recA.observations || 0) + (recB.observations || 0);

    mergedRecord.meta = { merged_from: [commitA.id, commitB.id], strategy };

  

    // create commit and attach to target branch (branchB)

    const commit = { id: this._newId("m"), record: this._clone(mergedRecord), meta: { merged: true, time: new Date().toISOString() } };

    this.commits.push(commit);

    this.branches[branchB].commits.push(commit.id);

    this.branches[branchB].head = commit.id;

  

    report.mergedCommit = commit.id;

    report.success = true;

    return report;

  }

  

  // ---------------------------

  // Export / Import

  // ---------------------------

  // Export a branch as JSONL (string)

  exportBranchAsJSONL(branchName) {

    if (!this.branches[branchName]) throw new Error("No such branch");

    const out = [];

    for (const id of this.branches[branchName].commits) {

      const c = this.getCommit(id);

      if (!c) continue;

      out.push(JSON.stringify(c.record));

    }

    return out.join("\n") + (out.length ? "\n" : "");

  }

  

  // Export a single commit (snapshot) as pretty JSON

  exportCommitSnapshot(commitId) {

    const c = this.getCommit(commitId);

    if (!c) throw new Error("No such commit");

    return JSON.stringify(c.record, null, 2);

  }

  

  // Import additional commits from JSONL into current branch

  importJsonlToBranch(jsonlText, branchName = null) {

    const parsed = MindGit.parseJSONL(jsonlText);

    const gens = parsed.filter(r => r && r["@canvasl"] === "generation");

    for (const g of gens) {

      const id = this._newId("c");

      this.commits.push({ id, record: this._clone(g) });

      const b = this.branches[branchName || this.head];

      b.commits.push(id);

      b.head = id;

    }

  }

}
```