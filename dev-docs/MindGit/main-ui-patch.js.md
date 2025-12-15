---
id: "mind-git:development:main-ui-patch-js"
title: "Main Ui Patch.Js"
type: ["development"]
category: development
layer: 7
dimensions: [8, 16]
mathematicalFoundation: ["division-algebras"]
hopfCompatible: false
normPreserving: false
status: "complete"
completeness: 70
tags: ["development","documentation","canvasl","api"]
keywords: ["canvasl","octonion"]
lastUpdate: "2025-12-15"

---

```js
// DROP-IN PATCH for Main UI/Engine

// This implementation now handles file loading directly to feed raw text to MindGit.

  

import { CanvasLReplayEngine } from './canvasl-replay-engine.js';

import { MindGit } from './mindgit.js'; // Import the new MindGit class

  

// Global state for the engine

const replayEngine = new CanvasLReplayEngine();

const mindRepo = new MindGit(); // Initialize the Git repository

let currentBranch = 'main'; // Track the currently active branch name

let selectedCommitId = null; // Track the commit selected for inspection/diff

  

document.addEventListener('DOMContentLoaded', () => {

// 1. Setup UI for loading and status

const loadButton = document.getElementById('load-dna-button');

const statusDiv = document.getElementById('replay-status');

const historyList = document.getElementById('history-list');

const currentStatusDiv = document.getElementById('current-genome-status');

const inspectionDiv = document.getElementById('genome-inspection');

  

// Initialize the repository structure

mindRepo.init(currentBranch);

  

if (!loadButton || !statusDiv || !historyList || !currentStatusDiv || !inspectionDiv) {

console.error('Replay UI elements not found. Skipping patch execution.');

return;

}

  

// --- Core File Loading Logic (moved from ReplayEngine for raw text access) ---

async function loadDNAFile() {

try {

if (typeof window.showOpenFilePicker === "undefined") {

statusDiv.textContent = 'File System Access API not available. Please use a modern browser.';

return null;

}

const [handle] = await window.showOpenFilePicker({

types: [{

description: "CanvasL Genomic Log",

accept: { "application/jsonlines": [".canvasl"] }

}],

multiple: false

});

  

const file = await handle.getFile();

return await file.text();

} catch (err) {

if (err.name !== "AbortError") {

console.error("CanvasL DNA Load failed:", err);

statusDiv.textContent = `DNA Load Failed: ${err.message}`;

} else {

statusDiv.textContent = 'DNA Load Cancelled.';

}

return null;

}

}

// -----------------------------------------------------------------------------

  

// 2. Load DNA Handler

loadButton.onclick = async () => {

statusDiv.textContent = 'Loading DNA file...';

loadButton.disabled = true;

historyList.innerHTML = '';

selectedCommitId = null;

inspectionDiv.textContent = 'Select a genome to inspect...';

const textContent = await loadDNAFile();

  

if (textContent) {

// 1. Use ReplayEngine to parse and check validity (optional, but good for raw validation)

const count = replayEngine.loadDNAFromText(textContent);

// 2. Load the history into the MindGit repository

mindRepo.init(currentBranch); // Reset the repo

mindRepo.importFromDNAJsonl(textContent, { branch: currentBranch });

  

const history = mindRepo.log(currentBranch);

statusDiv.textContent = `Load Complete: ${count} records (${history.length} commits) found in branch '${currentBranch}'.`;

updateCurrentStatus(mindRepo.headCommit());

displayHistory(history);

} else {

updateCurrentStatus(null);

}

  

loadButton.disabled = false;

};

  

// Update the display for the currently active genome

function updateCurrentStatus(commit) {

if (commit) {

const record = commit.record;

currentStatusDiv.innerHTML = `

<span class="font-semibold text-blue-700">CURRENT BRANCH: ${mindRepo.head}</span>

| COMMIT: ${commit.id.substring(0, 7)}...

| Gen ${record.generation} | Fitness: ${record.fitness.toFixed(4)} | Born: ${new Date(record.timestamp).toLocaleTimeString()}

`;

} else {

currentStatusDiv.textContent = 'No active genome (Load DNA log to begin).';

}

// Re-display history to update the 'CURRENT' indicator

if (mindRepo.headCommit()) {

displayHistory(mindRepo.log(mindRepo.head));

}

}

  

// 3. History Visualization and Git Actions

function displayHistory(history) {

historyList.innerHTML = '';

const headId = mindRepo.headCommit(mindRepo.head)?.id;

  

history.forEach((commit, index) => {

const record = commit.record;

const isCurrent = commit.id === headId;

const isSelected = commit.id === selectedCommitId;

  

const listItem = document.createElement('li');

listItem.className = `p-2 border-b flex justify-between items-center transition-colors text-sm ${

isCurrent ? 'bg-green-100 font-bold' : isSelected ? 'bg-yellow-100' : 'hover:bg-gray-100 cursor-pointer'

}`;

// Display the core metadata

const currentMarker = isCurrent ? ' *HEAD* ' : '';

const summary = `${currentMarker} ${commit.id.substring(0, 7)}... | Gen ${record.generation} | Fitness: ${record.fitness.toFixed(4)}`;

const summarySpan = document.createElement('span');

summarySpan.textContent = summary;

listItem.appendChild(summarySpan);

  

const buttonContainer = document.createElement('div');

buttonContainer.className = 'flex space-x-2';

  

// Button for "Checkout" (Branching)

const checkoutButton = document.createElement('button');

checkoutButton.textContent = 'Checkout';

checkoutButton.className = 'bg-blue-500 hover:bg-blue-700 text-white font-bold py-1 px-2 rounded-lg text-xs disabled:opacity-50';

checkoutButton.disabled = isCurrent;

checkoutButton.onclick = async (e) => {

e.stopPropagation();

// Create a new branch at this commit and checkout, or checkout if exists

const newBranchName = `gen-${record.generation}-branch`;

try {

// Check if branch exists, if not, create it from this commit

if (!mindRepo.branches[newBranchName]) {

mindRepo.createBranch(newBranchName, commit.id);

statusDiv.textContent = `Created and Checked out new branch: ${newBranchName}`;

} else {

statusDiv.textContent = `Checked out existing branch: ${newBranchName}`;

}

mindRepo.checkout(newBranchName);

currentBranch = newBranchName;

const genome = commit.record.octonion_table_raw;

updateCurrentStatus(mindRepo.headCommit());

// In a real system, you would call:

// postMessage({ type: 'load-genome', table: genome, generation: record.generation });

console.log(`--- CHECKOUT/BRANCHED TO ${mindRepo.head} (${commit.id.substring(0, 7)}...) ---`);

console.log('Genome Octonion Table loaded for replay (Checkout):', genome);

} catch (error) {

statusDiv.textContent = `Checkout Failed: ${error.message}`;

}

};

buttonContainer.appendChild(checkoutButton);

  

// Button for "Inspect" (Diff/Merge Preparation)

const inspectButton = document.createElement('button');

inspectButton.textContent = isSelected ? 'Inspected' : 'Inspect';

inspectButton.className = 'bg-gray-400 hover:bg-gray-600 text-white font-bold py-1 px-2 rounded-lg text-xs disabled:opacity-50';

inspectButton.disabled = isSelected;

inspectButton.onclick = (e) => {

e.stopPropagation();

selectedCommitId = commit.id;

const currentCommit = mindRepo.headCommit();

  

if (currentCommit) {

// Placeholder for actual Diff/Merge logic

const diffs = MindGit.diffOctTables(currentCommit.record.octonion_table_raw, commit.record.octonion_table_raw);

inspectionDiv.innerHTML = `

<h4 class="font-bold mb-1">Inspecting Commit ${commit.id.substring(0, 7)}...</h4>

<p class="text-xs mb-2">Comparing against CURRENT HEAD (${currentCommit.id.substring(0, 7)}...).</p>

<p class="text-sm font-semibold">${diffs.length} cell difference(s) found.</p>

<pre class="bg-white p-2 text-xs mt-2 border rounded overflow-x-auto max-h-24">${JSON.stringify(diffs.slice(0, 3), null, 2)}...</pre>

<select id="merge-strategy" class="mt-2 p-1 border rounded text-sm">

<option value="choose-latest">Merge Strategy: Latest Timestamp</option>

<option value="fitness-weighted">Merge Strategy: Fitness Weighted</option>

<option value="crossover">Merge Strategy: Crossover (Deterministic)</option>

</select>

  

<button id="merge-button" class="mt-2 ml-2 bg-purple-500 hover:bg-purple-700 text-white font-bold py-1 px-2 rounded-lg text-sm">

MERGE (Into ${mindRepo.head})

</button>

`;

// Add listener for the Merge button

document.getElementById('merge-button').onclick = async () => {

const strategy = document.getElementById('merge-strategy').value;

console.log(`--- MERGE REQUESTED: ${strategy} ---`);

try {

// Merge the selected commit's branch into the current head branch

const sourceBranchName = `gen-${record.generation}-branch`;

if (!mindRepo.branches[sourceBranchName]) {

// Create temporary branch for source commit if it wasn't checked out before

mindRepo.createBranch(sourceBranchName, commit.id);

}

  

const report = await mindRepo.merge(sourceBranchName, mindRepo.head, strategy);

updateCurrentStatus(mindRepo.headCommit());

statusDiv.textContent = `Merge Successful! New HEAD: ${mindRepo.headCommit().id.substring(0, 7)}... Strategy: ${strategy}. Decisions: ${report.decisions.length}`;

console.log("Merge Report:", report);

} catch (error) {

statusDiv.textContent = `Merge Failed: ${error.message}`;

console.error("Merge Error:", error);

}

};

}

  

displayHistory(mindRepo.log(mindRepo.head)); // Update the visual selection state

};

buttonContainer.appendChild(inspectButton);

listItem.appendChild(buttonContainer);

historyList.appendChild(listItem);

});

}

});

  

// For external use (e.g., in console or other modules)

export { replayEngine, mindRepo };
```