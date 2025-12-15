---
id: "mind-git:development:canvasl-replay-engine-js"
title: "Canvasl Replay Engine.Js"
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
keywords: ["canvasl","ast","octonion","javascript"]
lastUpdate: "2025-12-15"

---

```js
// canvasl-replay-engine.js

// Complete CanvasL DNA Replay Engine — Parses JSONL history for state reconstruction and navigation.

// Zero dependencies. Pure browser JavaScript.

  

/**

* @class CanvasLReplayEngine

* Handles loading, parsing, and navigating the append-only CanvasL DNA log (JSONL).

* Provides structured access to the genomic history.

*/

export class CanvasLReplayEngine {

constructor() {

/** @type {Array<Object>} The parsed and validated history of generation records. */

this.history = [];

/** @type {string | null} The full raw text content of the loaded DNA file. */

this.rawContent = null;

}

  

// -------------------------------------------------------------------------

// CORE PARSING METHODS

// -------------------------------------------------------------------------

  

/**

* Parses the JSONL content string and populates the history array.

* Only accepts records with "@canvasl": "generation".

* @param {string} textContent - The raw JSONL content of the DNA file.

* @returns {number} The number of generation records loaded.

*/

loadDNAFromText(textContent) {

if (!textContent) {

console.error("CanvasL Replay: Cannot load from empty text content.");

return 0;

}

  

this.rawContent = textContent;

const lines = textContent.trim().split('\n');

this.history = [];

  

for (let i = 0; i < lines.length; i++) {

const line = lines[i];

try {

const record = JSON.parse(line);

  

// Check for the manifest record (index 0)

if (i === 0 && record.canvasl) {

console.info(`CanvasL Replay: Loaded manifest v${record.canvasl} for ${record.organism}.`);

// Skip the manifest record for the generation history

continue;

}

  

// Only log and store generation records

if (record['@canvasl'] === 'generation' && record.genome && record.octonion_table_raw) {

this.history.push(record);

}

  

} catch (e) {

console.warn(`CanvasL Replay: Skipped malformed line ${i + 1}.`, e);

}

}

  

console.log(`%cCanvasL Replay Engine: Successfully loaded ${this.history.length} generation(s).`, "color:#007bff; font-weight:bold;");

return this.history.length;

}

  

// -------------------------------------------------------------------------

// BROWSER FILE SYSTEM ACCESS (User Interaction)

// -------------------------------------------------------------------------

  

/**

* Prompts the user to select and load a .canvasl DNA file.

* Uses the File System Access API if available, otherwise falls back to a standard <input type="file">.

* @returns {Promise<boolean>} True if loading was successful, false otherwise.

*/

async loadDNAFromFile() {

try {

if (typeof window.showOpenFilePicker !== "undefined") {

// --- File System Access API ---

const [handle] = await window.showOpenFilePicker({

types: [{

description: "CanvasL Genomic Log",

accept: { "application/jsonlines": [".canvasl"] }

}],

multiple: false

});

  

const file = await handle.getFile();

const textContent = await file.text();

this.loadDNAFromText(textContent);

return this.history.length > 0;

  

} else {

// --- Standard Input Fallback ---

return new Promise((resolve) => {

const input = document.createElement('input');

input.type = 'file';

input.accept = '.canvasl, application/jsonlines';

input.style.display = 'none';

  

input.onchange = async (e) => {

const file = e.target.files[0];

if (file) {

const textContent = await file.text();

this.loadDNAFromText(textContent);

resolve(this.history.length > 0);

} else {

resolve(false);

}

input.remove(); // Clean up the element

};

  

input.click(); // Trigger the file selection dialog

});

}

} catch (err) {

if (err.name !== "AbortError") {

console.error("CanvasL Replay: File loading aborted or failed.", err);

} else {

console.warn("CanvasL Replay: File selection cancelled by user.");

}

return false;

}

}

  

// -------------------------------------------------------------------------

// HISTORY NAVIGATION METHODS

// -------------------------------------------------------------------------

  

/**

* Gets the full history of generation records.

* This is the foundation for Git-like history visualization and branching.

* @returns {Array<Object>} The full history array.

*/

getFullHistory() {

return this.history;

}

  

/**

* Gets the most recently evolved genome (the last record in the log).

* @returns {Object | null} The latest generation record or null if history is empty.

*/

getLatestGenome() {

return this.history.length > 0 ? this.history[this.history.length - 1] : null;

}

  

/**

* Gets a specific generation record by its index in the history array.

* Index 0 is the first generation.

* @param {number} index - The zero-based index of the generation to retrieve.

* @returns {Object | null} The specific generation record or null if the index is out of bounds.

*/

getGeneration(index) {

if (index >= 0 && index < this.history.length) {

return this.history[index];

}

console.error(`CanvasL Replay: Generation index ${index} out of bounds (0-${this.history.length - 1}).`);

return null;

}

  

/**

* Gets the raw octonion multiplication table for a specific generation.

* This is the core state needed for system replay.

* @param {number} index - The zero-based index of the generation.

* @returns {Array<Array<[number, number]>> | null} The raw octonion table or null.

*/

getOctTableForGeneration(index) {

const record = this.getGeneration(index);

return record ? record.octonion_table_raw : null;

}

}
```