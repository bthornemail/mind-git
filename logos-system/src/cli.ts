#!/usr/bin/env node

import { compileCanvas } from './compiler/index';
import { readFileSync, writeFileSync } from 'fs';
import { join } from 'path';

const args = process.argv.slice(2);

async function main() {

if (args.length === 0) {
  console.log(`
CanvasL Logos System CLI

Usage:
  canvasl compile <canvas-file> [output-file]
  canvasl --help

Examples:
  canvasl compile examples/spatial-hello-world.json
  canvasl compile examples/spatial-hello-world.json output.js
  `);
  process.exit(0);
}

const command = args[0];

if (command === 'compile') {
  const inputFile = args[1];
  const outputFile = args[2] || 'output.js';
  
  if (!inputFile) {
    console.error('Error: Input file required');
    process.exit(1);
  }
  
  try {
    const canvasContent = readFileSync(inputFile, 'utf-8');
    const canvas = JSON.parse(canvasContent);
    
    console.log(`Compiling ${inputFile}...`);
    const result = await compileCanvas(canvas);
    
    if (result.success && result.javascript_code) {
      writeFileSync(outputFile, result.javascript_code);
      console.log(`✅ Compiled successfully to ${outputFile}`);
    } else {
      console.error('❌ Compilation failed:', result.errors);
      process.exit(1);
    }
  } catch (error) {
    console.error('❌ Error:', error.message);
    process.exit(1);
  }
} else if (command === '--help' || command === '-h') {
  console.log(`
CanvasL Logos System - Visual Programming Compiler

Commands:
  compile <canvas-file> [output-file]  Compile Canvas JSON to executable code
  --help, -h                         Show this help message

Examples:
  canvasl compile examples/spatial-hello-world.json
  canvasl compile examples/spatial-hello-world.json output.js

For more information, visit: https://github.com/bthornemail/mind-git
  `);
} else {
  console.error(`Unknown command: ${command}`);
  console.error('Use --help for available commands');
  process.exit(1);
}
}

main().catch(error => {
  console.error('❌ CLI Error:', error.message);
  process.exit(1);
});