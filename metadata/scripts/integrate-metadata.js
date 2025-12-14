#!/usr/bin/env node

/**
 * MIND-GIT Metadata Integration Script
 * 
 * Integrates the unified metadata framework with existing components
 */

import { promises as fs } from 'fs';
import path from 'path';
import { execSync } from 'child_process';
import { parse as parseYAML } from 'yaml';

/**
 * @typedef {Object} ComponentConfig
 * @property {string} path
 * @property {string} type
 * @property {number} layer
 * @property {string} category
 * @property {number[]} dimensions
 */

console.log('🧠 MIND-GIT Metadata Integration');
console.log('='.repeat(80));

// Configuration based on existing codebase structure
const COMPONENTS: Record<string, ComponentConfig> = {
  cli: {
    path: 'bin/mind-git-simple.cjs',
    type: 'compiler',
    layer: 3,
    category: 'core-compiler',
    dimensions: [3, 4, 5]
  },
  obsidianPlugin: {
    path: '.obsidian/plugins/logos-visual-compiler',
    type: 'integration',
    layer: 4,
    category: 'ide-integration',
    dimensions: [2, 3, 4]
  },
  webrtcFederation: {
    path: 'src/p2p',
    type: 'federation',
    layer: 5,
    category: 'distributed-sync',
    dimensions: [6, 7, 8]
  },
  mathematicalFoundation: {
    path: 'logos-system/src/core',
    type: 'mathematics',
    layer: 2,
    category: 'formal-verification',
    dimensions: [0, 1, 9]
  },
  compiler: {
    path: 'logos-system/src/compiler',
    type: 'compiler',
    layer: 3,
    category: 'core-compiler',
    dimensions: [3, 4, 5]
  },
  formalVerification: {
    path: 'logos-system/formal',
    type: 'mathematics',
    layer: 1,
    category: 'formal-verification',
    dimensions: [0, 1]
  },
  research: {
    path: 'docs/research',
    type: 'research',
    layer: 7,
    category: 'research',
    dimensions: [8, 9, 10]
  }
};

async function integrateMetadata() {
  console.log('\n📊 Component Analysis');
  console.log('='.repeat(80));
  
  const basePath = process.cwd();
  const service = new MetadataService(basePath);
  
  for (const [name, config] of Object.entries(COMPONENTS)) {
    console.log(`\n🔍 Analyzing ${name}...`);
    
    try {
      // 1. Generate component metadata
      const metadata = await analyzeComponent(basePath, name, config);
      
      // 2. Create AGENTS.md
      await createAgentsFile(basePath, name, config, metadata);
      
      // 3. Update front matter in key files
      await updateFrontMatter(basePath, config.path, metadata);
      
      // 4. Generate JSONL metadata
      await generateJSONLMetadata(basePath, name, metadata);
      
      console.log(`✅ ${name}: Metadata integrated`);
    } catch (error) {
      console.error(`❌ ${name}: Failed to integrate metadata - ${error.message}`);
    }
  }
  
  // 5. Generate global relationships
  await generateGlobalRelationships(basePath);
  
  // 6. Create metadata index
  await createMetadataIndex(basePath);
  
  console.log('\n🎉 Metadata Integration Complete!');
  console.log('='.repeat(80));
  console.log('\n📁 Metadata Structure:');
  
  try {
    const result = execSync('find .metadata -type f | sort', { encoding: 'utf8' });
    console.log(result);
  } catch (error) {
    console.log('Metadata structure created');
  }
}

/**
 * Analyze component and generate metadata
 * @param {string} basePath 
 * @param {string} name 
 * @param {ComponentConfig} config 
 * @returns {Promise<any>}
 */
async function analyzeComponent(basePath: string, name: string, config) {
  const componentPath = path.join(basePath, config.path);
  
  // Check if path exists
  if (!require('fs').existsSync(componentPath)) {
    console.warn(`⚠️ Path does not exist: ${componentPath}`);
    return null;
  }
  
  // Analyze file structure
  const files = walkDirectory(componentPath);
  const tsFiles = files.filter(f => f.endsWith('.ts') || f.endsWith('.js'));
  const canvasFiles = files.filter(f => f.endsWith('.canvas') || f.endsWith('.json'));
  const testFiles = files.filter(f => f.includes('.test.') || f.includes('.spec.'));
  const mdFiles = files.filter(f => f.endsWith('.md'));
  
  // Analyze mathematical content
  const mathematicalContent = analyzeMathematicalContent(files);
  
  // Analyze performance characteristics
  const performance = analyzePerformance(componentPath);
  
  return {
    id: `mind-git:${config.type}:${config.category}`,
    uuid: generateUUID(),
    fingerprint: generateFingerprint(componentPath),
    title: `MIND-GIT ${config.type}: ${config.category}`,
    type: [config.type, 'implementation', 'mind-git'],
    category: config.category,
    
    // CanvasL Integration
    canvasL: {
      nodeTypes: extractCanvasLTypes(canvasFiles),
      compilationOrder: config.layer,
      spatialCoordinates: { x: config.layer * 100, y: config.dimensions[0] * 50 },
      dimensionalMapping: config.dimensions.map(d => `D${d}`),
      aalMnemonics: extractAALMnemonics(tsFiles)
    },
    
    // Mathematical Context
    mathematical: {
      foundation: mathematicalContent.foundations,
      dimensions: config.dimensions,
      hopfCompatible: mathematicalContent.hopfCompatible,
      normPreserving: mathematicalContent.normPreserving,
      polynomialDegree: mathematicalContent.polynomialDegree,
      geometricType: mathematicalContent.geometricType,
      verification: {
        coqProof: mathematicalContent.coqProofs[0],
        formalVerified: mathematicalContent.coqProofs.length > 0,
        proofComplexity: mathematicalContent.proofComplexity
      }
    },
    
    // Development Metrics
    development: {
      layer: config.layer,
      difficulty: calculateDifficulty(tsFiles),
      status: 'complete',
      completeness: calculateCompleteness(files),
      tested: testFiles.length > 0,
      coverage: testFiles.length / Math.max(tsFiles.length, 1) * 100
    },
    
    // File Statistics
    statistics: {
      totalFiles: files.length,
      tsFiles: tsFiles.length,
      canvasFiles: canvasFiles.length,
      testFiles: testFiles.length,
      linesOfCode: calculateLOC(files),
      complexity: calculateComplexity(tsFiles)
    },
    
    // Export Configuration
    export: {
      tags: [config.type, config.category, 'mind-git'],
      keywords: [config.type, config.category, 'canvasl', 'mathematics'],
      exportTargets: ['docs', 'api'],
      noRef: false,
      classified: 'public'
    }
  };
}

function walkDirectory(dir: string): string[] {
  const results: string[] = [];
  
  try {
    const list = require('fs').readdirSync(dir);
    
    for (const file of list) {
      const fullPath = path.join(dir, file);
      const stat = require('fs').statSync(fullPath);
      
      if (stat && stat.isDirectory() && !file.startsWith('.') && file !== 'node_modules') {
        results.push(...walkDirectory(fullPath));
      } else if (stat && stat.isFile()) {
        results.push(fullPath);
      }
    }
  } catch (error) {
    // Directory might not exist or be inaccessible
  }
  
  return results;
}

function analyzeMathematicalContent(files: string[]): any {
  const foundations = [];
  const coqProofs = [];
  let hopfCompatible = false;
  let normPreserving = false;
  let polynomialDegree = 0;
  let geometricType = 'cartesian';
  let proofComplexity = 0;
  
  for (const file of files) {
    try {
      const content = require('fs').readFileSync(file, 'utf8');
      
      // Check for mathematical foundations
      if (content.includes('polynomial') || content.includes('algebra')) {
        foundations.push('polynomial-algebra');
      }
      if (content.includes('identity-chain') || content.includes('norm-preserving')) {
        foundations.push('identity-chain');
      }
      if (content.includes('hopf') || content.includes('fibration')) {
        foundations.push('hopf-fibration');
        hopfCompatible = true;
      }
      
      // Check for Coq proofs
      if (file.endsWith('.v')) {
        coqProofs.push(file);
        proofComplexity += content.split('\n').length;
      }
      
      // Check for norm preservation
      if (content.includes('norm') && content.includes('preserve')) {
        normPreserving = true;
      }
      
      // Determine geometric type
      if (content.includes('projective')) geometricType = 'projective';
      else if (content.includes('affine')) geometricType = 'affine';
      else if (content.includes('fano')) geometricType = 'fano';
      
      // Extract polynomial degree
      const degreeMatch = content.match(/degree[^\d]*(\d+)/i);
      if (degreeMatch) {
        polynomialDegree = Math.max(polynomialDegree, parseInt(degreeMatch[1]));
      }
    } catch (error) {
      // File might not be readable
    }
  }
  
  return {
    foundations: [...new Set(foundations)],
    coqProofs,
    hopfCompatible,
    normPreserving,
    polynomialDegree,
    geometricType,
    proofComplexity
  };
}

function analyzePerformance(componentPath: string): any {
  // Simple performance analysis based on file structure
  return {
    complexity: 'medium',
    optimization: 'basic',
    caching: false
  };
}

function extractCanvasLTypes(files: string[]): string[] {
  const types = new Set<string>();
  
  for (const file of files) {
    try {
      const content = require('fs').readFileSync(file, 'utf8');
      const matches = content.match(/#(\w+):/g);
      if (matches) {
        for (const match of matches) {
          const type = match.replace('#', '').replace(':', '');
          types.add(type);
        }
      }
    } catch (error) {
      // File might not be readable
    }
  }
  
  return Array.from(types);
}

function extractAALMnemonics(files: string[]): string[] {
  const mnemonics = new Set<string>();
  
  for (const file of files) {
    try {
      const content = require('fs').readFileSync(file, 'utf8');
      const patterns = content.match(/#(Observe|Activate|Transform|Verify|Store|Integrate|Propagate|BackPropagate):/g);
      if (patterns) {
        for (const pattern of patterns) {
          const mnemonic = canvasLToAAL(pattern);
          mnemonics.add(mnemonic);
        }
      }
    } catch (error) {
      // File might not be readable
    }
  }
  
  return Array.from(mnemonics);
}

function canvasLToAAL(canvasLPattern: string): string {
  const mapping: Record<string, string> = {
    '#Observe:': 'MOV',
    '#Activate:': 'CALL',
    '#Transform:': 'MUL',
    '#Verify:': 'CMP',
    '#Store:': 'ADD',
    '#Integrate:': 'ADD',
    '#Propagate:': 'MOV',
    '#BackPropagate:': 'FEEDBACK'
  };
  
  return mapping[canvasLPattern] || 'MOV';
}

function calculateDifficulty(files: string[]): number {
  // Simple difficulty calculation based on file content
  let difficulty = 3; // Base difficulty
  
  for (const file of files) {
    try {
      const content = require('fs').readFileSync(file, 'utf8');
      
      // Increase difficulty for complex patterns
      if (content.includes('polynomial') || content.includes('algebra')) difficulty += 1;
      if (content.includes('coq') || content.includes('proof')) difficulty += 2;
      if (content.includes('compiler') || content.includes('ast')) difficulty += 1;
    } catch (error) {
      // File might not be readable
    }
  }
  
  return Math.min(difficulty, 10);
}

function calculateCompleteness(files: string[]): number {
  if (files.length === 0) return 0;
  
  const testFiles = files.filter(f => f.includes('.test.') || f.includes('.spec.'));
  const docFiles = files.filter(f => f.endsWith('.md'));
  
  let completeness = 50; // Base completeness
  
  if (testFiles.length > 0) completeness += 20;
  if (docFiles.length > 0) completeness += 20;
  if (files.length > 5) completeness += 10;
  
  return Math.min(completeness, 100);
}

function calculateLOC(files: string[]): number {
  let loc = 0;
  
  for (const file of files) {
    try {
      const content = require('fs').readFileSync(file, 'utf8');
      loc += content.split('\n').length;
    } catch (error) {
      // File might not be readable
    }
  }
  
  return loc;
}

function calculateComplexity(files: string[]): number {
  let complexity = 0;
  
  for (const file of files) {
    try {
      const content = require('fs').readFileSync(file, 'utf8');
      
      // Simple complexity metrics
      complexity += (content.match(/if|for|while|function|class/g) || []).length * 2;
      complexity += (content.match(/polynomial|algebra|theorem|proof/g) || []).length * 3;
      complexity += (content.match(/#\w+:/g) || []).length;
    } catch (error) {
      // File might not be readable
    }
  }
  
  return complexity;
}

function generateUUID(): string {
  return Math.random().toString(36).substring(2, 15) + Math.random().toString(36).substring(2, 15);
}

function generateFingerprint(path: string): string {
  // Simple fingerprint based on path and current time
  return require('crypto').createHash('sha256').update(path + Date.now()).digest('hex').substring(0, 16);
}

/**
 * Create AGENTS.md file for component
 * @param {string} basePath 
 * @param {string} name 
 * @param {ComponentConfig} config 
 * @param {any} metadata 
 * @returns {Promise<void>}
 */
async function createAgentsFile(basePath: string, name: string, config, metadata) {
  if (!metadata) return;
  
  const agentsPath = path.join(basePath, config.path, 'AGENTS.md');
  
  // Choose template based on component type
  const templatePath = path.join(basePath, 'metadata', 'templates', 
    config.type === 'mathematics' ? 'AGENTS.md.template' : 'AGENTS-simple.md.template');
  
  try {
    const template = await fs.readFile(templatePath, 'utf8');
    
    // Replace template variables
    let content = template
      .replace(/{{componentName}}/g, name)
      .replace(/{{layer}}/g, config.layer.toString())
      .replace(/{{category}}/g, config.category)
      .replace(/{{type}}/g, config.type)
      .replace(/{{dimensions}}/g, config.dimensions.join(', '))
      .replace(/{{mathematicalFoundation}}/g, metadata.mathematical.foundation.join(', '))
      .replace(/{{status}}/g, metadata.development.status)
      .replace(/{{completeness}}/g, metadata.development.completeness.toString())
      .replace(/{{lastUpdated}}/g, new Date().toISOString().split('T')[0]);
    
    // Add file structure
    const files = walkDirectory(path.join(basePath, config.path));
    const fileStructure = files
      .filter(f => !f.includes('node_modules'))
      .map(f => path.relative(path.join(basePath, config.path), f))
      .slice(0, 10) // Limit to first 10 files
      .join('\n');
    
    content = content.replace(/{{fileStructure}}/g, fileStructure);
    
    await fs.writeFile(agentsPath, content);
    console.log(`  📝 Created AGENTS.md for ${name}`);
  } catch (error) {
    console.warn(`  ⚠️ Failed to create AGENTS.md for ${name}: ${error.message}`);
  }
}

/**
 * Update front matter in markdown files
 * @param {string} basePath 
 * @param {string} componentPath 
 * @param {any} metadata 
 * @returns {Promise<void>}
 */
async function updateFrontMatter(basePath: string, componentPath: string, metadata) {
  if (!metadata) return;
  
  // Find key markdown files to update
  const files = walkDirectory(path.join(basePath, componentPath));
  const mdFiles = files.filter(f => f.endsWith('.md') && !f.includes('AGENTS.md'));
  
  for (const file of mdFiles.slice(0, 3)) { // Limit to first 3 files
    try {
      const content = await fs.readFile(file, 'utf8');
      
      // Check if front matter already exists
      const frontMatterMatch = content.match(/^---\n([\s\S]*?)\n---/);
      
      const newFrontMatter = `---
id: ${metadata.id}
title: "${metadata.title}"
type: ${JSON.stringify(metadata.type)}
category: ${metadata.category}
layer: ${metadata.development.layer}
dimensions: [${metadata.mathematical.dimensions.join(', ')}]
mathematicalFoundation: ${JSON.stringify(metadata.mathematical.foundation)}
hopfCompatible: ${metadata.mathematical.hopfCompatible}
normPreserving: ${metadata.mathematical.normPreserving}
status: ${metadata.development.status}
completeness: ${metadata.development.completeness}
tags: ${JSON.stringify(metadata.export.tags)}
keywords: ${JSON.stringify(metadata.export.keywords)}
lastUpdate: ${new Date().toISOString().split('T')[0]}
---`;
      
      let updatedContent;
      if (frontMatterMatch) {
        updatedContent = content.replace(/^---\n[\s\S]*?\n---/, newFrontMatter);
      } else {
        updatedContent = newFrontMatter + '\n\n' + content;
      }
      
      await fs.writeFile(file, updatedContent);
      console.log(`  📝 Updated front matter in ${path.relative(basePath, file)}`);
    } catch (error) {
      console.warn(`  ⚠️ Failed to update front matter in ${file}: ${error.message}`);
    }
  }
}

async function generateJSONLMetadata(basePath: string, name: string, metadata: any): Promise<void> {
  if (!metadata) return;
  
  const jsonlPath = path.join(basePath, '.metadata', `${name}.jsonl`);
  
  try {
    const jsonlEntry = JSON.stringify(metadata);
    await fs.writeFile(jsonlPath, jsonlEntry);
    console.log(`  📊 Generated JSONL metadata for ${name}`);
  } catch (error) {
    console.warn(`  ⚠️ Failed to generate JSONL for ${name}: ${error.message}`);
  }
}

async function generateGlobalRelationships(basePath: string): Promise<void> {
  const relationshipsPath = path.join(basePath, '.metadata', 'relationships.jsonl');
  
  try {
    const relationships = [
      { type: 'dependency', from: 'mathematicalFoundation', to: 'compiler' },
      { type: 'dependency', from: 'compiler', to: 'cli' },
      { type: 'integration', from: 'compiler', to: 'obsidianPlugin' },
      { type: 'federation', from: 'compiler', to: 'webrtcFederation' },
      { type: 'research', from: 'mathematicalFoundation', to: 'research' }
    ];
    
    const jsonlContent = relationships.map(r => JSON.stringify(r)).join('\n');
    await fs.writeFile(relationshipsPath, jsonlContent);
    console.log('  🔗 Generated global relationships');
  } catch (error) {
    console.warn(`  ⚠️ Failed to generate relationships: ${error.message}`);
  }
}

async function createMetadataIndex(basePath: string): Promise<void> {
  const indexPath = path.join(basePath, '.metadata', 'index.jsonl');
  
  try {
    const components = Object.keys(COMPONENTS);
    const indexEntries = components.map(name => ({
      name,
      path: COMPONENTS[name].path,
      type: COMPONENTS[name].type,
      layer: COMPONENTS[name].layer,
      category: COMPONENTS[name].category
    }));
    
    const jsonlContent = indexEntries.map(e => JSON.stringify(e)).join('\n');
    await fs.writeFile(indexPath, jsonlContent);
    console.log('  📋 Created metadata index');
  } catch (error) {
    console.warn(`  ⚠️ Failed to create index: ${error.message}`);
  }
}

// Run integration
integrateMetadata().catch(console.error);