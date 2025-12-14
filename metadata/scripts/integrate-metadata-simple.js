#!/usr/bin/env node

/**
 * MIND-GIT Metadata Integration Script (Simplified)
 * 
 * Integrates unified metadata framework with existing components
 */

import fs from 'fs';
import { promises as fsAsync } from 'fs';
import path from 'path';
import { execSync } from 'child_process';
import crypto from 'crypto';

console.log('🧠 MIND-GIT Metadata Integration');
console.log('='.repeat(80));

// Configuration based on existing codebase structure
const COMPONENTS = {
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
  
  const basePath = path.resolve(process.cwd(), '..');
  
  // Ensure metadata directories exist
  ensureMetadataDirectories(basePath);
  
  for (const [name, config] of Object.entries(COMPONENTS)) {
    console.log(`\n🔍 Analyzing ${name}...`);
    
    try {
      // 1. Generate component metadata
      const metadata = await analyzeComponent(basePath, name, config);
      
      if (metadata) {
        // 2. Create AGENTS.md
        await createAgentsFile(basePath, name, config, metadata);
        
        // 3. Update front matter in key files
        await updateFrontMatter(basePath, config.path, metadata);
        
        // 4. Generate JSONL metadata
        await generateJSONLMetadata(basePath, name, metadata);
        
        console.log(`✅ ${name}: Metadata integrated`);
      } else {
        console.log(`⚠️ ${name}: No metadata generated`);
      }
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

function ensureMetadataDirectories(basePath) {
  const dirs = [
    path.join(basePath, '.metadata'),
    path.join(basePath, '.metadata', '.hidden'),
    path.join(basePath, '.metadata', '.hidden', 'cache'),
    path.join(basePath, '.metadata', '.hidden', 'registry'),
    path.join(basePath, '.metadata', 'schemas'),
    path.join(basePath, '.metadata', 'templates'),
    path.join(basePath, '.metadata', 'exports')
  ];
  
  dirs.forEach(dir => {
    if (!fs.existsSync(dir)) {
      fs.mkdirSync(dir, { recursive: true });
    }
  });
}

/**
 * Analyze component and generate metadata
 * @param {string} basePath 
 * @param {string} name 
 * @param {ComponentConfig} config 
 * @returns {Promise<any>}
 */
async function analyzeComponent(basePath, name, config) {
  const componentPath = path.join(basePath, config.path);
  
  // Check if path exists
  if (!fs.existsSync(componentPath)) {
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

/**
 * Walk directory and return all files
 * @param {string} dir 
 * @returns {string[]}
 */
function walkDirectory(dir) {
  const results = [];
  
  try {
    const list = fs.readdirSync(dir);
    
    for (const file of list) {
      const fullPath = path.join(dir, file);
      const stat = fs.statSync(fullPath);
      
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

/**
 * Analyze mathematical content in files
 * @param {string[]} files 
 * @returns {any}
 */
function analyzeMathematicalContent(files) {
  const foundations = [];
  const coqProofs = [];
  let hopfCompatible = false;
  let normPreserving = false;
  let polynomialDegree = 0;
  let geometricType = 'cartesian';
  let proofComplexity = 0;
  
  for (const file of files) {
    try {
      const content = fs.readFileSync(file, 'utf8');
      
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

/**
 * Extract CanvasL types from files
 * @param {string[]} files 
 * @returns {string[]}
 */
function extractCanvasLTypes(files) {
  const types = new Set();
  
  for (const file of files) {
    try {
      const content = fs.readFileSync(file, 'utf8');
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

/**
 * Extract AAL mnemonics from files
 * @param {string[]} files 
 * @returns {string[]}
 */
function extractAALMnemonics(files) {
  const mnemonics = new Set();
  
  for (const file of files) {
    try {
      const content = fs.readFileSync(file, 'utf8');
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

/**
 * Convert CanvasL pattern to AAL mnemonic
 * @param {string} canvasLPattern 
 * @returns {string}
 */
function canvasLToAAL(canvasLPattern) {
  const mapping = {
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

/**
 * Calculate difficulty score for files
 * @param {string[]} files 
 * @returns {number}
 */
function calculateDifficulty(files) {
  // Simple difficulty calculation based on file content
  let difficulty = 3; // Base difficulty
  
  for (const file of files) {
    try {
      const content = fs.readFileSync(file, 'utf8');
      
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

/**
 * Calculate completeness percentage for files
 * @param {string[]} files 
 * @returns {number}
 */
function calculateCompleteness(files) {
  if (files.length === 0) return 0;
  
  const testFiles = files.filter(f => f.includes('.test.') || f.includes('.spec.'));
  const docFiles = files.filter(f => f.endsWith('.md'));
  
  let completeness = 50; // Base completeness
  
  if (testFiles.length > 0) completeness += 20;
  if (docFiles.length > 0) completeness += 20;
  if (files.length > 5) completeness += 10;
  
  return Math.min(completeness, 100);
}

/**
 * Calculate lines of code for files
 * @param {string[]} files 
 * @returns {number}
 */
function calculateLOC(files) {
  let loc = 0;
  
  for (const file of files) {
    try {
      const content = fs.readFileSync(file, 'utf8');
      loc += content.split('\n').length;
    } catch (error) {
      // File might not be readable
    }
  }
  
  return loc;
}

/**
 * Calculate complexity score for files
 * @param {string[]} files 
 * @returns {number}
 */
function calculateComplexity(files) {
  let complexity = 0;
  
  for (const file of files) {
    try {
      const content = fs.readFileSync(file, 'utf8');
      
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

/**
 * Generate UUID
 * @returns {string}
 */
function generateUUID() {
  return Math.random().toString(36).substring(2, 15) + Math.random().toString(36).substring(2, 15);
}

/**
 * Generate fingerprint for path
 * @param {string} path 
 * @returns {string}
 */
function generateFingerprint(path) {
  // Simple fingerprint based on path and current time
  return crypto.createHash('sha256').update(path + Date.now()).digest('hex').substring(0, 16);
}

/**
 * Create AGENTS.md file for component
 * @param {string} basePath 
 * @param {string} name 
 * @param {ComponentConfig} config 
 * @param {any} metadata 
 * @returns {Promise<void>}
 */
async function createAgentsFile(basePath, name, config, metadata) {
  if (!metadata) return;
  
  const agentsPath = path.join(basePath, config.path, 'AGENTS.md');
  
  // Choose template based on component type
  const templatePath = path.join(basePath, 'metadata', 'templates', 
    config.type === 'mathematics' ? 'AGENTS.md.template' : 'AGENTS-simple.md.template');
  
  try {
    const template = fs.readFileSync(templatePath, 'utf8');
    
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
    
    await fsAsync.writeFile(agentsPath, content);
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
async function updateFrontMatter(basePath, componentPath, metadata) {
  if (!metadata) return;
  
  // Find key markdown files to update
  const files = walkDirectory(path.join(basePath, componentPath));
  const mdFiles = files.filter(f => f.endsWith('.md') && !f.includes('AGENTS.md'));
  
  for (const file of mdFiles.slice(0, 3)) { // Limit to first 3 files
    try {
      const content = await fsAsync.readFile(file, 'utf8');
      
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
      
      await fsAsync.writeFile(file, updatedContent);
      console.log(`  📝 Updated front matter in ${path.relative(basePath, file)}`);
    } catch (error) {
      console.warn(`  ⚠️ Failed to update front matter in ${file}: ${error.message}`);
    }
  }
}

/**
 * Generate JSONL metadata file
 * @param {string} basePath 
 * @param {string} name 
 * @param {any} metadata 
 * @returns {Promise<void>}
 */
async function generateJSONLMetadata(basePath, name, metadata) {
  if (!metadata) return;
  
  const jsonlPath = path.join(basePath, '.metadata', `${name}.jsonl`);
  
  try {
    const jsonlEntry = JSON.stringify(metadata);
    await fsAsync.writeFile(jsonlPath, jsonlEntry);
    console.log(`  📊 Generated JSONL metadata for ${name}`);
  } catch (error) {
    console.warn(`  ⚠️ Failed to generate JSONL for ${name}: ${error.message}`);
  }
}

/**
 * Generate global relationships file
 * @param {string} basePath 
 * @returns {Promise<void>}
 */
async function generateGlobalRelationships(basePath) {
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
    await fsAsync.writeFile(relationshipsPath, jsonlContent);
    console.log('  🔗 Generated global relationships');
  } catch (error) {
    console.warn(`  ⚠️ Failed to generate relationships: ${error.message}`);
  }
}

/**
 * Create metadata index file
 * @param {string} basePath 
 * @returns {Promise<void>}
 */
async function createMetadataIndex(basePath) {
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
    await fsAsync.writeFile(indexPath, jsonlContent);
    console.log('  📋 Created metadata index');
  } catch (error) {
    console.warn(`  ⚠️ Failed to create index: ${error.message}`);
  }
}

// Run integration
integrateMetadata().catch(console.error);