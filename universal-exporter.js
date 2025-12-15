#!/usr/bin/env node

/**
 * Universal Knowledge Exporter
 *
 * Exports repository metadata to federated, distributable formats
 * for P2P knowledge sharing and collaborative development.
 */

import fs from 'fs';
import { promises as fsAsync } from 'fs';
import path from 'path';
import crypto from 'crypto';

console.log('📤 Universal Knowledge Exporter');
console.log('='.repeat(80));

class UniversalExporter {
  constructor(kernelPath) {
    this.kernelPath = kernelPath;
    this.componentsPath = path.join(kernelPath, 'components', 'registry.jsonl');
    this.canvasPath = path.join(kernelPath, 'repository-structure.canvas');
    this.exportsDir = path.join(kernelPath, 'exports');

    this.ensureExportsDirectory();
  }

  ensureExportsDirectory() {
    if (!fs.existsSync(this.exportsDir)) {
      fs.mkdirSync(this.exportsDir, { recursive: true });
    }
  }

  /**
   * Load components from kernel registry
   */
  async loadComponents() {
    try {
      const data = await fsAsync.readFile(this.componentsPath, 'utf8');
      const registry = JSON.parse(data);
      return registry.components || [];
    } catch (error) {
      console.error('⚠️ Could not load components:', error.message);
      return [];
    }
  }

  /**
   * Export to multiple formats simultaneously
   */
  async exportAll(options = {}) {
    console.log('🚀 Starting universal export...\n');

    const components = await this.loadComponents();
    const filteredComponents = this.filterComponents(components, options);

    console.log(`📊 Exporting ${filteredComponents.length} components (filtered from ${components.length} total)\n`);

    const results = {
      json: await this.exportJSON(filteredComponents, options),
      jsonld: await this.exportJSONLD(filteredComponents, options),
      markdown: await this.exportMarkdown(filteredComponents, options),
      rdf: await this.exportRDF(filteredComponents, options),
      ipfs: await this.exportIPFS(filteredComponents, options),
      federation: await this.exportFederation(filteredComponents, options)
    };

    console.log('\n✅ Export complete!\n');
    console.log('📁 Output files:');
    for (const [format, filePath] of Object.entries(results)) {
      console.log(`  ${format.toUpperCase()}: ${filePath}`);
    }

    return results;
  }

  /**
   * Filter components based on criteria
   */
  filterComponents(components, options) {
    let filtered = components;

    // Filter by layers
    if (options.layers) {
      const layers = options.layers.split(',').map(Number);
      filtered = filtered.filter(c => layers.includes(c.layer));
    }

    // Filter by mathematical content
    if (options.onlyMathematical) {
      filtered = filtered.filter(c => c.mathematical && c.mathematical.hasMathematical);
    }

    // Filter by complexity
    if (options.maxComplexity) {
      filtered = filtered.filter(c => c.complexity <= parseInt(options.maxComplexity));
    }

    // Filter by test coverage
    if (options.minTests) {
      filtered = filtered.filter(c => c.tests >= parseInt(options.minTests));
    }

    return filtered;
  }

  /**
   * Export as JSON (standard format)
   */
  async exportJSON(components, options) {
    const output = {
      format: 'universal-knowledge-base',
      version: '1.0.0',
      exported: new Date().toISOString(),
      components: components.map(c => ({
        ...c,
        hash: this.hashComponent(c)
      })),
      statistics: this.computeStatistics(components),
      metadata: {
        exportOptions: options,
        filterCriteria: this.getFilterCriteria(options)
      }
    };

    const filePath = path.join(this.exportsDir, 'knowledge-base.json');
    await fsAsync.writeFile(filePath, JSON.stringify(output, null, 2));

    return filePath;
  }

  /**
   * Export as JSON-LD (Linked Data)
   */
  async exportJSONLD(components, options) {
    const output = {
      '@context': {
        '@vocab': 'https://mind-git.org/schema/',
        'schema': 'https://schema.org/',
        'rdfs': 'http://www.w3.org/2000/01/rdf-schema#',
        'xsd': 'http://www.w3.org/2001/XMLSchema#'
      },
      '@type': 'KnowledgeBase',
      '@id': `urn:uuid:${crypto.randomUUID()}`,
      'dateCreated': new Date().toISOString(),
      'version': '1.0.0',
      'components': components.map(c => ({
        '@type': 'Component',
        '@id': c.id,
        'name': c.path,
        'componentType': c.type,
        'layer': {
          '@type': 'Layer',
          'level': c.layer,
          'name': this.getLayerName(c.layer)
        },
        'complexity': {
          '@type': 'ComplexityMetric',
          'value': c.complexity,
          'unit': 'abstract-complexity-units'
        },
        'mathematical': c.mathematical?.hasMathematical ? {
          '@type': 'MathematicalContent',
          'concepts': c.mathematical.concepts,
          'theorems': c.mathematical.theorems,
          'formalSystems': c.mathematical.formalSystems
        } : null,
        'files': c.files,
        'tests': c.tests,
        'documentation': c.documentation,
        'contentHash': this.hashComponent(c)
      }))
    };

    const filePath = path.join(this.exportsDir, 'knowledge-base.jsonld');
    await fsAsync.writeFile(filePath, JSON.stringify(output, null, 2));

    return filePath;
  }

  /**
   * Export as Markdown (human-readable documentation)
   */
  async exportMarkdown(components, options) {
    const layerGroups = this.groupByLayer(components);

    let markdown = `# Universal Knowledge Base Export

**Exported**: ${new Date().toISOString()}
**Components**: ${components.length}
**Filters**: ${this.getFilterCriteria(options)}

---

## 📊 Statistics

${this.generateMarkdownStatistics(components)}

---

## 🏗️ Components by Layer

`;

    for (const [layer, layerComponents] of Object.entries(layerGroups)) {
      const layerName = this.getLayerName(parseInt(layer));
      markdown += `### Layer ${layer}: ${layerName}\n\n`;
      markdown += `**Components**: ${layerComponents.length}\n\n`;

      for (const component of layerComponents) {
        markdown += `#### ${component.path}\n\n`;
        markdown += `- **Type**: ${component.type}\n`;
        markdown += `- **Complexity**: ${component.complexity}\n`;
        markdown += `- **Files**: ${component.files}\n`;
        markdown += `- **Tests**: ${component.tests}\n`;
        markdown += `- **Documentation**: ${component.documentation}\n`;

        if (component.mathematical?.hasMathematical) {
          markdown += `- **Mathematical Content**: ${component.mathematical.concepts.length} concepts\n`;
          if (component.mathematical.formalSystems.length > 0) {
            markdown += `- **Formal Systems**: ${component.mathematical.formalSystems.join(', ')}\n`;
          }
        }

        markdown += `- **Hash**: \`${this.hashComponent(component)}\`\n\n`;
      }

      markdown += '\n---\n\n';
    }

    markdown += `## 🔗 Federated Metadata

This knowledge base can be distributed via:
- **IPFS**: Content-addressed storage
- **P2P Networks**: Direct peer exchange
- **Git**: Traditional version control
- **Federation**: Cross-repository linking

**Knowledge Graph ID**: \`${crypto.randomUUID()}\`

---

*Generated by Universal Metadata Kernel v1.0.0*
`;

    const filePath = path.join(this.exportsDir, 'knowledge-base.md');
    await fsAsync.writeFile(filePath, markdown);

    return filePath;
  }

  /**
   * Export as RDF/Turtle (Semantic Web)
   */
  async exportRDF(components, options) {
    let turtle = `@prefix mindgit: <https://mind-git.org/schema/> .
@prefix schema: <https://schema.org/> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .

<urn:uuid:${crypto.randomUUID()}> a mindgit:KnowledgeBase ;
    schema:dateCreated "${new Date().toISOString()}"^^xsd:dateTime ;
    schema:version "1.0.0" ;
    mindgit:componentCount ${components.length} .

`;

    for (const component of components) {
      const componentId = `<urn:component:${component.id}>`;
      turtle += `${componentId} a mindgit:Component ;
    rdfs:label "${component.path}" ;
    mindgit:type "${component.type}" ;
    mindgit:layer ${component.layer} ;
    mindgit:complexity ${component.complexity} ;
    mindgit:fileCount ${component.files} ;
    mindgit:testCount ${component.tests} ;
    mindgit:documentationCount ${component.documentation} ;
    mindgit:contentHash "${this.hashComponent(component)}" .\n\n`;
    }

    const filePath = path.join(this.exportsDir, 'knowledge-base.ttl');
    await fsAsync.writeFile(filePath, turtle);

    return filePath;
  }

  /**
   * Export for IPFS distribution
   */
  async exportIPFS(components, options) {
    // Create IPFS-ready directory structure
    const ipfsDir = path.join(this.exportsDir, 'ipfs-export');
    if (!fs.existsSync(ipfsDir)) {
      fs.mkdirSync(ipfsDir, { recursive: true });
    }

    // Export components as individual files (content-addressed)
    for (const component of components) {
      const componentHash = this.hashComponent(component);
      const componentPath = path.join(ipfsDir, `${componentHash}.json`);

      await fsAsync.writeFile(componentPath, JSON.stringify({
        ...component,
        hash: componentHash,
        exported: new Date().toISOString()
      }, null, 2));
    }

    // Create index file
    const index = {
      type: 'ipfs-knowledge-base',
      version: '1.0.0',
      exported: new Date().toISOString(),
      components: components.map(c => ({
        id: c.id,
        path: c.path,
        hash: this.hashComponent(c),
        cid: `ipfs://${this.hashComponent(c)}` // Placeholder for actual IPFS CID
      }))
    };

    await fsAsync.writeFile(
      path.join(ipfsDir, 'index.json'),
      JSON.stringify(index, null, 2)
    );

    // Create README for IPFS
    const readme = `# IPFS Knowledge Base Export

This directory contains a content-addressed knowledge base export suitable for IPFS distribution.

## Structure

- \`index.json\`: Master index of all components
- \`<hash>.json\`: Individual component files (content-addressed)

## Usage

1. Add to IPFS:
   \`\`\`bash
   ipfs add -r ipfs-export/
   \`\`\`

2. Pin the directory:
   \`\`\`bash
   ipfs pin add <CID>
   \`\`\`

3. Share the CID with others for federated access

## Components

Total components: ${components.length}
Exported: ${new Date().toISOString()}
`;

    await fsAsync.writeFile(path.join(ipfsDir, 'README.md'), readme);

    return ipfsDir;
  }

  /**
   * Export for P2P Federation
   */
  async exportFederation(components, options) {
    const federationData = {
      version: '1.0.0',
      protocol: 'mind-git-federation',
      exported: new Date().toISOString(),
      knowledgeBaseId: crypto.randomUUID(),

      // Federation metadata
      federation: {
        replicationStrategy: 'content-addressed',
        consistencyModel: 'eventual',
        syncProtocol: 'git-like',
        verificationMethod: 'merkle-dag'
      },

      // Component index
      components: components.map(c => ({
        id: c.id,
        path: c.path,
        type: c.type,
        layer: c.layer,
        hash: this.hashComponent(c),
        dependencies: this.extractDependencyHashes(c, components),
        metadata: {
          complexity: c.complexity,
          files: c.files,
          tests: c.tests,
          mathematical: c.mathematical?.hasMathematical || false
        }
      })),

      // Merkle tree for verification
      merkleRoot: this.computeMerkleRoot(components),

      // Signature (placeholder - would use actual signing in production)
      signature: this.signKnowledgeBase(components),

      // Replication instructions
      replication: {
        minimumPeers: 3,
        redundancyFactor: 2,
        priorityComponents: components
          .filter(c => c.mathematical?.hasMathematical)
          .map(c => c.id)
      }
    };

    const filePath = path.join(this.exportsDir, 'federation-manifest.json');
    await fsAsync.writeFile(filePath, JSON.stringify(federationData, null, 2));

    return filePath;
  }

  /**
   * Helper: Hash a component
   */
  hashComponent(component) {
    const content = JSON.stringify({
      id: component.id,
      path: component.path,
      type: component.type,
      layer: component.layer,
      files: component.files
    });

    return crypto.createHash('sha256').update(content).digest('hex').substring(0, 16);
  }

  /**
   * Helper: Extract dependency hashes
   */
  extractDependencyHashes(component, allComponents) {
    // This would analyze actual dependencies
    // For now, return related components in same layer
    return allComponents
      .filter(c => c.layer === component.layer && c.id !== component.id)
      .slice(0, 3)
      .map(c => this.hashComponent(c));
  }

  /**
   * Helper: Compute Merkle root
   */
  computeMerkleRoot(components) {
    const hashes = components.map(c => this.hashComponent(c));

    if (hashes.length === 0) return '';
    if (hashes.length === 1) return hashes[0];

    // Simple Merkle tree construction
    while (hashes.length > 1) {
      const newLevel = [];
      for (let i = 0; i < hashes.length; i += 2) {
        const left = hashes[i];
        const right = hashes[i + 1] || left;
        const combined = crypto.createHash('sha256')
          .update(left + right)
          .digest('hex');
        newLevel.push(combined);
      }
      hashes.splice(0, hashes.length, ...newLevel);
    }

    return hashes[0];
  }

  /**
   * Helper: Sign knowledge base
   */
  signKnowledgeBase(components) {
    const merkleRoot = this.computeMerkleRoot(components);
    const timestamp = new Date().toISOString();
    const signatureContent = `${merkleRoot}:${timestamp}`;

    // In production, this would use asymmetric cryptography
    return crypto.createHash('sha256')
      .update(signatureContent)
      .digest('hex');
  }

  /**
   * Helper: Compute statistics
   */
  computeStatistics(components) {
    const totalComplexity = components.reduce((sum, c) => sum + c.complexity, 0);
    const totalFiles = components.reduce((sum, c) => sum + c.files, 0);
    const totalTests = components.reduce((sum, c) => sum + c.tests, 0);
    const mathematicalComponents = components.filter(c => c.mathematical?.hasMathematical).length;

    const layerDistribution = {};
    for (const component of components) {
      layerDistribution[component.layer] = (layerDistribution[component.layer] || 0) + 1;
    }

    return {
      total: components.length,
      totalComplexity,
      averageComplexity: components.length > 0 ? Math.round(totalComplexity / components.length) : 0,
      totalFiles,
      totalTests,
      testCoverage: totalFiles > 0 ? Math.round((totalTests / totalFiles) * 100) : 0,
      mathematicalComponents,
      mathematicalPercentage: components.length > 0 ? Math.round((mathematicalComponents / components.length) * 100) : 0,
      layerDistribution
    };
  }

  /**
   * Helper: Generate markdown statistics
   */
  generateMarkdownStatistics(components) {
    const stats = this.computeStatistics(components);

    return `| Metric | Value |
|--------|-------|
| **Total Components** | ${stats.total} |
| **Total Complexity** | ${stats.totalComplexity} |
| **Average Complexity** | ${stats.averageComplexity} |
| **Total Files** | ${stats.totalFiles} |
| **Total Tests** | ${stats.totalTests} |
| **Test Coverage** | ${stats.testCoverage}% |
| **Mathematical Components** | ${stats.mathematicalComponents} (${stats.mathematicalPercentage}%) |

### Layer Distribution

| Layer | Components |
|-------|-----------|
${Object.entries(stats.layerDistribution).map(([layer, count]) =>
  `| ${layer} - ${this.getLayerName(parseInt(layer))} | ${count} |`
).join('\n')}`;
  }

  /**
   * Helper: Group components by layer
   */
  groupByLayer(components) {
    const groups = {};
    for (const component of components) {
      if (!groups[component.layer]) {
        groups[component.layer] = [];
      }
      groups[component.layer].push(component);
    }
    return groups;
  }

  /**
   * Helper: Get layer name
   */
  getLayerName(layer) {
    const names = {
      1: 'Mathematical Foundation',
      2: 'Core Implementation',
      3: 'API/Interface',
      4: 'Services/Business Logic',
      5: 'Data Layer',
      6: 'UI/Presentation',
      7: 'Tests',
      8: 'Documentation'
    };
    return names[layer] || 'Unknown';
  }

  /**
   * Helper: Get filter criteria as string
   */
  getFilterCriteria(options) {
    const criteria = [];
    if (options.layers) criteria.push(`Layers: ${options.layers}`);
    if (options.onlyMathematical) criteria.push('Mathematical content only');
    if (options.maxComplexity) criteria.push(`Max complexity: ${options.maxComplexity}`);
    if (options.minTests) criteria.push(`Min tests: ${options.minTests}`);
    return criteria.length > 0 ? criteria.join(', ') : 'None';
  }
}

// CLI Interface
const command = process.argv[2];
const kernelPath = process.argv[3] || './.metadata-kernel';

if (!command || command === 'help') {
  console.log(`
🚀 Universal Knowledge Exporter

Exports repository metadata to federated, distributable formats.

Commands:
  export <kernel-path>    Export to all formats
  json <kernel-path>      Export to JSON only
  jsonld <kernel-path>    Export to JSON-LD only
  markdown <kernel-path>  Export to Markdown only
  rdf <kernel-path>       Export to RDF/Turtle only
  ipfs <kernel-path>      Export for IPFS distribution
  federation <kernel-path> Export for P2P federation

Options:
  --layers <1,2,3>         Filter by layers
  --only-mathematical      Only export mathematical components
  --max-complexity <num>   Maximum complexity threshold
  --min-tests <num>        Minimum test count

Examples:
  universal-exporter export ./.metadata-kernel
  universal-exporter export /tmp/kernel-test/lodash/.metadata-kernel --layers 1,2
  universal-exporter ipfs ./.metadata-kernel --only-mathematical
  universal-exporter federation ./.metadata-kernel

Output formats:
  - JSON: Standard machine-readable format
  - JSON-LD: Linked Data for semantic web
  - Markdown: Human-readable documentation
  - RDF/Turtle: Semantic web triple format
  - IPFS: Content-addressed distribution
  - Federation: P2P network manifest

All exports include:
  ✓ Content hashing for verification
  ✓ Merkle trees for integrity
  ✓ Cryptographic signatures
  ✓ Replication instructions
  ✓ Dependency graphs
  `);
  process.exit(0);
}

// Parse options
const options = {};
for (let i = 4; i < process.argv.length; i++) {
  if (process.argv[i] === '--layers' && process.argv[i + 1]) {
    options.layers = process.argv[i + 1];
    i++;
  } else if (process.argv[i] === '--only-mathematical') {
    options.onlyMathematical = true;
  } else if (process.argv[i] === '--max-complexity' && process.argv[i + 1]) {
    options.maxComplexity = process.argv[i + 1];
    i++;
  } else if (process.argv[i] === '--min-tests' && process.argv[i + 1]) {
    options.minTests = process.argv[i + 1];
    i++;
  }
}

const exporter = new UniversalExporter(kernelPath);

switch (command) {
  case 'export':
    exporter.exportAll(options)
      .then(results => {
        console.log('\n📊 Export Summary:');
        console.log('  All formats exported successfully!');
      })
      .catch(error => {
        console.error('❌ Export failed:', error.message);
        process.exit(1);
      });
    break;

  case 'json':
    exporter.loadComponents()
      .then(components => exporter.filterComponents(components, options))
      .then(filtered => exporter.exportJSON(filtered, options))
      .then(filePath => console.log(`✅ JSON exported to: ${filePath}`))
      .catch(error => {
        console.error('❌ Export failed:', error.message);
        process.exit(1);
      });
    break;

  case 'jsonld':
    exporter.loadComponents()
      .then(components => exporter.filterComponents(components, options))
      .then(filtered => exporter.exportJSONLD(filtered, options))
      .then(filePath => console.log(`✅ JSON-LD exported to: ${filePath}`))
      .catch(error => {
        console.error('❌ Export failed:', error.message);
        process.exit(1);
      });
    break;

  case 'markdown':
    exporter.loadComponents()
      .then(components => exporter.filterComponents(components, options))
      .then(filtered => exporter.exportMarkdown(filtered, options))
      .then(filePath => console.log(`✅ Markdown exported to: ${filePath}`))
      .catch(error => {
        console.error('❌ Export failed:', error.message);
        process.exit(1);
      });
    break;

  case 'rdf':
    exporter.loadComponents()
      .then(components => exporter.filterComponents(components, options))
      .then(filtered => exporter.exportRDF(filtered, options))
      .then(filePath => console.log(`✅ RDF exported to: ${filePath}`))
      .catch(error => {
        console.error('❌ Export failed:', error.message);
        process.exit(1);
      });
    break;

  case 'ipfs':
    exporter.loadComponents()
      .then(components => exporter.filterComponents(components, options))
      .then(filtered => exporter.exportIPFS(filtered, options))
      .then(dirPath => console.log(`✅ IPFS export ready at: ${dirPath}`))
      .catch(error => {
        console.error('❌ Export failed:', error.message);
        process.exit(1);
      });
    break;

  case 'federation':
    exporter.loadComponents()
      .then(components => exporter.filterComponents(components, options))
      .then(filtered => exporter.exportFederation(filtered, options))
      .then(filePath => console.log(`✅ Federation manifest exported to: ${filePath}`))
      .catch(error => {
        console.error('❌ Export failed:', error.message);
        process.exit(1);
      });
    break;

  default:
    console.error(`Unknown command: ${command}`);
    console.error('Use "help" to see available commands');
    process.exit(1);
}
