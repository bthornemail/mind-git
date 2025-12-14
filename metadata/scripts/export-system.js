#!/usr/bin/env node

/**
 * MIND-GIT Export System with Org-Mode Style Tags
 * 
 * Enables selective documentation export based on metadata
 */

import { promises as fs } from 'fs';
import path from 'path';
import { parse as parseYAML } from 'yaml';

console.log('📤 MIND-GIT Export System');
console.log('='.repeat(80));

class ExportSystem {
  private metadataDir: string;
  private exportRules: any;
  
  constructor() {
    this.metadataDir = path.join(process.cwd(), '.metadata');
    this.exportRules = this.loadExportRules();
  }
  
  private loadExportRules(): any {
    return {
      // Export targets
      'docs': {
        include: ['#EXPORT_TAGS: docs', '#EXPORT_TAGS: api'],
        exclude: ['#NO_REF: true', '#CLASSIFIED: internal'],
        format: 'markdown'
      },
      'api': {
        include: ['#EXPORT_TAGS: api'],
        exclude: ['#DRAFT: true', '#CLASSIFIED: internal'],
        format: 'json'
      },
      'npm': {
        include: ['#EXPORT_TAGS: npm'],
        exclude: ['#CLASSIFIED: internal', '#DRAFT: true'],
        format: 'typescript'
      },
      'research': {
        include: ['#EXPORT_TAGS: research', '#EXPORT_TAGS: mathematics'],
        exclude: ['#CLASSIFIED: restricted'],
        format: 'pdf'
      },
      'all': {
        include: [],
        exclude: ['#CLASSIFIED: restricted', '#NO_REF: true'],
        format: 'markdown'
      }
    };
  }
  
  async export(target: string, options: any = {}) {
    console.log(`\n📤 Exporting for target: ${target}`);
    
    const rules = this.exportRules[target];
    if (!rules) {
      throw new Error(`Unknown export target: ${target}`);
    }
    
    // Load all metadata
    const metadata = await this.loadAllMetadata();
    
    // Filter based on tags
    const filtered = this.filterMetadata(metadata, rules, options);
    
    // Generate export
    const result = await this.generateExport(filtered, rules.format, options);
    
    // Save export
    const outputPath = this.saveExport(result, target, rules.format);
    
    console.log(`✅ Exported ${filtered.length} components to ${outputPath}`);
    return outputPath;
  }
  
  filterMetadata(metadata: any[], rules: any, options: any): any[] {
    return metadata.filter(item => {
      // Check include tags
      if (rules.include.length > 0) {
        const hasIncludeTag = rules.include.some(tag => 
          item.export?.tags?.includes(tag.replace('#EXPORT_TAGS: ', '').trim())
        );
        if (!hasIncludeTag) return false;
      }
      
      // Check exclude tags
      const hasExcludeTag = rules.exclude.some(tag => {
        const tagName = tag.replace('#', '').split(':')[0].toLowerCase();
        const tagValue = tag.split(':')[1]?.trim();
        
        if (tagName === 'no_ref' && tagValue === 'true') {
          return item.export?.noRef === true;
        }
        if (tagName === 'classified') {
          return item.export?.classified === tagValue;
        }
        if (tagName === 'draft' && tagValue === 'true') {
          return item.development?.status === 'draft';
        }
        
        return false;
      });
      
      if (hasExcludeTag) return false;
      
      // Apply additional filters
      if (options.minCompleteness && item.development?.completeness < options.minCompleteness) {
        return false;
      }
      
      if (options.onlyVerified && !item.mathematical?.verification?.formalVerified) {
        return false;
      }
      
      if (options.layers && !options.layers.includes(item.development?.layer)) {
        return false;
      }
      
      return true;
    });
  }
  
  async generateExport(metadata: any[], format: string, options: any): Promise<string> {
    switch (format) {
      case 'markdown':
        return this.generateMarkdownExport(metadata, options);
      case 'json':
        return this.generateJSONExport(metadata, options);
      case 'typescript':
        return this.generateTypeScriptExport(metadata, options);
      case 'pdf':
        return this.generatePDFExport(metadata, options);
      default:
        return JSON.stringify(metadata, null, 2);
    }
  }
  
  generateMarkdownExport(metadata: any[], options: any): string {
    let output = `# MIND-GIT System Documentation\n\n`;
    output += `*Generated: ${new Date().toISOString()}*\n`;
    output += `*Total Components: ${metadata.length}*\n\n`;
    
    // Group by layer
    const byLayer = metadata.reduce((acc, item) => {
      const layer = item.development?.layer || 0;
      if (!acc[layer]) acc[layer] = [];
      acc[layer].push(item);
      return acc;
    }, {} as Record<number, any[]>);
    
    for (const [layer, items] of Object.entries(byLayer).sort()) {
      output += `## Layer ${layer}: ${this.getLayerName(parseInt(layer))}\n\n`;
      
      for (const item of items) {
        output += this.generateComponentMarkdown(item);
      }
    }
    
    return output;
  }
  
  generateComponentMarkdown(item: any): string {
    return `
### ${item.title || item.id}

**ID**: ${item.id}  
**Status**: ${item.development?.status || 'unknown'} | **Completeness**: ${item.development?.completeness || 0}%  
**Layer**: ${item.development?.layer || 0} | **Dimensions**: ${item.mathematical?.dimensions?.join(', ') || 'N/A'}

#### Mathematical Foundation
${item.mathematical?.foundation?.length > 0 ? item.mathematical.foundation.map((f: string) => `- ${f}`).join('\n') : 'None specified'}

#### CanvasL Integration
- **Node Types**: ${item.canvasL?.nodeTypes?.join(', ') || 'N/A'}
- **AAL Mnemonics**: ${item.canvasL?.aalMnemonics?.join(', ') || 'N/A'}
- **Spatial Coordinates**: (${item.canvasL?.spatialCoordinates?.x || 0}, ${item.canvasL?.spatialCoordinates?.y || 0})

#### Verification Status
${item.mathematical?.verification?.formalVerified ? '✅ Formally Verified' : '⚠️ Not Formally Verified'}
${item.mathematical?.verification?.coqProof ? `- Coq Proof: ${item.mathematical.verification.coqProof}` : ''}

#### Export Tags
${item.export?.tags?.length > 0 ? item.export.tags.map((t: string) => `\`${t}\``).join(' ') : 'No tags'}

---
`;
  }
  
  generateJSONExport(metadata: any[], options: any): string {
    const exportData = {
      generated: new Date().toISOString(),
      totalComponents: metadata.length,
      components: metadata.map(item => ({
        id: item.id,
        title: item.title,
        type: item.type,
        category: item.category,
        layer: item.development?.layer,
        status: item.development?.status,
        completeness: item.development?.completeness,
        mathematical: {
          foundation: item.mathematical?.foundation,
          dimensions: item.mathematical?.dimensions,
          verified: item.mathematical?.verification?.formalVerified
        },
        canvasL: {
          nodeTypes: item.canvasL?.nodeTypes,
          aalMnemonics: item.canvasL?.aalMnemonics
        },
        export: {
          tags: item.export?.tags,
          keywords: item.export?.keywords
        }
      }))
    };
    
    return JSON.stringify(exportData, null, 2);
  }
  
  generateTypeScriptExport(metadata: any[], options: any): string {
    let output = `// Generated MIND-GIT API Types\n`;
    output += `// Generated: ${new Date().toISOString()}\n\n`;
    
    // Generate interfaces
    output += `export interface MindGitComponent {\n`;
    output += `  id: string;\n`;
    output += `  title: string;\n`;
    output += `  type: string[];\n`;
    output += `  category: string;\n`;
    output += `  layer: number;\n`;
    output += `  status: string;\n`;
    output += `  completeness: number;\n`;
    output += `}\n\n`;
    
    // Generate component registry
    output += `export const COMPONENT_REGISTRY: Record<string, MindGitComponent> = {\n`;
    
    for (const item of metadata) {
      output += `  '${item.id}': {\n`;
      output += `    id: '${item.id}',\n`;
      output += `    title: '${(item.title || item.id).replace(/'/g, "\\'")}',\n`;
      output += `    type: ${JSON.stringify(item.type || [])},\n`;
      output += `    category: '${item.category || 'unknown'}',\n`;
      output += `    layer: ${item.development?.layer || 0},\n`;
      output += `    status: '${item.development?.status || 'unknown'}',\n`;
      output += `    completeness: ${item.development?.completeness || 0}\n`;
      output += `  },\n`;
    }
    
    output += `};\n\n`;
    
    // Generate lookup functions
    output += `export function getComponentsByLayer(layer: number): MindGitComponent[] {\n`;
    output += `  return Object.values(COMPONENT_REGISTRY).filter(c => c.layer === layer);\n`;
    output += `}\n\n`;
    
    output += `export function getComponentsByType(type: string): MindGitComponent[] {\n`;
    output += `  return Object.values(COMPONENT_REGISTRY).filter(c => c.type.includes(type));\n`;
    output += `}\n\n`;
    
    output += `export function getVerifiedComponents(): MindGitComponent[] {\n`;
    output += `  return Object.values(COMPONENT_REGISTRY).filter(c => c.completeness >= 90);\n`;
    output += `}\n`;
    
    return output;
  }
  
  generatePDFExport(metadata: any[], options: any): string {
    // For now, return markdown that can be converted to PDF
    return this.generateMarkdownExport(metadata, options);
  }
  
  getLayerName(layer: number): string {
    const layerNames: Record<number, string> = {
      1: 'Mathematical Foundation',
      2: 'Theoretical Framework',
      3: 'System Architecture',
      4: 'Implementation Details',
      5: 'Security & Production',
      6: 'Integration & Ecosystem',
      7: 'Research & Development'
    };
    
    return layerNames[layer] || `Layer ${layer}`;
  }
  
  async loadAllMetadata(): Promise<any[]> {
    const indexPath = path.join(this.metadataDir, 'index.jsonl');
    if (!require('fs').existsSync(indexPath)) {
      return [];
    }
    
    const content = await fs.readFile(indexPath, 'utf8');
    return content.split('\n')
      .filter(line => line.trim())
      .map(line => JSON.parse(line));
  }
  
  saveExport(content: string, target: string, format: string): string {
    const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    const extension = this.getFileExtension(format);
    const filename = `${target}-export-${timestamp}.${extension}`;
    
    const exportDir = path.join(this.metadataDir, 'exports');
    if (!require('fs').existsSync(exportDir)) {
      require('fs').mkdirSync(exportDir, { recursive: true });
    }
    
    const fullPath = path.join(exportDir, filename);
    require('fs').writeFileSync(fullPath, content);
    
    return fullPath;
  }
  
  getFileExtension(format: string): string {
    const extensions: Record<string, string> = {
      'markdown': 'md',
      'json': 'json',
      'typescript': 'ts',
      'pdf': 'pdf'
    };
    
    return extensions[format] || 'txt';
  }
}

// Command line interface
const exportSystem = new ExportSystem();

const command = process.argv[2];
const target = process.argv[3];

switch (command) {
  case 'export':
    exportSystem.export(target, {
      minCompleteness: 80,
      onlyVerified: true
    });
    break;
    
  case 'list':
    console.log('Available export targets:');
    Object.keys(exportSystem['exportRules']).forEach(target => {
      console.log(`  - ${target}`);
    });
    break;
    
  default:
    console.log('Usage:');
    console.log('  node export-system.js export <target>');
    console.log('  node export-system.js list');
    console.log('\nExamples:');
    console.log('  node export-system.js export docs');
    console.log('  node export-system.js export api');
    console.log('  node export-system.js export npm');
    console.log('  node export-system.js export research');
}