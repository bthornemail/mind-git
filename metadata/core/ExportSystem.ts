import { promises as fs } from 'fs';
import path from 'path';
import { FileMetadata } from './MetadataService.js';

export interface ExportRule {
  include: string[];
  exclude: string[];
  format: 'markdown' | 'json' | 'typescript' | 'pdf';
}

export interface ExportOptions {
  minCompleteness?: number;
  onlyVerified?: boolean;
  layers?: number[];
  outputPath?: string;
}

export class ExportSystem {
  private metadataDir: string;
  private exportRules: Record<string, ExportRule>;
  
  constructor(private basePath: string) {
    this.metadataDir = path.join(basePath, '.metadata');
    this.exportRules = this.loadExportRules();
  }
  
  private loadExportRules(): Record<string, ExportRule> {
    return {
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
  
  async export(target: string, options: ExportOptions = {}): Promise<string> {
    console.log(`\n📤 Exporting for target: ${target}`);
    
    const rules = this.exportRules[target];
    if (!rules) {
      throw new Error(`Unknown export target: ${target}`);
    }
    
    // Load all metadata
    const metadata = await this.loadAllMetadata();
    
    // Filter based on tags and options
    const filtered = this.filterMetadata(metadata, rules, options);
    
    // Generate export
    const result = await this.generateExport(filtered, rules.format, options);
    
    // Save export
    const outputPath = this.saveExport(result, target, rules.format, options.outputPath);
    
    console.log(`✅ Exported ${filtered.length} components to ${outputPath}`);
    return outputPath;
  }
  
  private async loadAllMetadata(): Promise<FileMetadata[]> {
    const indexPath = path.join(this.metadataDir, 'index.jsonl');
    if (!require('fs').existsSync(indexPath)) {
      return [];
    }
    
    const content = await fs.readFile(indexPath, 'utf8');
    const entries = content.split('\n')
      .filter(line => line.trim())
      .map(line => JSON.parse(line));
    
    // Load full metadata for each entry
    const fullMetadata: FileMetadata[] = [];
    for (const entry of entries) {
      const metadataPath = path.join(this.metadataDir, '.hidden', 'registry', `${entry.path.replace(/[^a-zA-Z0-9]/g, '-')}.json`);
      if (require('fs').existsSync(metadataPath)) {
        const metadataContent = await fs.readFile(metadataPath, 'utf8');
        fullMetadata.push(JSON.parse(metadataContent));
      }
    }
    
    return fullMetadata;
  }
  
  private filterMetadata(metadata: FileMetadata[], rules: ExportRule, options: ExportOptions): FileMetadata[] {
    return metadata.filter(item => {
      // Check include tags
      if (rules.include.length > 0) {
        const hasIncludeTag = rules.include.some(tag => 
          item.export.tags.includes(tag.replace('#EXPORT_TAGS: ', '').trim())
        );
        if (!hasIncludeTag) return false;
      }
      
      // Check exclude tags
      const hasExcludeTag = rules.exclude.some(tag => {
        const tagName = tag.replace('#', '').split(':')[0].toLowerCase();
        const tagValue = tag.split(':')[1]?.trim();
        
        if (tagName === 'no_ref' && tagValue === 'true') {
          return item.export.noRef === true;
        }
        if (tagName === 'classified') {
          return item.export.classified === tagValue;
        }
        if (tagName === 'draft' && tagValue === 'true') {
          return item.development.status === 'draft';
        }
        
        return false;
      });
      
      if (hasExcludeTag) return false;
      
      // Apply additional filters
      if (options.minCompleteness && item.development.completeness < options.minCompleteness) {
        return false;
      }
      
      if (options.onlyVerified && !item.mathematical.verification.formalVerified) {
        return false;
      }
      
      if (options.layers && !options.layers.includes(item.development.layer)) {
        return false;
      }
      
      return true;
    });
  }
  
  private async generateExport(metadata: FileMetadata[], format: string, options: ExportOptions): Promise<string> {
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
  
  private generateMarkdownExport(metadata: FileMetadata[], options: ExportOptions): string {
    let output = `# MIND-GIT System Documentation\n\n`;
    output += `*Generated: ${new Date().toISOString()}*\n`;
    output += `*Total Components: ${metadata.length}*\n\n`;
    
    // Group by layer
    const byLayer = metadata.reduce((acc, item) => {
      const layer = item.development.layer || 0;
      if (!acc[layer]) acc[layer] = [];
      acc[layer].push(item);
      return acc;
    }, {} as Record<number, FileMetadata[]>);
    
    for (const [layer, items] of Object.entries(byLayer).sort()) {
      output += `## Layer ${layer}: ${this.getLayerName(parseInt(layer))}\n\n`;
      
      for (const item of items) {
        output += this.generateComponentMarkdown(item);
      }
    }
    
    return output;
  }
  
  private generateComponentMarkdown(item: FileMetadata): string {
    return `
### ${item.title}

**ID**: ${item.id}  
**Status**: ${item.development.status} | **Completeness**: ${item.development.completeness}%  
**Layer**: ${item.development.layer} | **Dimensions**: ${item.mathematical.dimensions.join(', ')}

#### Mathematical Foundation
${item.mathematical.foundation.length > 0 ? item.mathematical.foundation.map(f => `- ${f}`).join('\n') : 'None specified'}

#### CanvasL Integration
- **Node Types**: ${item.canvasL.nodeTypes.join(', ') || 'N/A'}
- **AAL Mnemonics**: ${item.canvasL.aalMnemonics.join(', ') || 'N/A'}
- **Spatial Coordinates**: (${item.canvasL.spatialCoordinates.x}, ${item.canvasL.spatialCoordinates.y})

#### Verification Status
${item.mathematical.verification.formalVerified ? '✅ Formally Verified' : '⚠️ Not Formally Verified'}
${item.mathematical.verification.coqProof ? `- Coq Proof: ${item.mathematical.verification.coqProof}` : ''}

#### Export Tags
${item.export.tags.length > 0 ? item.export.tags.map(t => `\`${t}\``).join(' ') : 'No tags'}

---
`;
  }
  
  private generateJSONExport(metadata: FileMetadata[], options: ExportOptions): string {
    const exportData = {
      generated: new Date().toISOString(),
      totalComponents: metadata.length,
      components: metadata.map(item => ({
        id: item.id,
        title: item.title,
        type: item.type,
        category: item.category,
        layer: item.development.layer,
        status: item.development.status,
        completeness: item.development.completeness,
        mathematical: {
          foundation: item.mathematical.foundation,
          dimensions: item.mathematical.dimensions,
          verified: item.mathematical.verification.formalVerified
        },
        canvasL: {
          nodeTypes: item.canvasL.nodeTypes,
          aalMnemonics: item.canvasL.aalMnemonics
        },
        export: {
          tags: item.export.tags,
          keywords: item.export.keywords
        }
      }))
    };
    
    return JSON.stringify(exportData, null, 2);
  }
  
  private generateTypeScriptExport(metadata: FileMetadata[], options: ExportOptions): string {
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
      output += `    title: '${item.title.replace(/'/g, "\\'")}',\n`;
      output += `    type: ${JSON.stringify(item.type)},\n`;
      output += `    category: '${item.category}',\n`;
      output += `    layer: ${item.development.layer},\n`;
      output += `    status: '${item.development.status}',\n`;
      output += `    completeness: ${item.development.completeness}\n`;
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
  
  private generatePDFExport(metadata: FileMetadata[], options: ExportOptions): string {
    // For now, return markdown that can be converted to PDF
    return this.generateMarkdownExport(metadata, options);
  }
  
  private getLayerName(layer: number): string {
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
  
  private saveExport(content: string, target: string, format: string, outputPath?: string): string {
    const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    const extension = this.getFileExtension(format);
    const filename = `${target}-export-${timestamp}.${extension}`;
    
    const exportDir = outputPath || path.join(this.metadataDir, 'exports');
    if (!require('fs').existsSync(exportDir)) {
      require('fs').mkdirSync(exportDir, { recursive: true });
    }
    
    const fullPath = path.join(exportDir, filename);
    require('fs').writeFileSync(fullPath, content);
    
    return fullPath;
  }
  
  private getFileExtension(format: string): string {
    const extensions: Record<string, string> = {
      'markdown': 'md',
      'json': 'json',
      'typescript': 'ts',
      'pdf': 'pdf'
    };
    
    return extensions[format] || 'txt';
  }
}