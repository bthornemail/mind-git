import { promises as fs } from 'fs';
import path from 'path';
import crypto from 'crypto';
import { parse as parseYAML, stringify as stringifyYAML } from 'yaml';

export interface CanvasLMetadata {
  nodeTypes: string[];
  compilationOrder: number;
  spatialCoordinates: { x: number; y: number };
  dimensionalMapping: string[];  // AAL Dimensions D0-D10
  aalMnemonics: string[];        // ADD, SUB, MUL, DIV, etc.
}

export interface MathematicalMetadata {
  foundation: string[];
  dimensions: number[];
  hopfCompatible: boolean;
  normPreserving: boolean;
  polynomialDegree?: number;
  geometricType: 'projective' | 'affine' | 'fano' | 'cartesian';
  verification: {
    coqProof?: string;
    formalVerified: boolean;
    proofComplexity: number;
  };
}

export interface DevelopmentMetadata {
  layer: number;  // 1-7 from dev-docs structure
  difficulty: number;
  status: 'draft' | 'review' | 'approved' | 'deprecated' | 'superseded';
  completeness: number;
  tested: boolean;
  coverage: number;
  lastUpdate: string;
}

export interface FileMetadata {
  // Core Identification
  id: string;
  uuid: string;
  fingerprint: string;
  title: string;
  type: string[];
  category: string;
  
  // CanvasL Integration
  canvasL: CanvasLMetadata;
  
  // Mathematical Context
  mathematical: MathematicalMetadata;
  
  // Development & Quality
  development: DevelopmentMetadata;
  
  // File Statistics
  statistics: {
    totalFiles: number;
    tsFiles: number;
    canvasFiles: number;
    testFiles: number;
    linesOfCode: number;
    complexity: number;
  };
  
  // Export & Tagging
  export: {
    tags: string[];
    keywords: string[];
    exportTargets: string[];
    noRef: boolean;
    classified: string;
  };
}

export class MetadataService {
  private metadataDir = '.metadata';
  private hiddenMetadataDir = path.join(this.metadataDir, '.hidden');
  private registryPath = path.join(this.hiddenMetadataDir, 'registry');
  
  constructor(private basePath: string) {
    this.ensureDirectories();
  }
  
  private ensureDirectories() {
    const dirs = [
      this.metadataDir,
      this.hiddenMetadataDir,
      path.join(this.hiddenMetadataDir, 'cache'),
      path.join(this.hiddenMetadataDir, 'registry'),
      path.join(this.metadataDir, 'schemas'),
      path.join(this.metadataDir, 'templates'),
      path.join(this.metadataDir, 'exports')
    ];
    
    dirs.forEach(dir => {
      if (!require('fs').existsSync(dir)) {
        require('fs').mkdirSync(dir, { recursive: true });
      }
    });
  }
  
  /**
   * Generate comprehensive fingerprint for any file
   */
  async generateFingerprint(filePath: string): Promise<string> {
    const content = await fs.readFile(filePath, 'utf8');
    const stats = await fs.stat(filePath);
    
    // Multi-factor fingerprint including:
    // 1. Content hash
    // 2. CanvasL structure hash (if canvas file)
    // 3. AAL mathematical signature
    const contentHash = crypto.createHash('sha256').update(content).digest('hex');
    
    let canvasLHash = '';
    if (filePath.endsWith('.canvas') || filePath.endsWith('.json')) {
      const canvasStructure = await this.extractCanvasStructure(content);
      canvasLHash = crypto.createHash('sha256')
        .update(JSON.stringify(canvasStructure))
        .digest('hex');
    }
    
    // Generate AAL mathematical signature
    const aalSignature = await this.generateAALSignature(content);
    
    const combined = `${contentHash}:${stats.size}:${stats.mtimeMs}:${canvasLHash}:${aalSignature}`;
    return crypto.createHash('sha256').update(combined).digest('hex');
  }
  
  /**
   * Extract CanvasL structure for fingerprinting
   */
  private async extractCanvasStructure(content: string): Promise<any> {
    try {
      const parsed = JSON.parse(content);
      return {
        nodeCount: parsed.nodes?.length || 0,
        edgeCount: parsed.edges?.length || 0,
        canvasTypes: this.extractCanvasLTypes(parsed.nodes || []),
        aalPatterns: this.extractAALPatterns(parsed.nodes || []),
        spatialBounds: this.calculateSpatialBounds(parsed.nodes || [])
      };
    } catch {
      return { type: 'text' };
    }
  }
  
  /**
   * Generate AAL mathematical signature
   */
  private async generateAALSignature(content: string): Promise<string> {
    // Extract CanvasL patterns and convert to polynomial representation
    const patterns = content.match(/#(Observe|Activate|Transform|Verify|Store|Integrate|Propagate|BackPropagate):/g) || [];
    const aalMnemonics = patterns.map(p => this.canvasLToAAL(p));
    
    // Convert to polynomial coefficients over F₂
    const polynomial = this.mnemonicsToPolynomial(aalMnemonics);
    
    return crypto.createHash('sha256')
      .update(polynomial.join(','))
      .digest('hex');
  }
  
  /**
   * Map CanvasL patterns to AAL mnemonics
   */
  private canvasLToAAL(canvasLPattern: string): string {
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
  
  /**
   * Convert AAL mnemonics to polynomial over F₂
   */
  private mnemonicsToPolynomial(mnemonics: string[]): number[] {
    const aalEncoding: Record<string, number[]> = {
      'ADD': [1, 0, 0, 1],
      'SUB': [1, 1, 0, 0],
      'MUL': [1, 0, 1, 0],
      'DIV': [0, 1, 1, 0],
      'MOV': [0, 0, 1, 1],
      'CMP': [1, 1, 1, 0],
      'CALL': [0, 1, 0, 1],
      'RET': [1, 0, 1, 1],
      'VOTE': [1, 1, 0, 1],
      'FEEDBACK': [0, 1, 1, 1]
    };
    
    // Sum all mnemonics (XOR in F₂)
    const result = [0, 0, 0, 0];
    for (const mnemonic of mnemonics) {
      const encoding = aalEncoding[mnemonic] || [0, 0, 0, 0];
      for (let i = 0; i < 4; i++) {
        result[i] = (result[i] + encoding[i]) % 2;
      }
    }
    
    return result;
  }
  
  /**
   * Extract CanvasL types from nodes
   */
  private extractCanvasLTypes(nodes: any[]): string[] {
    const types = new Set<string>();
    for (const node of nodes) {
      const match = node.text?.match(/#(\w+):/);
      if (match) types.add(match[1]);
    }
    return Array.from(types);
  }
  
  /**
   * Extract AAL patterns from canvas nodes
   */
  private extractAALPatterns(nodes: any[]): string[] {
    const patterns = new Set<string>();
    for (const node of nodes) {
      const canvasLType = node.text?.match(/#(\w+):/)?.[1];
      if (canvasLType) {
        patterns.add(this.canvasLToAAL(`#${canvasLType}:`));
      }
    }
    return Array.from(patterns);
  }
  
  /**
   * Calculate spatial bounds for fingerprinting
   */
  private calculateSpatialBounds(nodes: any[]): { minX: number; maxX: number; minY: number; maxY: number } {
    if (nodes.length === 0) return { minX: 0, maxX: 0, minY: 0, maxY: 0 };
    
    let minX = Infinity, maxX = -Infinity;
    let minY = Infinity, maxY = -Infinity;
    
    for (const node of nodes) {
      minX = Math.min(minX, node.x || 0);
      maxX = Math.max(maxX, node.x || 0);
      minY = Math.min(minY, node.y || 0);
      maxY = Math.max(maxY, node.y || 0);
    }
    
    return { minX, maxX, minY, maxY };
  }
  
  /**
   * Extract metadata from file front matter
   */
  async extractFrontMatter(filePath: string): Promise<any> {
    const content = await fs.readFile(filePath, 'utf8');
    
    // Check for YAML front matter
    const frontMatterMatch = content.match(/^---\n([\s\S]*?)\n---/);
    if (frontMatterMatch) {
      try {
        return parseYAML(frontMatterMatch[1]);
      } catch (error) {
        console.warn(`Failed to parse front matter in ${filePath}:`, error);
        return {};
      }
    }
    
    return {};
  }
  
  /**
   * Generate metadata for a file
   */
  async generateFileMetadata(filePath: string): Promise<FileMetadata> {
    const relativePath = path.relative(this.basePath, filePath);
    const stats = await fs.stat(filePath);
    const fingerprint = await this.generateFingerprint(filePath);
    const frontMatter = await this.extractFrontMatter(filePath);
    
    // Extract CanvasL information
    const content = await fs.readFile(filePath, 'utf8');
    const canvasLTypes = this.extractCanvasLTypesFromContent(content);
    const aalMnemonics = this.extractAALMnemonicsFromContent(content);
    
    // Generate UUID based on path and content
    const uuid = crypto.createHash('sha256')
      .update(`${relativePath}:${fingerprint}`)
      .digest('hex')
      .substring(0, 32);
    
    return {
      id: `mind-git:${relativePath.replace(/[^a-zA-Z0-9]/g, '-')}`,
      uuid,
      fingerprint,
      title: frontMatter.title || path.basename(filePath, path.extname(filePath)),
      type: frontMatter.type || ['implementation'],
      category: frontMatter.category || 'core',
      
      canvasL: {
        nodeTypes: canvasLTypes,
        compilationOrder: frontMatter.compilationOrder || 0,
        spatialCoordinates: frontMatter.spatialCoordinates || { x: 0, y: 0 },
        dimensionalMapping: frontMatter.dimensional || ['D0'],
        aalMnemonics
      },
      
      mathematical: {
        foundation: frontMatter.mathematicalFoundation || [],
        dimensions: frontMatter.dimensions || [0],
        hopfCompatible: frontMatter.hopfCompatible || false,
        normPreserving: frontMatter.normPreserving || false,
        geometricType: frontMatter.geometricType || 'cartesian',
        verification: {
          coqProof: frontMatter.coqProof,
          formalVerified: frontMatter.formalVerified || false,
          proofComplexity: frontMatter.proofComplexity || 0
        }
      },
      
      development: {
        layer: frontMatter.layer || this.inferLayer(relativePath),
        difficulty: frontMatter.difficulty || 3,
        status: frontMatter.status || 'draft',
        completeness: frontMatter.completeness || 0,
        tested: frontMatter.tested || false,
        coverage: frontMatter.coverage || 0,
        lastUpdate: stats.mtime.toISOString()
      },
      
      statistics: {
        totalFiles: 1,
        tsFiles: filePath.endsWith('.ts') || filePath.endsWith('.js') ? 1 : 0,
        canvasFiles: filePath.endsWith('.canvas') || filePath.endsWith('.json') ? 1 : 0,
        testFiles: filePath.includes('.test.') || filePath.includes('.spec.') ? 1 : 0,
        linesOfCode: content.split('\n').length,
        complexity: this.calculateComplexity(content)
      },
      
      export: {
        tags: frontMatter.tags || [],
        keywords: frontMatter.keywords || [],
        exportTargets: frontMatter.exportTargets || [],
        noRef: frontMatter.noRef || false,
        classified: frontMatter.classified || 'public'
      }
    };
  }
  
  /**
   * Extract CanvasL types from file content
   */
  private extractCanvasLTypesFromContent(content: string): string[] {
    const types = new Set<string>();
    const matches = content.match(/#(\w+):/g);
    if (matches) {
      for (const match of matches) {
        const type = match.replace('#', '').replace(':', '');
        types.add(type);
      }
    }
    return Array.from(types);
  }
  
  /**
   * Extract AAL mnemonics from file content
   */
  private extractAALMnemonicsFromContent(content: string): string[] {
    const patterns = content.match(/#(Observe|Activate|Transform|Verify|Store|Integrate|Propagate|BackPropagate):/g) || [];
    return patterns.map(p => this.canvasLToAAL(p));
  }
  
  /**
   * Infer layer from file path
   */
  private inferLayer(relativePath: string): number {
    if (relativePath.includes('dev-docs/1._')) return 1;
    if (relativePath.includes('dev-docs/2._')) return 2;
    if (relativePath.includes('dev-docs/3._')) return 3;
    if (relativePath.includes('dev-docs/4._')) return 4;
    if (relativePath.includes('dev-docs/5._')) return 5;
    if (relativePath.includes('dev-docs/6._')) return 6;
    if (relativePath.includes('dev-docs/7._')) return 7;
    if (relativePath.includes('logos-system/src/core')) return 2;
    if (relativePath.includes('logos-system/src/compiler')) return 3;
    if (relativePath.includes('logos-system/src/')) return 4;
    return 3; // Default
  }
  
  /**
   * Calculate complexity of content
   */
  private calculateComplexity(content: string): number {
    // Simple complexity metric based on patterns
    const canvasLPatterns = (content.match(/#\w+:/g) || []).length;
    const codeComplexity = (content.match(/if|for|while|function|class/g) || []).length;
    const mathematicalComplexity = (content.match(/polynomial|algebra|theorem|proof/g) || []).length;
    
    return canvasLPatterns + codeComplexity * 2 + mathematicalComplexity * 3;
  }
  
  /**
   * Write metadata to registry
   */
  async writeMetadata(relativePath: string, metadata: FileMetadata): Promise<void> {
    const registryFile = path.join(this.registryPath, `${relativePath.replace(/[^a-zA-Z0-9]/g, '-')}.json`);
    await fs.writeFile(registryFile, JSON.stringify(metadata, null, 2));
  }
  
  /**
   * Update global index
   */
  async updateGlobalIndex(relativePath: string, metadata: FileMetadata): Promise<void> {
    const indexPath = path.join(this.metadataDir, 'index.jsonl');
    const entry = {
      path: relativePath,
      id: metadata.id,
      uuid: metadata.uuid,
      fingerprint: metadata.fingerprint,
      title: metadata.title,
      type: metadata.type,
      category: metadata.category,
      layer: metadata.development.layer,
      status: metadata.development.status,
      lastUpdate: metadata.development.lastUpdate
    };
    
    // Read existing index
    let existingEntries: any[] = [];
    if (require('fs').existsSync(indexPath)) {
      const content = await fs.readFile(indexPath, 'utf8');
      existingEntries = content.split('\n')
        .filter(line => line.trim())
        .map(line => JSON.parse(line));
    }
    
    // Update or add entry
    const existingIndex = existingEntries.findIndex(e => e.path === relativePath);
    if (existingIndex >= 0) {
      existingEntries[existingIndex] = entry;
    } else {
      existingEntries.push(entry);
    }
    
    // Write updated index
    const updatedContent = existingEntries.map(e => JSON.stringify(e)).join('\n');
    await fs.writeFile(indexPath, updatedContent);
  }
  
  /**
   * Walk directory and process all files
   */
  async walkDirectory(dir: string): Promise<string[]> {
    const results: string[] = [];
    const list = await fs.readdir(dir);
    
    for (const file of list) {
      const fullPath = path.join(dir, file);
      const stat = await fs.stat(fullPath);
      
      if (stat && stat.isDirectory() && !file.startsWith('.') && file !== 'node_modules') {
        results.push(...await this.walkDirectory(fullPath));
      } else if (stat && stat.isFile()) {
        results.push(fullPath);
      }
    }
    
    return results;
  }
  
  /**
   * Process all files and update metadata
   */
  async updateMetadata(): Promise<FileMetadata[]> {
    console.log('🔄 Updating MIND-GIT metadata...');
    
    // Walk through all files
    const files = await this.walkDirectory(this.basePath);
    
    const metadataPromises = files.map(async (file) => {
      const relativePath = path.relative(this.basePath, file);
      
      // Skip metadata directories
      if (relativePath.includes('.metadata/')) return null;
      
      try {
        const metadata = await this.generateFileMetadata(file);
        
        // Write to hidden metadata store
        await this.writeMetadata(relativePath, metadata);
        
        // Update global index
        await this.updateGlobalIndex(relativePath, metadata);
        
        return metadata;
      } catch (error) {
        console.warn(`⚠️ Failed to process ${relativePath}:`, error.message);
        return null;
      }
    });
    
    const results = await Promise.all(metadataPromises);
    const validResults = results.filter(r => r !== null) as FileMetadata[];
    
    console.log(`✅ Updated metadata for ${validResults.length} files`);
    
    return validResults;
  }
}