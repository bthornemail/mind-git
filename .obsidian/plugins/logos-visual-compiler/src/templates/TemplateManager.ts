import { AST, ASTNode } from '../types/ast';
import { ParsedCanvas, ClassifiedNode } from '../types/canvas';

/**
 * Template definition for CanvasL
 */
export interface CanvasTemplate {
  id: string;
  name: string;
  description: string;
  category: 'function' | 'verification' | 'pipeline' | 'data' | 'control' | 'custom';
  tags: string[];
  icon: string;
  
  // Template structure
  nodes: TemplateNode[];
  edges: TemplateEdge[];
  
  // Metadata
  author?: string;
  version?: string;
  documentation?: string;
  examples?: string[];
  
  // AST/Data type requirements
  requiredNodeTypes?: string[];
  requiredDataTypes?: string[];
  outputFormat?: string;
}

export interface TemplateNode {
  id: string;
  type: 'text' | 'data' | 'function' | 'control';
  text: string;
  x: number;
  y: number;
  width?: number;
  height?: number;
  color?: string;
  classification?: string;
  dimension?: string;
  operation?: string;
  operands?: string[];
}

export interface TemplateEdge {
  id: string;
  fromNode: string;
  toNode: string;
  fromSide?: 'top' | 'right' | 'bottom' | 'left';
  toSide?: 'top' | 'right' | 'bottom' | 'left';
  label?: string;
  color?: string;
}

/**
 * Template manager for CanvasL
 * Provides extendable template system based on AST/data types
 */
export class TemplateManager {
  private templates = new Map<string, CanvasTemplate>();
  private userTemplates = new Map<string, CanvasTemplate>();
  
  constructor() {
    this.loadBuiltinTemplates();
  }
  
  /**
   * Load built-in templates
   */
  private loadBuiltinTemplates(): void {
    const builtinTemplates: CanvasTemplate[] = [
      // Function templates
      {
        id: 'basic-function',
        name: 'Basic Function',
        description: 'Simple function with input and output',
        category: 'function',
        tags: ['basic', 'function', 'input-output'],
        icon: '🔧',
        nodes: [
          {
            id: 'input',
            type: 'text',
            text: '#Integrate: input',
            x: 0,
            y: 0,
            width: 200,
            height: 60,
            classification: 'integrate',
            dimension: '1D'
          },
          {
            id: 'process',
            type: 'text',
            text: '#Transform: process(input)',
            x: 250,
            y: 0,
            width: 200,
            height: 60,
            classification: 'transform',
            dimension: '2D'
          },
          {
            id: 'output',
            type: 'text',
            text: '#Store: result',
            x: 500,
            y: 0,
            width: 200,
            height: 60,
            classification: 'store',
            dimension: '3D'
          }
        ],
        edges: [
          {
            id: 'edge-1',
            fromNode: 'input',
            toNode: 'process',
            label: 'data'
          },
          {
            id: 'edge-2',
            fromNode: 'process',
            toNode: 'output',
            label: 'result'
          }
        ],
        requiredNodeTypes: ['integrate', 'transform', 'store'],
        outputFormat: 'function'
      },
      
      // Verification templates
      {
        id: 'verification-pipeline',
        name: 'Verification Pipeline',
        description: 'Data verification with AAL proofs',
        category: 'verification',
        tags: ['verification', 'aal', 'proof', 'validation'],
        icon: '✅',
        nodes: [
          {
            id: 'data',
            type: 'text',
            text: '#Store: data',
            x: 0,
            y: 0,
            classification: 'store',
            dimension: '3D'
          },
          {
            id: 'verify',
            type: 'text',
            text: '#Verify: isValid(data)',
            x: 200,
            y: 0,
            classification: 'verify',
            dimension: '4D'
          },
          {
            id: 'transform',
            type: 'text',
            text: '#Transform: process(data)',
            x: 400,
            y: 0,
            classification: 'transform',
            dimension: '5D'
          },
          {
            id: 'observe',
            type: 'text',
            text: '#Observe: result',
            x: 600,
            y: 0,
            classification: 'observe',
            dimension: '6D'
          }
        ],
        edges: [
          {
            id: 'edge-1',
            fromNode: 'data',
            toNode: 'verify',
            label: 'validate'
          },
          {
            id: 'edge-2',
            fromNode: 'verify',
            toNode: 'transform',
            label: 'valid'
          },
          {
            id: 'edge-3',
            fromNode: 'transform',
            toNode: 'observe',
            label: 'output'
          }
        ],
        requiredNodeTypes: ['store', 'verify', 'transform', 'observe'],
        outputFormat: 'verification'
      },
      
      // Pipeline templates
      {
        id: 'data-pipeline',
        name: 'Data Pipeline',
        description: 'Multi-stage data processing pipeline',
        category: 'pipeline',
        tags: ['pipeline', 'data', 'processing', 'stages'],
        icon: '🔄',
        nodes: [
          {
            id: 'source',
            type: 'text',
            text: '#Activate: data_source',
            x: 0,
            y: 0,
            classification: 'activate',
            dimension: '0D'
          },
          {
            id: 'stage1',
            type: 'text',
            text: '#Integrate: stage1',
            x: 200,
            y: 0,
            classification: 'integrate',
            dimension: '1D'
          },
          {
            id: 'stage2',
            type: 'text',
            text: '#Transform: stage2',
            x: 400,
            y: 0,
            classification: 'transform',
            dimension: '2D'
          },
          {
            id: 'stage3',
            type: 'text',
            text: '#Propagate: stage3',
            x: 600,
            y: 0,
            classification: 'propagate',
            dimension: '3D'
          },
          {
            id: 'output',
            type: 'text',
            text: '#Store: pipeline_result',
            x: 800,
            y: 0,
            classification: 'store',
            dimension: '4D'
          }
        ],
        edges: [
          {
            id: 'edge-1',
            fromNode: 'source',
            toNode: 'stage1',
            label: 'flow'
          },
          {
            id: 'edge-2',
            fromNode: 'stage1',
            toNode: 'stage2',
            label: 'data'
          },
          {
            id: 'edge-3',
            fromNode: 'stage2',
            toNode: 'stage3',
            label: 'processed'
          },
          {
            id: 'edge-4',
            fromNode: 'stage3',
            toNode: 'output',
            label: 'result'
          }
        ],
        requiredNodeTypes: ['activate', 'integrate', 'transform', 'propagate', 'store'],
        outputFormat: 'pipeline'
      },
      
      // Control flow templates
      {
        id: 'conditional-flow',
        name: 'Conditional Flow',
        description: 'Conditional branching with verification',
        category: 'control',
        tags: ['conditional', 'branch', 'if-else', 'control'],
        icon: '🔀',
        nodes: [
          {
            id: 'condition',
            type: 'text',
            text: '#Verify: condition',
            x: 200,
            y: 0,
            classification: 'verify',
            dimension: '4D'
          },
          {
            id: 'true-branch',
            type: 'text',
            text: '#Transform: true_path',
            x: 100,
            y: 150,
            classification: 'transform',
            dimension: '5D'
          },
          {
            id: 'false-branch',
            type: 'text',
            text: '#Transform: false_path',
            x: 300,
            y: 150,
            classification: 'transform',
            dimension: '5D'
          },
          {
            id: 'merge',
            type: 'text',
            text: '#Integrate: result',
            x: 200,
            y: 300,
            classification: 'integrate',
            dimension: '6D'
          }
        ],
        edges: [
          {
            id: 'edge-1',
            fromNode: 'condition',
            toNode: 'true-branch',
            label: 'true'
          },
          {
            id: 'edge-2',
            fromNode: 'condition',
            toNode: 'false-branch',
            label: 'false'
          },
          {
            id: 'edge-3',
            fromNode: 'true-branch',
            toNode: 'merge',
            label: 'output'
          },
          {
            id: 'edge-4',
            fromNode: 'false-branch',
            toNode: 'merge',
            label: 'output'
          }
        ],
        requiredNodeTypes: ['verify', 'transform', 'integrate'],
        outputFormat: 'control'
      },
      
      // Data structure templates
      {
        id: 'data-structure',
        name: 'Data Structure',
        description: 'Complex data structure with multiple components',
        category: 'data',
        tags: ['data', 'structure', 'components', 'assembly'],
        icon: '📊',
        nodes: [
          {
            id: 'component1',
            type: 'text',
            text: '#Store: component1',
            x: 0,
            y: 0,
            classification: 'store',
            dimension: '3D'
          },
          {
            id: 'component2',
            type: 'text',
            text: '#Store: component2',
            x: 200,
            y: 0,
            classification: 'store',
            dimension: '3D'
          },
          {
            id: 'component3',
            type: 'text',
            text: '#Store: component3',
            x: 400,
            y: 0,
            classification: 'store',
            dimension: '3D'
          },
          {
            id: 'assemble',
            type: 'text',
            text: '#Integrate: data_structure',
            x: 200,
            y: 150,
            classification: 'integrate',
            dimension: '4D'
          },
          {
            id: 'validate',
            type: 'text',
            text: '#Verify: is_valid(data_structure)',
            x: 200,
            y: 300,
            classification: 'verify',
            dimension: '5D'
          }
        ],
        edges: [
          {
            id: 'edge-1',
            fromNode: 'component1',
            toNode: 'assemble',
            label: 'part'
          },
          {
            id: 'edge-2',
            fromNode: 'component2',
            toNode: 'assemble',
            label: 'part'
          },
          {
            id: 'edge-3',
            fromNode: 'component3',
            toNode: 'assemble',
            label: 'part'
          },
          {
            id: 'edge-4',
            fromNode: 'assemble',
            toNode: 'validate',
            label: 'structure'
          }
        ],
        requiredNodeTypes: ['store', 'integrate', 'verify'],
        outputFormat: 'data'
      }
    ];
    
    // Register built-in templates
    for (const template of builtinTemplates) {
      this.templates.set(template.id, template);
    }
  }
  
  /**
   * Get all templates
   */
  getAllTemplates(): CanvasTemplate[] {
    return [
      ...Array.from(this.templates.values()),
      ...Array.from(this.userTemplates.values())
    ];
  }
  
  /**
   * Get template by ID
   */
  getTemplate(id: string): CanvasTemplate | undefined {
    return this.templates.get(id) || this.userTemplates.get(id);
  }
  
  /**
   * Get templates by category
   */
  getTemplatesByCategory(category: string): CanvasTemplate[] {
    return this.getAllTemplates().filter(template => template.category === category);
  }
  
  /**
   * Get templates by tags
   */
  getTemplatesByTags(tags: string[]): CanvasTemplate[] {
    return this.getAllTemplates().filter(template =>
      tags.some(tag => template.tags.includes(tag))
    );
  }
  
  /**
   * Search templates
   */
  searchTemplates(query: string): CanvasTemplate[] {
    const lowerQuery = query.toLowerCase();
    return this.getAllTemplates().filter(template =>
      template.name.toLowerCase().includes(lowerQuery) ||
      template.description.toLowerCase().includes(lowerQuery) ||
      template.tags.some(tag => tag.toLowerCase().includes(lowerQuery))
    );
  }
  
  /**
   * Get templates compatible with AST
   */
  getTemplatesForAST(ast: AST): CanvasTemplate[] {
    const nodeTypes = ast.nodes.map(node => node.type);
    const dataTypes = ast.variables.map(variable => variable.type);
    
    return this.getAllTemplates().filter(template => {
      // Check if template requirements are met
      if (template.requiredNodeTypes) {
        const hasRequiredTypes = template.requiredNodeTypes.every(requiredType =>
          nodeTypes.includes(requiredType)
        );
        if (!hasRequiredTypes) return false;
      }
      
      if (template.requiredDataTypes) {
        const hasRequiredDataTypes = template.requiredDataTypes.every(requiredType =>
          dataTypes.includes(requiredType)
        );
        if (!hasRequiredDataTypes) return false;
      }
      
      return true;
    });
  }
  
  /**
   * Get templates compatible with parsed canvas
   */
  getTemplatesForCanvas(canvas: ParsedCanvas): CanvasTemplate[] {
    const nodeTypes = canvas.nodes.map(node => node.classification);
    const dataTypes = canvas.nodes
      .filter(node => node.type === 'data')
      .map(node => node.dataType || 'unknown');
    
    return this.getAllTemplates().filter(template => {
      if (template.requiredNodeTypes) {
        const hasRequiredTypes = template.requiredNodeTypes.every(requiredType =>
          nodeTypes.includes(requiredType)
        );
        if (!hasRequiredTypes) return false;
      }
      
      if (template.requiredDataTypes) {
        const hasRequiredDataTypes = template.requiredDataTypes.every(requiredType =>
          dataTypes.includes(requiredType)
        );
        if (!hasRequiredDataTypes) return false;
      }
      
      return true;
    });
  }
  
  /**
   * Add user template
   */
  addUserTemplate(template: CanvasTemplate): void {
    // Validate template
    if (!this.validateTemplate(template)) {
      throw new Error('Invalid template structure');
    }
    
    this.userTemplates.set(template.id, template);
  }
  
  /**
   * Remove user template
   */
  removeUserTemplate(id: string): boolean {
    return this.userTemplates.delete(id);
  }
  
  /**
   * Update user template
   */
  updateUserTemplate(template: CanvasTemplate): void {
    if (!this.userTemplates.has(template.id)) {
      throw new Error('Template not found');
    }
    
    if (!this.validateTemplate(template)) {
      throw new Error('Invalid template structure');
    }
    
    this.userTemplates.set(template.id, template);
  }
  
  /**
   * Validate template structure
   */
  private validateTemplate(template: CanvasTemplate): boolean {
    if (!template.id || !template.name || !template.description) {
      return false;
    }
    
    if (!template.nodes || !Array.isArray(template.nodes) || template.nodes.length === 0) {
      return false;
    }
    
    if (!template.edges || !Array.isArray(template.edges)) {
      return false;
    }
    
    // Validate nodes
    for (const node of template.nodes) {
      if (!node.id || !node.type || !node.text) {
        return false;
      }
      
      if (typeof node.x !== 'number' || typeof node.y !== 'number') {
        return false;
      }
    }
    
    // Validate edges
    for (const edge of template.edges) {
      if (!edge.id || !edge.fromNode || !edge.toNode) {
        return false;
      }
      
      // Check if referenced nodes exist
      const fromNode = template.nodes.find(n => n.id === edge.fromNode);
      const toNode = template.nodes.find(n => n.id === edge.toNode);
      
      if (!fromNode || !toNode) {
        return false;
      }
    }
    
    return true;
  }
  
  /**
   * Convert template to canvas format
   */
  templateToCanvas(template: CanvasTemplate, offsetX = 0, offsetY = 0): any {
    return {
      nodes: template.nodes.map(node => ({
        id: node.id,
        type: node.type,
        text: node.text,
        x: node.x + offsetX,
        y: node.y + offsetY,
        width: node.width || 200,
        height: node.height || 60,
        color: node.color || '1',
        classification: node.classification,
        dimension: node.dimension,
        operation: node.operation,
        operands: node.operands
      })),
      edges: template.edges.map(edge => ({
        id: edge.id,
        fromNode: edge.fromNode,
        toNode: edge.toNode,
        fromSide: edge.fromSide || 'right',
        toSide: edge.toSide || 'left',
        label: edge.label,
        color: edge.color || '1'
      }))
    };
  }
  
  /**
   * Get template categories
   */
  getCategories(): Array<{ id: string; name: string; description: string }> {
    return [
      { id: 'function', name: 'Functions', description: 'Function templates with input/output' },
      { id: 'verification', name: 'Verification', description: 'Templates with AAL proofs' },
      { id: 'pipeline', name: 'Pipelines', description: 'Multi-stage processing pipelines' },
      { id: 'control', name: 'Control Flow', description: 'Conditional and branching logic' },
      { id: 'data', name: 'Data Structures', description: 'Data organization templates' },
      { id: 'custom', name: 'Custom', description: 'User-defined templates' }
    ];
  }
  
  /**
   * Export templates to JSON
   */
  exportTemplates(): string {
    const exportData = {
      version: '1.0',
      exported: new Date().toISOString(),
      templates: Array.from(this.userTemplates.values())
    };
    
    return JSON.stringify(exportData, null, 2);
  }
  
  /**
   * Import templates from JSON
   */
  importTemplates(jsonData: string): { imported: number; errors: string[] } {
    const errors: string[] = [];
    let imported = 0;
    
    try {
      const importData = JSON.parse(jsonData);
      
      if (!importData.templates || !Array.isArray(importData.templates)) {
        errors.push('Invalid template file format');
        return { imported, errors };
      }
      
      for (const template of importData.templates) {
        try {
          this.addUserTemplate(template);
          imported++;
        } catch (error) {
          errors.push(`Template "${template.name}": ${error.message}`);
        }
      }
      
    } catch (error) {
      errors.push(`Failed to parse JSON: ${error.message}`);
    }
    
    return { imported, errors };
  }
  
  /**
   * Get template statistics
   */
  getStats(): {
    total: number;
    builtin: number;
    user: number;
    byCategory: Record<string, number>;
  } {
    const allTemplates = this.getAllTemplates();
    const byCategory: Record<string, number> = {};
    
    for (const template of allTemplates) {
      byCategory[template.category] = (byCategory[template.category] || 0) + 1;
    }
    
    return {
      total: allTemplates.length,
      builtin: this.templates.size,
      user: this.userTemplates.size,
      byCategory
    };
  }
}