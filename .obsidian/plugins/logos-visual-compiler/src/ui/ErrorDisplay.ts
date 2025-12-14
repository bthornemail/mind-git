import { Notice } from 'obsidian';
import { CompilationError } from '../state/StateManager';

/**
 * Error display system for CanvasL nodes
 * Supports inline red underlines, tooltips, and console output
 */

export interface ErrorDisplayOptions {
  mode: 'inline' | 'console' | 'both';
  showTooltips: boolean;
  highlightColor?: string;
  tooltipDelay?: number;
}

export class ErrorDisplay {
  private errorOverlays = new Map<string, HTMLElement>();
  private tooltipTimeouts = new Map<string, NodeJS.Timeout>();
  
  constructor(private options: ErrorDisplayOptions) {}
  
  /**
   * Display errors on canvas nodes
   */
  displayErrors(
    errors: CompilationError[], 
    canvasElement: HTMLElement,
    onNodeClick?: (nodeId: string) => void
  ): void {
    // Clear previous errors
    this.clearErrors();
    
    if (this.options.mode === 'console') {
      this.displayErrorsInConsole(errors);
      return;
    }
    
    // Group errors by node
    const errorsByNode = this.groupErrorsByNode(errors);
    
    // Display errors for each node
    for (const [nodeId, nodeErrors] of errorsByNode) {
      const nodeElement = this.findNodeElement(nodeId, canvasElement);
      
      if (nodeElement) {
        if (this.options.mode === 'inline' || this.options.mode === 'both') {
          this.displayInlineErrors(nodeElement, nodeId, nodeErrors, onNodeClick);
        }
        
        if (this.options.mode === 'both') {
          this.displayErrorsInConsole(nodeErrors);
        }
      } else {
        console.warn(`Could not find node element for ${nodeId}`);
      }
    }
  }
  
  /**
   * Clear all error displays
   */
  clearErrors(): void {
    // Remove error overlays
    for (const [nodeId, overlay] of this.errorOverlays) {
      overlay.remove();
    }
    this.errorOverlays.clear();
    
    // Clear tooltip timeouts
    for (const [nodeId, timeout] of this.tooltipTimeouts) {
      clearTimeout(timeout);
    }
    this.tooltipTimeouts.clear();
    
    // Remove error classes from nodes
    document.querySelectorAll('.logos-node-error').forEach(el => {
      el.classList.remove('logos-node-error');
    });
  }
  
  /**
   * Group errors by node ID
   */
  private groupErrorsByNode(errors: CompilationError[]): Map<string, CompilationError[]> {
    const grouped = new Map<string, CompilationError[]>();
    
    for (const error of errors) {
      const nodeId = error.node_id || 'unknown';
      
      if (!grouped.has(nodeId)) {
        grouped.set(nodeId, []);
      }
      
      grouped.get(nodeId)!.push(error);
    }
    
    return grouped;
  }
  
  /**
   * Find node element in canvas
   */
  private findNodeElement(nodeId: string, canvasElement: HTMLElement): HTMLElement | null {
    // Try different selectors to find the node
    const selectors = [
      `[data-node-id="${nodeId}"]`,
      `[id="${nodeId}"]`,
      `.canvas-node[data-id="${nodeId}"]`,
      `.node[data-node-id="${nodeId}"]`
    ];
    
    for (const selector of selectors) {
      const element = canvasElement.querySelector(selector) as HTMLElement;
      if (element) {
        return element;
      }
    }
    
    // Try to find by text content matching node ID
    const allNodes = canvasElement.querySelectorAll('.canvas-node, .node, [data-node-id]');
    for (const node of allNodes) {
      if (node.textContent?.includes(nodeId) || node.getAttribute('aria-label')?.includes(nodeId)) {
        return node as HTMLElement;
      }
    }
    
    return null;
  }
  
  /**
   * Display inline errors on node
   */
  private displayInlineErrors(
    nodeElement: HTMLElement,
    nodeId: string,
    errors: CompilationError[],
    onNodeClick?: (nodeId: string) => void
  ): void {
    // Add error class to node
    nodeElement.classList.add('logos-node-error');
    
    // Create error overlay
    const overlay = this.createErrorOverlay(nodeElement, nodeId, errors, onNodeClick);
    
    // Position overlay
    this.positionErrorOverlay(nodeElement, overlay);
    
    // Add to DOM and track
    nodeElement.appendChild(overlay);
    this.errorOverlays.set(nodeId, overlay);
    
    // Add hover events for tooltips
    if (this.options.showTooltips) {
      this.addTooltipEvents(nodeElement, overlay, errors);
    }
  }
  
  /**
   * Create error overlay element
   */
  private createErrorOverlay(
    nodeElement: HTMLElement,
    nodeId: string,
    errors: CompilationError[],
    onNodeClick?: (nodeId: string) => void
  ): HTMLElement {
    const overlay = document.createElement('div');
    overlay.className = 'logos-error-overlay';
    
    // Create red underline
    const underline = document.createElement('div');
    underline.className = 'logos-error-underline';
    underline.style.backgroundColor = this.options.highlightColor || '#e74c3c';
    
    // Create error indicator
    const indicator = document.createElement('div');
    indicator.className = 'logos-error-indicator';
    indicator.innerHTML = '⚠️';
    indicator.title = `${errors.length} error(s) - Click for details`;
    
    // Add click handler
    if (onNodeClick) {
      indicator.addEventListener('click', (e) => {
        e.stopPropagation();
        onNodeClick(nodeId);
      });
    }
    
    overlay.appendChild(underline);
    overlay.appendChild(indicator);
    
    return overlay;
  }
  
  /**
   * Position error overlay
   */
  private positionErrorOverlay(nodeElement: HTMLElement, overlay: HTMLElement): void {
    const rect = nodeElement.getBoundingClientRect();
    const parentRect = nodeElement.parentElement?.getBoundingClientRect();
    
    if (!parentRect) return;
    
    // Position at bottom of node
    overlay.style.position = 'absolute';
    overlay.style.bottom = '-2px';
    overlay.style.left = '0';
    overlay.style.width = '100%';
    overlay.style.height = '2px';
    overlay.style.zIndex = '1000';
    
    // Position indicator
    const indicator = overlay.querySelector('.logos-error-indicator') as HTMLElement;
    if (indicator) {
      indicator.style.position = 'absolute';
      indicator.style.top = '-20px';
      indicator.style.right = '0';
      indicator.style.fontSize = '12px';
      indicator.style.cursor = 'pointer';
    }
  }
  
  /**
   * Add tooltip events
   */
  private addTooltipEvents(
    nodeElement: HTMLElement,
    overlay: HTMLElement,
    errors: CompilationError[]
  ): void {
    let tooltip: HTMLElement | null = null;
    
    const showTooltip = () => {
      // Hide existing tooltip
      this.hideTooltip();
      
      // Create new tooltip
      tooltip = this.createTooltip(errors);
      document.body.appendChild(tooltip);
      
      // Position tooltip
      const rect = overlay.getBoundingClientRect();
      tooltip.style.position = 'fixed';
      tooltip.style.top = `${rect.top - 10}px`;
      tooltip.style.left = `${rect.right + 10}px`;
      tooltip.style.zIndex = '10000';
    };
    
    const hideTooltip = () => {
      this.hideTooltip();
    };
    
    // Add event listeners
    nodeElement.addEventListener('mouseenter', showTooltip);
    nodeElement.addEventListener('mouseleave', hideTooltip);
    
    overlay.addEventListener('mouseenter', showTooltip);
    overlay.addEventListener('mouseleave', hideTooltip);
  }
  
  /**
   * Create tooltip element
   */
  private createTooltip(errors: CompilationError[]): HTMLElement {
    const tooltip = document.createElement('div');
    tooltip.className = 'logos-error-tooltip';
    
    // Tooltip header
    const header = document.createElement('div');
    header.className = 'logos-tooltip-header';
    header.textContent = `${errors.length} Compilation Error(s)`;
    tooltip.appendChild(header);
    
    // Error list
    const errorList = document.createElement('div');
    errorList.className = 'logos-tooltip-errors';
    
    for (const error of errors) {
      const errorItem = document.createElement('div');
      errorItem.className = `logos-tooltip-error logos-tooltip-${error.severity}`;
      
      // Error type
      const typeSpan = document.createElement('span');
      typeSpan.className = 'logos-error-type';
      typeSpan.textContent = `${error.severity.toUpperCase()}: `;
      errorItem.appendChild(typeSpan);
      
      // Error message
      const messageSpan = document.createElement('span');
      messageSpan.className = 'logos-error-message';
      messageSpan.textContent = error.message;
      errorItem.appendChild(messageSpan);
      
      // Location info
      if (error.line !== undefined) {
        const locationSpan = document.createElement('span');
        locationSpan.className = 'logos-error-location';
        locationSpan.textContent = ` (line ${error.line}${error.column ? `, col ${error.column}` : ''})`;
        errorItem.appendChild(locationSpan);
      }
      
      errorList.appendChild(errorItem);
    }
    
    tooltip.appendChild(errorList);
    
    return tooltip;
  }
  
  /**
   * Hide current tooltip
   */
  private hideTooltip(): void {
    const existingTooltip = document.querySelector('.logos-error-tooltip');
    if (existingTooltip) {
      existingTooltip.remove();
    }
  }
  
  /**
   * Display errors in console
   */
  private displayErrorsInConsole(errors: CompilationError[]): void {
    console.group('🔴 CanvasL Compilation Errors');
    
    for (const error of errors) {
      const location = error.line !== undefined 
        ? ` (${error.line}${error.column ? `:${error.column}` : ''})`
        : '';
      
      if (error.severity === 'error') {
        console.error(`❌ ${error.message}${location}`, error);
      } else {
        console.warn(`⚠️ ${error.message}${location}`, error);
      }
    }
    
    console.groupEnd();
    
    // Show notice for errors
    const errorCount = errors.filter(e => e.severity === 'error').length;
    const warningCount = errors.filter(e => e.severity === 'warning').length;
    
    if (errorCount > 0) {
      new Notice(`❌ ${errorCount} compilation error(s) found`);
    } else if (warningCount > 0) {
      new Notice(`⚠️ ${warningCount} compilation warning(s) found`);
    }
  }
  
  /**
   * Update display options
   */
  updateOptions(options: Partial<ErrorDisplayOptions>): void {
    this.options = { ...this.options, ...options };
  }
  
  /**
   * Get current error statistics
   */
  getErrorStats(errors: CompilationError[]): {
    total: number;
    errors: number;
    warnings: number;
    nodesAffected: number;
  } {
    const nodesAffected = new Set(errors.map(e => e.node_id)).size;
    const errorCount = errors.filter(e => e.severity === 'error').length;
    const warningCount = errors.filter(e => e.severity === 'warning').length;
    
    return {
      total: errors.length,
      errors: errorCount,
      warnings: warningCount,
      nodesAffected
    };
  }
  
  /**
   * Check if node has errors
   */
  nodeHasErrors(nodeId: string, errors: CompilationError[]): boolean {
    return errors.some(error => error.node_id === nodeId);
  }
  
  /**
   * Get errors for specific node
   */
  getErrorsForNode(nodeId: string, errors: CompilationError[]): CompilationError[] {
    return errors.filter(error => error.node_id === nodeId);
  }
}