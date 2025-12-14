/**
 * CanvasL Syntax Highlighter
 * Provides syntax highlighting for CanvasL nodes and AAL mnemonic tooltips
 */

export interface CanvasLPattern {
  prefix: string;
  color: string;
  backgroundColor?: string;
  mnemonic: string;
  description: string;
  dimension: string;
  assembly: string;
  examples?: string[];
}

export interface HighlightOptions {
  showTooltips: boolean;
  showMnemonics: boolean;
  showDimensions: boolean;
  tooltipDelay: number;
  highlightColors: boolean;
}

export interface TooltipContent {
  prefix: string;
  mnemonic: string;
  description: string;
  dimension: string;
  assembly: string;
  examples?: string[];
}

export class CanvasLHighlighter {
  private readonly canvasLPatterns: Map<string, CanvasLPattern> = new Map();
  private tooltipTimeouts = new Map<string, NodeJS.Timeout>();
  private activeTooltips = new Set<HTMLElement>();
  
  constructor(private options: HighlightOptions) {
    this.initializePatterns();
  }
  
  /**
   * Initialize CanvasL patterns
   */
  private initializePatterns(): void {
    const patterns: CanvasLPattern[] = [
      {
        prefix: '#Activate:',
        color: '#3498db',
        backgroundColor: 'rgba(52, 152, 219, 0.1)',
        mnemonic: 'JMP',
        description: 'Program entry point or function call',
        dimension: '0D→1D',
        assembly: 'JMP/CALL',
        examples: [
          '#Activate: main',
          '#Activate: function_name(param)',
          '#Activate: initialize_system'
        ]
      },
      {
        prefix: '#Integrate:',
        color: '#2ecc71',
        backgroundColor: 'rgba(46, 204, 113, 0.1)',
        mnemonic: 'ADD',
        description: 'Variable assignment or data integration',
        dimension: '1D→2D',
        assembly: 'ADD/SUB',
        examples: [
          '#Integrate: result = value',
          '#Integrate: counter += 1',
          '#Integrate: data = merge(a, b)'
        ]
      },
      {
        prefix: '#Transform:',
        color: '#f39c12',
        backgroundColor: 'rgba(243, 156, 18, 0.1)',
        mnemonic: 'MUL',
        description: 'Mathematical transformation or operation',
        dimension: '2D→3D',
        assembly: 'MUL/DIV',
        examples: [
          '#Transform: result = x * y',
          '#Transform: normalized = data / max',
          '#Transform: output = process(input)'
        ]
      },
      {
        prefix: '#Propagate:',
        color: '#9b59b6',
        backgroundColor: 'rgba(155, 89, 182, 0.1)',
        mnemonic: 'SHL',
        description: 'Data propagation or signal transmission',
        dimension: '3D→4D',
        assembly: 'SHL/ROL',
        examples: [
          '#Propagate: signal = broadcast(data)',
          '#Propagate: result = cascade(value)',
          '#Propagate: output = forward(input)'
        ]
      },
      {
        prefix: '#BackPropagate:',
        color: '#8e44ad',
        backgroundColor: 'rgba(142, 68, 173, 0.1)',
        mnemonic: 'CMP',
        description: 'Reverse propagation or comparison',
        dimension: '4D→3D',
        assembly: 'CMP/TEST',
        examples: [
          '#BackPropagate: error = compare(actual, expected)',
          '#BackPropagate: gradient = reverse(loss)',
          '#BackPropagate: feedback = evaluate(result)'
        ]
      },
      {
        prefix: '#Verify:',
        color: '#e74c3c',
        backgroundColor: 'rgba(231, 76, 60, 0.1)',
        mnemonic: 'VOTE',
        description: 'Condition checking or verification',
        dimension: '4D→5D',
        assembly: 'CMP/TEST',
        examples: [
          '#Verify: condition == true',
          '#Verify: is_valid(data)',
          '#Verify: proof.check(assertion)'
        ]
      },
      {
        prefix: '#Store:',
        color: '#95a5a6',
        backgroundColor: 'rgba(149, 165, 166, 0.1)',
        mnemonic: 'PUSH',
        description: 'Data storage or memory operation',
        dimension: '5D→6D',
        assembly: 'MOV/ST',
        examples: [
          '#Store: "Hello World"',
          '#Store: result_value',
          '#Store: database.save(data)'
        ]
      },
      {
        prefix: '#Observe:',
        color: '#e67e22',
        backgroundColor: 'rgba(230, 126, 34, 0.1)',
        mnemonic: 'SYNC',
        description: 'Data observation or quantum measurement',
        dimension: '6D→7D',
        assembly: 'LD/GET',
        examples: [
          '#Observe: console.log(output)',
          '#Observe: return result',
          '#Observe: measure(state)'
        ]
      }
    ];
    
    for (const pattern of patterns) {
      this.canvasLPatterns.set(pattern.prefix, pattern);
    }
  }
  
  /**
   * Highlight syntax in text content
   */
  highlightSyntax(text: string): { 
    highlighted: string; 
    tooltips: Array<{ element: HTMLElement; content: TooltipContent }>;
  } {
    let highlighted = text;
    const tooltips: Array<{ element: HTMLElement; content: TooltipContent }> = [];
    
    // Find all CanvasL patterns
    for (const [prefix, pattern] of this.canvasLPatterns) {
      const regex = new RegExp(`(${prefix})\\s*([^\\n]*)`, 'g');
      let match;
      
      while ((match = regex.exec(text)) !== null) {
        const fullMatch = match[0];
        const prefixMatch = match[1];
        const content = match[2];
        
        // Create highlighted span
        const spanId = `logos-highlight-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;
        const highlightedSpan = this.createHighlightedSpan(prefixMatch, content, pattern, spanId);
        
        // Replace in text
        highlighted = highlighted.replace(fullMatch, highlightedSpan);
        
        // Create tooltip content
        const tooltipContent: TooltipContent = {
          prefix: pattern.prefix,
          mnemonic: pattern.mnemonic,
          description: pattern.description,
          dimension: pattern.dimension,
          assembly: pattern.assembly,
          examples: pattern.examples
        };
        
        tooltips.push({
          element: document.getElementById(spanId)!,
          content: tooltipContent
        });
      }
    }
    
    return { highlighted, tooltips };
  }
  
  /**
   * Create highlighted span element
   */
  private createHighlightedSpan(
    prefix: string, 
    content: string, 
    pattern: CanvasLPattern,
    spanId: string
  ): string {
    const prefixStyle = this.options.highlightColors 
      ? `color: ${pattern.color}; background-color: ${pattern.backgroundColor || 'transparent'};`
      : '';
    
    const mnemonicStyle = this.options.showMnemonics 
      ? `color: ${pattern.color}; font-weight: bold;`
      : '';
    
    const dimensionStyle = this.options.showDimensions
      ? `color: #7f8c8d; font-size: 0.9em;`
      : '';
    
    let spanContent = `<span id="${spanId}" class="logos-canvasl-highlight" style="${prefixStyle}">`;
    spanContent += `<span class="logos-prefix">${prefix}</span>`;
    
    if (content) {
      spanContent += ` <span class="logos-content">${content}</span>`;
    }
    
    if (this.options.showMnemonics) {
      spanContent += ` <span class="logos-mnemonic" style="${mnemonicStyle}">[${pattern.mnemonic}]</span>`;
    }
    
    if (this.options.showDimensions) {
      spanContent += ` <span class="logos-dimension" style="${dimensionStyle}">(${pattern.dimension})</span>`;
    }
    
    spanContent += '</span>';
    
    return spanContent;
  }
  
  /**
   * Apply highlighting to element
   */
  applyHighlighting(element: HTMLElement): void {
    const text = element.textContent || '';
    const { highlighted, tooltips } = this.highlightSyntax(text);
    
    // Update element content
    element.innerHTML = highlighted;
    
    // Add tooltip events
    if (this.options.showTooltips) {
      for (const { element: tooltipElement, content } of tooltips) {
        this.addTooltipEvents(tooltipElement, content);
      }
    }
  }
  
  /**
   * Add tooltip events to element
   */
  private addTooltipEvents(element: HTMLElement, content: TooltipContent): void {
    let tooltip: HTMLElement | null = null;
    let showTimeout: NodeJS.Timeout;
    
    const showTooltip = () => {
      // Clear any existing timeout
      if (showTimeout) {
        clearTimeout(showTimeout);
      }
      
      // Set delay
      showTimeout = setTimeout(() => {
        // Hide existing tooltip
        this.hideAllTooltips();
        
        // Create new tooltip
        tooltip = this.createTooltip(content);
        document.body.appendChild(tooltip);
        
        // Position tooltip
        this.positionTooltip(element, tooltip);
        
        this.activeTooltips.add(tooltip);
      }, this.options.tooltipDelay);
    };
    
    const hideTooltip = () => {
      if (showTimeout) {
        clearTimeout(showTimeout);
      }
      
      if (tooltip) {
        tooltip.remove();
        this.activeTooltips.delete(tooltip);
        tooltip = null;
      }
    };
    
    // Add event listeners
    element.addEventListener('mouseenter', showTooltip);
    element.addEventListener('mouseleave', hideTooltip);
    element.addEventListener('click', hideTooltip);
  }
  
  /**
   * Create tooltip element
   */
  private createTooltip(content: TooltipContent): HTMLElement {
    const tooltip = document.createElement('div');
    tooltip.className = 'logos-canvasl-tooltip';
    
    // Header
    const header = document.createElement('div');
    header.className = 'logos-tooltip-header';
    
    const prefix = document.createElement('span');
    prefix.className = 'logos-tooltip-prefix';
    prefix.textContent = content.prefix;
    header.appendChild(prefix);
    
    const mnemonic = document.createElement('span');
    mnemonic.className = 'logos-tooltip-mnemonic';
    mnemonic.textContent = ` [${content.mnemonic}]`;
    header.appendChild(mnemonic);
    
    const dimension = document.createElement('span');
    dimension.className = 'logos-tooltip-dimension';
    dimension.textContent = ` ${content.dimension}`;
    header.appendChild(dimension);
    
    tooltip.appendChild(header);
    
    // Description
    const description = document.createElement('div');
    description.className = 'logos-tooltip-description';
    description.textContent = content.description;
    tooltip.appendChild(description);
    
    // Assembly info
    const assembly = document.createElement('div');
    assembly.className = 'logos-tooltip-assembly';
    assembly.innerHTML = `<strong>Assembly:</strong> ${content.assembly}`;
    tooltip.appendChild(assembly);
    
    // Examples
    if (content.examples && content.examples.length > 0) {
      const examplesSection = document.createElement('div');
      examplesSection.className = 'logos-tooltip-examples';
      
      const examplesTitle = document.createElement('div');
      examplesTitle.className = 'logos-tooltip-examples-title';
      examplesTitle.textContent = 'Examples:';
      examplesSection.appendChild(examplesTitle);
      
      const examplesList = document.createElement('ul');
      for (const example of content.examples) {
        const li = document.createElement('li');
        li.className = 'logos-tooltip-example';
        li.textContent = example;
        examplesList.appendChild(li);
      }
      examplesSection.appendChild(examplesList);
      
      tooltip.appendChild(examplesSection);
    }
    
    return tooltip;
  }
  
  /**
   * Position tooltip relative to element
   */
  private positionTooltip(element: HTMLElement, tooltip: HTMLElement): void {
    const elementRect = element.getBoundingClientRect();
    const tooltipRect = tooltip.getBoundingClientRect();
    
    let top = elementRect.top - tooltipRect.height - 10;
    let left = elementRect.left + (elementRect.width / 2) - (tooltipRect.width / 2);
    
    // Adjust if tooltip goes off screen
    if (top < 10) {
      top = elementRect.bottom + 10;
    }
    
    if (left < 10) {
      left = 10;
    }
    
    if (left + tooltipRect.width > window.innerWidth - 10) {
      left = window.innerWidth - tooltipRect.width - 10;
    }
    
    tooltip.style.position = 'fixed';
    tooltip.style.top = `${top}px`;
    tooltip.style.left = `${left}px`;
    tooltip.style.zIndex = '10000';
  }
  
  /**
   * Hide all active tooltips
   */
  private hideAllTooltips(): void {
    for (const tooltip of this.activeTooltips) {
      tooltip.remove();
    }
    this.activeTooltips.clear();
    
    // Clear all timeouts
    for (const timeout of this.tooltipTimeouts.values()) {
      clearTimeout(timeout);
    }
    this.tooltipTimeouts.clear();
  }
  
  /**
   * Get pattern for prefix
   */
  getPattern(prefix: string): CanvasLPattern | undefined {
    return this.canvasLPatterns.get(prefix);
  }
  
  /**
   * Get all patterns
   */
  getAllPatterns(): CanvasLPattern[] {
    return Array.from(this.canvasLPatterns.values());
  }
  
  /**
   * Check if text contains CanvasL syntax
   */
  containsCanvasLSyntax(text: string): boolean {
    for (const prefix of this.canvasLPatterns.keys()) {
      if (text.includes(prefix)) {
        return true;
      }
    }
    return false;
  }
  
  /**
   * Extract CanvasL operations from text
   */
  extractOperations(text: string): Array<{
    prefix: string;
    content: string;
    pattern: CanvasLPattern;
    position: number;
  }> {
    const operations: Array<{
      prefix: string;
      content: string;
      pattern: CanvasLPattern;
      position: number;
    }> = [];
    
    for (const [prefix, pattern] of this.canvasLPatterns) {
      const regex = new RegExp(`(${prefix})\\s*([^\\n]*)`, 'g');
      let match;
      
      while ((match = regex.exec(text)) !== null) {
        operations.push({
          prefix: match[1],
          content: match[2],
          pattern,
          position: match.index
        });
      }
    }
    
    return operations.sort((a, b) => a.position - b.position);
  }
  
  /**
   * Update highlighting options
   */
  updateOptions(options: Partial<HighlightOptions>): void {
    this.options = { ...this.options, ...options };
  }
  
  /**
   * Get current options
   */
  getOptions(): HighlightOptions {
    return { ...this.options };
  }
  
  /**
   * Clean up resources
   */
  dispose(): void {
    this.hideAllTooltips();
    this.canvasLPatterns.clear();
  }
}