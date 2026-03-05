#!/usr/bin/env node

/**
 * Mind-Log to Assembly Compiler
 * Processes markdown files and compiles them to AAL assembly instructions
 */

const fs = require('fs');
const path = require('path');

// Simple AAL compiler based on the logos-system
class MindLogToAssemblyCompiler {
  constructor() {
    this.canvasToAAL = new Map([
      ['#Activate:', 'JMP'],
      ['#Integrate:', 'ADD'],
      ['#Propagate:', 'SHL'],
      ['#BackPropagate:', 'CMP'],
      ['#Transform:', 'MUL'],
      ['#Verify:', 'VOTE'],
      ['#Store:', 'PUSH'],
      ['#Observe:', 'SYNC'],
    ]);
  }

  /**
   * Process markdown file and extract AAL instructions
   */
  processMarkdownFile(filePath) {
    try {
      const content = fs.readFileSync(filePath, 'utf8');
      const lines = content.split('\n');
      
      const instructions = [];
      let currentSection = '';
      let lineNumber = 0;
      
      for (const line of lines) {
        lineNumber++;
        
        // Skip empty lines and comments
        if (!line.trim() || line.trim().startsWith('//')) continue;
        
        // Detect headers as sections
        if (line.startsWith('#')) {
          currentSection = line.trim();
          continue;
        }
        
        // Look for AAL patterns
        const aalInstruction = this.detectAALPattern(line, lineNumber, currentSection);
        if (aalInstruction) {
          instructions.push(aalInstruction);
        }
      }
      
      return {
        file: filePath,
        instructions,
        metadata: {
          totalLines: lineNumber,
          instructionCount: instructions.length,
          sections: this.extractSections(content)
        }
      };
      
    } catch (error) {
      return {
        file: filePath,
        error: error.message,
        instructions: []
      };
    }
  }

  /**
   * Detect AAL patterns in text
   */
  detectAALPattern(line, lineNumber, section) {
    const trimmed = line.trim();
    
    // Check for CanvasL prefixes
    for (const [prefix, mnemonic] of this.canvasToAAL) {
      if (trimmed.includes(prefix)) {
        return {
          line: lineNumber,
          mnemonic,
          operands: this.extractOperands(trimmed),
          section,
          original: trimmed
        };
      }
    }
    
    // Check for mathematical patterns
    if (trimmed.includes('polynomial') || trimmed.includes('algebra')) {
      return {
        line: lineNumber,
        mnemonic: 'MUL',
        operands: ['polynomial', 'algebra'],
        section,
        original: trimmed
      };
    }
    
    if (trimmed.includes('verify') || trimmed.includes('proof')) {
      return {
        line: lineNumber,
        mnemonic: 'VOTE',
        operands: ['verification'],
        section,
        original: trimmed
      };
    }
    
    if (trimmed.includes('transform') || trimmed.includes('compile')) {
      return {
        line: lineNumber,
        mnemonic: 'SHL',
        operands: ['transformation'],
        section,
        original: trimmed
      };
    }
    
    return null;
  }

  /**
   * Extract operands from line
   */
  extractOperands(line) {
    const operands = [];
    
    // Extract words in quotes or after colons
    const quotedWords = line.match(/"([^"]+)"/g);
    if (quotedWords) {
      operands.push(...quotedWords.map(w => w.replace(/"/g, '')));
    }
    
    // Extract words after colons
    const colonWords = line.match(/:\s*([a-zA-Z0-9_]+)/g);
    if (colonWords) {
      operands.push(...colonWords.map(w => w.replace(/:\s*/, '')));
    }
    
    // Extract mathematical terms
    const mathTerms = line.match(/\b(polynomial|algebra|norm|dimension|vector|matrix|proof|verify)\b/gi);
    if (mathTerms) {
      operands.push(...mathTerms);
    }
    
    return operands.length > 0 ? operands : ['default'];
  }

  /**
   * Extract sections from markdown
   */
  extractSections(content) {
    const sections = [];
    const lines = content.split('\n');
    
    for (const line of lines) {
      if (line.startsWith('#')) {
        sections.push(line.trim());
      }
    }
    
    return sections;
  }

  /**
   * Generate assembly output
   */
  generateAssembly(processedFile) {
    if (processedFile.error) {
      return `; Error processing ${processedFile.file}: ${processedFile.error}`;
    }
    
    const lines = [
      `; Generated AAL Assembly from ${path.basename(processedFile.file)}`,
      `; Processed ${processedFile.metadata.totalLines} lines`,
      `; Found ${processedFile.metadata.instructionCount} instructions`,
      `; Sections: ${processedFile.metadata.sections.join(', ')}`,
      '',
      '; === ASSEMBLY INSTRUCTIONS ===',
      ''
    ];
    
    for (const instruction of processedFile.instructions) {
      lines.push(`; Line ${instruction.line} (${instruction.section})`);
      lines.push(`; ${instruction.original}`);
      lines.push(`${instruction.mnemonic} ${instruction.operands.join(', ')}`);
      lines.push('');
    }
    
    return lines.join('\n');
  }
}

// Main execution
function main() {
  const files = process.argv.slice(2);
  
  if (files.length === 0) {
    console.log('Usage: node mind-log-to-assembly.js <file1.md> [file2.md] ...');
    process.exit(1);
  }
  
  const compiler = new MindLogToAssemblyCompiler();
  
  console.log('🚀 Mind-Log to Assembly Compiler');
  console.log('=====================================\n');
  
  for (const filePath of files) {
    console.log(`📄 Processing: ${filePath}`);
    
    if (!fs.existsSync(filePath)) {
      console.log(`❌ File not found: ${filePath}\n`);
      continue;
    }
    
    const processed = compiler.processMarkdownFile(filePath);
    const assembly = compiler.generateAssembly(processed);
    
    console.log(assembly);
    console.log('\n' + '='.repeat(50) + '\n');
    
    // Save assembly output
    const outputPath = filePath.replace(/\.md$/, '.aal');
    fs.writeFileSync(outputPath, assembly);
    console.log(`💾 Assembly saved to: ${outputPath}\n`);
  }
  
  console.log('✅ Compilation complete!');
}

if (require.main === module) {
  main();
}

module.exports = { MindLogToAssemblyCompiler };