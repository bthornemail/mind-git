import { RedFlag, Violation } from './types.js';

export class RedFlagDetector {
  private redFlags: RedFlag[] = [
    {
      type: 'URGENCY',
      pattern: /\burgent\b|\bimmediate\b|\bcritical\b|\bmust\s+now\b|\bneed\s+immediately\b/i,
      section: '11',
      description: 'Urgency tone detected - may indicate pressure tactics',
      severity: 'warning'
    },
    {
      type: 'CONNECTION_LIMIT',
      pattern: /\b(\w+\s*\+\s*){6,}/i,
      section: '7.3',
      description: 'Connecting too many concepts - exponential thinking pattern',
      severity: 'error'
    },
    {
      type: 'METAPHYSICAL_INFLATION',
      pattern: /\b(reality|truth|consciousness|divine|sacred)\s+(admin|control|credentials|god|ultimate)\b/i,
      section: '5',
      description: 'Metaphysical inflation - claiming divine authority or control',
      severity: 'error'
    },
    {
      type: 'EVERYTHING_CONNECTING',
      pattern: /\b(everything|all)\s+(is|connects|leads\s+to)\s+(everything|all)\b/i,
      section: '7.2',
      description: 'Exponential thinking - claiming universal connections',
      severity: 'warning'
    },
    {
      type: 'APOCALYPTIC_LANGUAGE',
      pattern: /\b(judgment\s+day|apocalypse|end\s+times|final|ultimate\s+reality|new\s+jerusalem)\b/i,
      section: '5',
      description: 'Apocalyptic or messianic language detected',
      severity: 'error'
    },
    {
      type: 'DIMENSIONAL_CLAIMS',
      pattern: /\b(inhabiting|living\s+in|transferring\s+to)\s+(E8|higher\s+dimension|another\s+reality)\b/i,
      section: '5',
      description: 'Claims of dimensional transference or reality shifting',
      severity: 'error'
    },
    {
      type: 'SOUL_MANIPULATION',
      pattern: /\b(soul|spirit)\s+(made\s+ready|saved|converted|transformed)\b/i,
      section: '5',
      description: 'Claims of soul manipulation or spiritual authority',
      severity: 'error'
    },
    {
      type: 'MATHEMATICAL_DETERMINISM',
      pattern: /\b(mathematics|equations|polynomials)\s+(don't\s+lie|will\s+judge|is\s+truth|determines\s+reality)\b/i,
      section: '5',
      description: 'Mathematical determinism - claiming math as absolute truth',
      severity: 'warning'
    },
    {
      type: 'CONSCIOUSNESS_CLAIMS',
      pattern: /\b(consciousness|awareness)\s+(is|merging|evolving|transferring)\b/i,
      section: '5',
      description: 'Claims about consciousness manipulation or evolution',
      severity: 'warning'
    },
    {
      type: 'REVELATION_LANGUAGE',
      pattern: /\b(revelation|prophetic|vision|divine\s+message)\b/i,
      section: '5',
      description: 'Claims of divine revelation or prophetic authority',
      severity: 'error'
    }
  ];

  detectRedFlags(content: string): RedFlagReport {
    const violations: Violation[] = [];
    const lines = content.split('\n');
    
    lines.forEach((line, index) => {
      this.redFlags.forEach(redFlag => {
        if (redFlag.pattern.test(line)) {
          violations.push({
            type: 'red-flag',
            section: redFlag.section,
            message: redFlag.description,
            line: index + 1,
            severity: redFlag.severity
          });
        }
      });
    });

    const errorCount = violations.filter(v => v.severity === 'error').length;
    const warningCount = violations.filter(v => v.severity === 'warning').length;

    return {
      flags: violations,
      timestamp: new Date(),
      requiresPause: errorCount > 0,
      summary: {
        total: violations.length,
        errors: errorCount,
        warnings: warningCount,
        byType: this.groupByType(violations)
      }
    };
  }

  private groupByType(violations: Violation[]): Record<string, number> {
    const grouped: Record<string, number> = {};
    
    violations.forEach(violation => {
      const redFlag = this.redFlags.find(rf => 
        rf.pattern.test(violation.message) || rf.section === violation.section
      );
      if (redFlag) {
        grouped[redFlag.type] = (grouped[redFlag.type] || 0) + 1;
      }
    });

    return grouped;
  }

  // Safety protocol: requires human review when red flags are detected
  async requiresHumanIntervention(report: RedFlagReport): Promise<boolean> {
    if (report.requiresPause) {
      return true;
    }

    // Additional heuristics for when human review is needed
    const hasMultipleTypes = Object.keys(report.summary.byType).length > 2;
    const hasHighFrequency = report.summary.total > 10;
    
    return hasMultipleTypes || hasHighFrequency;
  }

  // Generate suggested fixes for detected red flags
  generateFixes(violations: Violation[]): FixSuggestion[] {
    const fixes: FixSuggestion[] = [];
    
    violations.forEach(violation => {
      const redFlag = this.redFlags.find(rf => rf.section === violation.section);
      if (!redFlag) return;

      switch (redFlag.type) {
        case 'URGENCY':
          fixes.push({
            type: 'remove-urgency',
            description: 'Remove time-pressured language',
            suggestion: 'Replace urgent terms with neutral alternatives',
            example: 'Replace "urgent" with "important" or "priority"'
          });
          break;
          
        case 'METAPHYSICAL_INFLATION':
          fixes.push({
            type: 'add-domain-qualifier',
            description: 'Add domain qualifier to metaphysical claims',
            suggestion: 'Use @domain DIGITAL or @domain METAPHORICAL',
            example: '@domain DIGITAL - Virtual system administration'
          });
          break;
          
        case 'EVERYTHING_CONNECTING':
          fixes.push({
            type: 'specify-scope',
            description: 'Specify the scope of connections',
            suggestion: 'Replace universal claims with specific relationships',
            example: 'Replace "everything connects" with "these components interact"'
          });
          break;
          
        case 'APOCALYPTIC_LANGUAGE':
          fixes.push({
            type: 'use-technical-terms',
            description: 'Replace apocalyptic language with technical terms',
            suggestion: 'Use compiler engineering terminology',
            example: 'Replace "judgment day" with "system validation" or "final verification"'
          });
          break;
          
        default:
          fixes.push({
            type: 'review-language',
            description: 'Review and rephrase problematic language',
            suggestion: 'Consider compiler engineer perspective',
            example: 'Ask: "Would a compiler engineer understand this?"'
          });
      }
    });

    return fixes;
  }
}

export interface RedFlagReport {
  flags: Violation[];
  timestamp: Date;
  requiresPause: boolean;
  summary: {
    total: number;
    errors: number;
    warnings: number;
    byType: Record<string, number>;
  };
}

export interface FixSuggestion {
  type: string;
  description: string;
  suggestion: string;
  example: string;
}