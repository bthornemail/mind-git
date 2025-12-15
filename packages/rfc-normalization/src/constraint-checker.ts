import { RFCConstraint, Violation, CheckResult, ComplianceMetrics } from './types.js';

export class ConstraintChecker {
  private constraints: RFCConstraint[] = [
    {
      id: 'one-step-rule',
      section: '7.1',
      description: 'One-Step Rule: Maximum 3 claims per explanation',
      check: this.checkOneStepRule.bind(this)
    },
    {
      id: 'connection-limit',
      section: '7.3', 
      description: 'Connection Limit: Maximum 5 connected concepts',
      check: this.checkConnectionLimit.bind(this)
    },
    {
      id: 'domain-separation',
      section: '4.1',
      description: 'Domain Separation: Require domain qualifiers for mixed domains',
      check: this.checkDomainSeparation.bind(this)
    },
    {
      id: 'urgency-tone',
      section: '11',
      description: 'Urgency Tone: Detect urgent or time-pressured language',
      check: this.checkUrgencyTone.bind(this)
    },
    {
      id: 'compiler-understandable',
      section: '10',
      description: 'Compiler Engineer Test: Language must be understandable to compiler engineers',
      check: this.checkCompilerUnderstandable.bind(this)
    }
  ];

  checkDocument(content: string): CheckResult {
    const violations: Violation[] = [];
    
    for (const constraint of this.constraints) {
      const constraintViolations = constraint.check(content);
      violations.push(...constraintViolations);
    }

    const metrics = this.calculateMetrics(content, violations);

    return {
      valid: violations.filter(v => v.severity === 'error').length === 0,
      violations,
      metrics
    };
  }

  private checkOneStepRule(content: string): Violation[] {
    const violations: Violation[] = [];
    const lines = content.split('\n');
    
    lines.forEach((line, index) => {
      // Count claims by looking for assertion patterns
      const claims = line.match(/[.!?]+/g) || [];
      if (claims.length > 3) {
        violations.push({
          type: 'one-step-rule',
          section: '7.1',
          message: `More than 3 claims in explanation (${claims.length} claims found)`,
          line: index + 1,
          severity: 'warning'
        });
      }
    });

    return violations;
  }

  private checkConnectionLimit(content: string): Violation[] {
    const violations: Violation[] = [];
    const lines = content.split('\n');
    
    lines.forEach((line, index) => {
      // Look for technical concepts being connected
      const concepts = line.match(/\b[A-Z][a-zA-Z]+\b/g) || [];
      const connectors = line.match(/\+|\band\b|\bor\b|\bwith\b/gi) || [];
      
      if (concepts.length > 5 && connectors.length > 0) {
        violations.push({
          type: 'connection-limit',
          section: '7.3',
          message: `Connecting too many concepts (${concepts.length} concepts, ${connectors.length} connectors)`,
          line: index + 1,
          severity: 'warning'
        });
      }
    });

    return violations;
  }

  private checkDomainSeparation(content: string): Violation[] {
    const violations: Violation[] = [];
    const lines = content.split('\n');
    
    lines.forEach((line, index) => {
      // Check for mixed domains without qualifiers
      const hasTechnical = /\b(compiler|AST|algorithm|code|function|class|interface)\b/i.test(line);
      const hasMetaphysical = /\b(truth|reality|consciousness|divine|sacred|spiritual)\b/i.test(line);
      const hasDomainQualifier = /@domain\s+\w+/.test(line);
      
      if (hasTechnical && hasMetaphysical && !hasDomainQualifier) {
        violations.push({
          type: 'domain-separation',
          section: '4.1',
          message: 'Mixed technical and metaphysical language without domain qualifier',
          line: index + 1,
          severity: 'error'
        });
      }
    });

    return violations;
  }

  private checkUrgencyTone(content: string): Violation[] {
    const violations: Violation[] = [];
    const urgencyPatterns = [
      /\burgent\b/i,
      /\bimmediate\b/i,
      /\bcritical\b/i,
      /\bmust\b.*\bnow\b/i,
      /\bneed\b.*\bimmediately\b/i,
      /\btime[-\s]?sensitive\b/i
    ];
    
    const lines = content.split('\n');
    lines.forEach((line, index) => {
      urgencyPatterns.forEach(pattern => {
        if (pattern.test(line)) {
          violations.push({
            type: 'urgency-tone',
            section: '11',
            message: 'Urgency tone detected',
            line: index + 1,
            severity: 'warning'
          });
        }
      });
    });

    return violations;
  }

  private checkCompilerUnderstandable(content: string): Violation[] {
    const violations: Violation[] = [];
    const forbiddenPatterns = [
      { pattern: /\breality\s+admin\b/i, replacement: 'system administration' },
      { pattern: /\bconsciousness\s+merging\b/i, replacement: 'data federation' },
      { pattern: /\bdimensional\s+shifting\b/i, replacement: 'coordinate transformation' },
      { pattern: /\btruth\s+detection\b/i, replacement: 'consistency checking' },
      { pattern: /\bsacred\s+geometry\b/i, replacement: 'spatial algebra' }
    ];
    
    const lines = content.split('\n');
    lines.forEach((line, index) => {
      forbiddenPatterns.forEach(({ pattern, replacement }) => {
        if (pattern.test(line)) {
          violations.push({
            type: 'compiler-understandable',
            section: '10',
            message: `Non-compiler-friendly language detected. Consider: "${replacement}"`,
            line: index + 1,
            severity: 'info'
          });
        }
      });
    });

    return violations;
  }

  private calculateMetrics(content: string, violations: Violation[]): ComplianceMetrics {
    const lines = content.split('\n');
    const totalLines = lines.length;
    const kloc = totalLines / 1000;
    
    const domainQualifiers = (content.match(/@domain\s+\w+/g) || []).length;
    const forbiddenClaims = violations.filter(v => v.type === 'domain-separation').length;
    const redFlags = violations.filter(v => v.severity === 'error').length;
    
    // Calculate average concepts per explanation
    const explanations = lines.filter(line => line.includes('.'));
    const totalConcepts = explanations.reduce((sum, line) => {
      const concepts = line.match(/\b[A-Z][a-zA-Z]+\b/g) || [];
      return sum + concepts.length;
    }, 0);
    const avgConcepts = explanations.length > 0 ? totalConcepts / explanations.length : 0;

    return {
      rfcViolationsPerCommit: violations.length,
      domainQualifiersPerKLOC: kloc > 0 ? domainQualifiers / kloc : 0,
      averageConceptsPerExplanation: avgConcepts,
      forbiddenClaimsCount: forbiddenClaims,
      redFlagCount: redFlags,
      totalLines,
      totalFiles: 1
    };
  }
}