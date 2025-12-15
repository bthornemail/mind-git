import { DomainQualifier, Violation } from './types.js';

export class DomainQualifierSystem {
  private domains: Map<string, DomainQualifier> = new Map([
    ['DIGITAL', {
      domain: 'DIGITAL',
      description: 'Digital systems, software, compilers, algorithms',
      requiredFor: ['compiler', 'AST', 'algorithm', 'code', 'function', 'class', 'interface']
    }],
    ['MATHEMATICAL', {
      domain: 'MATHEMATICAL',
      description: 'Mathematical concepts, proofs, algebra, geometry',
      requiredFor: ['polynomial', 'algebra', 'theorem', 'proof', 'norm', 'vector', 'matrix']
    }],
    ['METAPHORICAL', {
      domain: 'METAPHORICAL',
      description: 'Metaphorical language, analogies, conceptual frameworks',
      requiredFor: ['sacred', 'divine', 'consciousness', 'reality', 'truth', 'spiritual']
    }],
    ['ORGANIZATIONAL', {
      domain: 'ORGANIZATIONAL',
      description: 'Project management, processes, workflows, team coordination',
      requiredFor: ['phase', 'workflow', 'process', 'management', 'coordination', 'planning']
    }],
    ['TECHNICAL', {
      domain: 'TECHNICAL',
      description: 'Technical implementation, engineering, system design',
      requiredFor: ['system', 'architecture', 'design', 'implementation', 'engineering']
    }]
  ]);

  checkDomainQualifiers(content: string): Violation[] {
    const violations: Violation[] = [];
    const lines = content.split('\n');
    
    lines.forEach((line, index) => {
      // Check for mixed domains without qualifiers
      const domainIssues = this.analyzeLineDomains(line);
      
      if (domainIssues.requiresQualifier && !this.hasDomainQualifier(line)) {
        violations.push({
          type: 'missing-domain-qualifier',
          section: '4.1',
          message: `Mixed domain language requires qualifier: ${domainIssues.suggestedDomain}`,
          line: index + 1,
          severity: 'warning'
        });
      }

      // Check for incorrect domain usage
      const incorrectDomain = this.checkIncorrectDomainUsage(line);
      if (incorrectDomain) {
        violations.push({
          type: 'incorrect-domain-qualifier',
          section: '4.1',
          message: `Incorrect domain usage: ${incorrectDomain}`,
          line: index + 1,
          severity: 'info'
        });
      }
    });

    return violations;
  }

  private analyzeLineDomains(line: string): { requiresQualifier: boolean; suggestedDomain: string } {
    const detectedDomains: string[] = [];
    
    this.domains.forEach((qualifier, domainName) => {
      const hasDomainTerms = qualifier.requiredFor.some(term => 
        new RegExp(`\\b${term}\\b`, 'i').test(line)
      );
      if (hasDomainTerms) {
        detectedDomains.push(domainName);
      }
    });

    if (detectedDomains.length > 1) {
      // Multiple domains detected - needs qualifier
      const primaryDomain = this.selectPrimaryDomain(detectedDomains, line);
      return {
        requiresQualifier: true,
        suggestedDomain: primaryDomain
      };
    }

    return { requiresQualifier: false, suggestedDomain: '' };
  }

  private selectPrimaryDomain(detectedDomains: string[], line: string): string {
    // Prioritize DIGITAL for technical content
    if (detectedDomains.includes('DIGITAL')) {
      return 'DIGITAL';
    }
    
    // Prioritize MATHEMATICAL for mathematical content
    if (detectedDomains.includes('MATHEMATICAL')) {
      return 'MATHEMATICAL';
    }
    
    // Use METAPHORICAL for mixed metaphorical content
    if (detectedDomains.includes('METAPHORICAL')) {
      return 'METAPHORICAL';
    }
    
    // Default to first detected
    return detectedDomains[0];
  }

  private hasDomainQualifier(line: string): boolean {
    return /@domain\s+\w+/.test(line);
  }

  private checkIncorrectDomainUsage(line: string): string | null {
    const domainMatch = line.match(/@domain\s+(\w+)/);
    if (!domainMatch) return null;

    const usedDomain = domainMatch[1];
    const qualifier = this.domains.get(usedDomain);
    
    if (!qualifier) {
      return `Unknown domain: ${usedDomain}`;
    }

    // Check if line content matches the domain
    const hasMatchingTerms = qualifier.requiredFor.some(term => 
      new RegExp(`\\b${term}\\b`, 'i').test(line)
    );

    if (!hasMatchingTerms) {
      return `Domain ${usedDomain} doesn't match line content`;
    }

    return null;
  }

  addDomainQualifier(content: string, domain: string): string {
    const lines = content.split('\n');
    const modifiedLines = lines.map(line => {
      if (this.needsDomainQualifier(line) && !this.hasDomainQualifier(line)) {
        return `// @domain ${domain} - ${this.domains.get(domain)?.description}\n${line}`;
      }
      return line;
    });

    return modifiedLines.join('\n');
  }

  private needsDomainQualifier(line: string): boolean {
    const analysis = this.analyzeLineDomains(line);
    return analysis.requiresQualifier;
  }

  generateDomainReport(content: string): DomainReport {
    const lines = content.split('\n');
    let totalLines = 0;
    let qualifiedLines = 0;
    const domainUsage: Record<string, number> = {};
    const violations: Violation[] = [];

    lines.forEach(line => {
      totalLines++;
      
      if (this.hasDomainQualifier(line)) {
        qualifiedLines++;
        const domainMatch = line.match(/@domain\s+(\w+)/);
        if (domainMatch) {
          const domain = domainMatch[1];
          domainUsage[domain] = (domainUsage[domain] || 0) + 1;
        }
      }

      const lineViolations = this.checkDomainQualifiers(line);
      violations.push(...lineViolations);
    });

    return {
      totalLines,
      qualifiedLines,
      qualificationRate: totalLines > 0 ? (qualifiedLines / totalLines) * 100 : 0,
      domainUsage,
      violations,
      recommendations: this.generateRecommendations(domainUsage, violations)
    };
  }

  private generateRecommendations(
    domainUsage: Record<string, number>, 
    violations: Violation[]
  ): string[] {
    const recommendations: string[] = [];

    if (Object.keys(domainUsage).length === 0) {
      recommendations.push('Consider adding domain qualifiers to improve clarity');
    }

    const missingQualifiers = violations.filter(v => v.type === 'missing-domain-qualifier');
    if (missingQualifiers.length > 0) {
      recommendations.push(`Add ${missingQualifiers.length} missing domain qualifiers`);
    }

    const mostUsedDomain = Object.entries(domainUsage)
      .sort(([,a], [,b]) => b - a)[0];
    if (mostUsedDomain) {
      recommendations.push(`Most used domain: ${mostUsedDomain[0]} (${mostUsedDomain[1]} times)`);
    }

    return recommendations;
  }

  // Get all available domains
  getAvailableDomains(): DomainQualifier[] {
    return Array.from(this.domains.values());
  }

  // Add a new domain
  addDomain(domain: DomainQualifier): void {
    this.domains.set(domain.domain, domain);
  }

  // Validate domain qualifier format
  validateDomainQualifier(qualifier: string): boolean {
    const match = qualifier.match(/@domain\s+(\w+)/);
    if (!match) return false;

    const domain = match[1];
    return this.domains.has(domain);
  }
}

export interface DomainReport {
  totalLines: number;
  qualifiedLines: number;
  qualificationRate: number;
  domainUsage: Record<string, number>;
  violations: Violation[];
  recommendations: string[];
}