import { ConstraintChecker } from './constraint-checker.js';
import { RedFlagDetector } from './red-flag-detector.js';
import { DomainQualifierSystem } from './domain-qualifier.js';
import { PhaseManager, Phase } from './phase-manager.js';
import { CheckResult } from './types.js';

export class RFCNormalizer {
  private constraintChecker: ConstraintChecker;
  private redFlagDetector: RedFlagDetector;
  private domainQualifier: DomainQualifierSystem;
  private phaseManager: PhaseManager;

  constructor() {
    this.constraintChecker = new ConstraintChecker();
    this.redFlagDetector = new RedFlagDetector();
    this.domainQualifier = new DomainQualifierSystem();
    this.phaseManager = new PhaseManager();
  }

  // Main normalization function
  normalizeContent(content: string, options: NormalizeOptions = {}): NormalizeResult {
    const result: NormalizeResult = {
      original: content,
      normalized: content,
      changes: [],
      violations: [],
      redFlags: [],
      metrics: {
        original: this.calculateBasicMetrics(content),
        normalized: this.calculateBasicMetrics(content)
      }
    };

    // Step 1: Check for red flags (safety first)
    const redFlagReport = this.redFlagDetector.detectRedFlags(content);
    result.redFlags = redFlagReport.flags;

    // Step 2: Apply constraint-based fixes
    let normalizedContent = content;
    const constraintResult = this.constraintChecker.checkDocument(content);
    result.violations = constraintResult.violations;

    // Step 3: Apply domain qualifiers
    if (options.addDomainQualifiers) {
      normalizedContent = this.domainQualifier.addDomainQualifier(normalizedContent, 'DIGITAL');
      result.changes.push({
        type: 'domain-qualifiers',
        description: 'Added domain qualifiers for mixed-domain content'
      });
    }

    // Step 4: Apply language normalization
    normalizedContent = this.normalizeLanguage(normalizedContent, result);
    
    // Step 5: Apply structural fixes
    normalizedContent = this.applyStructuralFixes(normalizedContent, result);

    result.normalized = normalizedContent;
    result.metrics.normalized = this.calculateBasicMetrics(normalizedContent);

    return result;
  }

  private normalizeLanguage(content: string, result: NormalizeResult): string {
    let normalized = content;
    const changes: LanguageChange[] = [];

    // Replace problematic metaphysical terms with technical equivalents
    const replacements = [
      {
        pattern: /\breality\s+admin\b/gi,
        replacement: 'system administration',
        type: 'technical-terminology'
      },
      {
        pattern: /\bconsciousness\s+merging\b/gi,
        replacement: 'data federation',
        type: 'technical-terminology'
      },
      {
        pattern: /\bdimensional\s+shifting\b/gi,
        replacement: 'coordinate transformation',
        type: 'technical-terminology'
      },
      {
        pattern: /\btruth\s+detection\b/gi,
        replacement: 'consistency checking',
        type: 'technical-terminology'
      },
      {
        pattern: /\bsacred\s+geometry\b/gi,
        replacement: 'spatial algebra',
        type: 'technical-terminology'
      },
      {
        pattern: /\bjudgment\s+day\b/gi,
        replacement: 'system validation',
        type: 'apocalyptic-language'
      },
      {
        pattern: /\bnew\s+jerusalem\b/gi,
        replacement: 'distributed system architecture',
        type: 'apocalyptic-language'
      },
      {
        pattern: /\bwedding\s+feast\b/gi,
        replacement: 'system integration',
        type: 'metaphorical-language'
      },
      {
        pattern: /\bsoul\s+made\s+ready\b/gi,
        replacement: 'component prepared',
        type: 'metaphysical-language'
      },
      {
        pattern: /\bdimensional\s+transference\b/gi,
        replacement: 'coordinate system transformation',
        type: 'dimensional-language'
      }
    ];

    replacements.forEach(({ pattern, replacement, type }) => {
      const matches = normalized.match(pattern);
      if (matches) {
        normalized = normalized.replace(pattern, replacement);
        changes.push({
          type,
          original: matches[0],
          replacement,
          count: matches.length
        });
      }
    });

    result.changes.push(...changes);
    return normalized;
  }

  private applyStructuralFixes(content: string, result: NormalizeResult): string {
    let normalized = content;

    // Break long explanations into smaller chunks
    const lines = normalized.split('\n');
    const fixedLines = lines.map(line => {
      // Check for lines with too many claims
      const claims = line.match(/[.!?]+/g) || [];
      if (claims.length > 3) {
        // Split into multiple lines
        const sentences = line.split(/([.!?]+\s*)/);
        const chunks: string[] = [];
        let currentChunk = '';

        sentences.forEach(sentence => {
          if (currentChunk && currentChunk.match(/[.!?]+/g)?.length && currentChunk.match(/[.!?]+/g)!.length >= 3) {
            chunks.push(currentChunk.trim());
            currentChunk = sentence;
          } else {
            currentChunk += sentence;
          }
        });

        if (currentChunk.trim()) {
          chunks.push(currentChunk.trim());
        }

        result.changes.push({
          type: 'structural',
          description: `Split line with ${claims.length} claims into ${chunks.length} lines`
        });

        return chunks.join('\n');
      }
      return line;
    });

    return fixedLines.join('\n');
  }

  private calculateBasicMetrics(content: string): BasicMetrics {
    const lines = content.split('\n');
    const words = content.split(/\s+/).filter(w => w.length > 0);
    const sentences = content.split(/[.!?]+/).filter(s => s.trim().length > 0);
    
    return {
      lineCount: lines.length,
      wordCount: words.length,
      sentenceCount: sentences.length,
      avgWordsPerSentence: sentences.length > 0 ? words.length / sentences.length : 0,
      avgCharsPerLine: lines.length > 0 ? content.length / lines.length : 0
    };
  }

  // Validate if content is RFC compliant
  validateContent(content: string): CheckResult {
    const constraintResult = this.constraintChecker.checkDocument(content);
    const redFlagReport = this.redFlagDetector.detectRedFlags(content);
    const domainViolations = this.domainQualifier.checkDomainQualifiers(content);

    // Combine all violations
    const allViolations = [
      ...constraintResult.violations,
      ...redFlagReport.flags,
      ...domainViolations
    ];

    return {
      valid: allViolations.filter(v => v.severity === 'error').length === 0,
      violations: allViolations,
      metrics: constraintResult.metrics
    };
  }

  // Generate compliance report
  generateComplianceReport(content: string): ComplianceReport {
    const validation = this.validateContent(content);
    const domainReport = this.domainQualifier.generateDomainReport(content);
    const redFlagReport = this.redFlagDetector.detectRedFlags(content);

    return {
      timestamp: new Date(),
      overall: validation.valid ? 'COMPLIANT' : 'NON_COMPLIANT',
      score: this.calculateComplianceScore(validation, domainReport, redFlagReport),
      violations: validation.violations,
      domainReport,
      redFlagReport,
      recommendations: this.generateRecommendations(validation, domainReport, redFlagReport)
    };
  }

  private calculateComplianceScore(
    validation: CheckResult,
    domainReport: any,
    redFlagReport: any
  ): number {
    let score = 100;

    // Deduct points for violations
    validation.violations.forEach(violation => {
      switch (violation.severity) {
        case 'error': score -= 20; break;
        case 'warning': score -= 10; break;
        case 'info': score -= 5; break;
      }
    });

    // Deduct points for low domain qualification
    if (domainReport.qualificationRate < 50) {
      score -= 15;
    }

    // Deduct points for red flags
    score -= redFlagReport.summary.errors * 15;
    score -= redFlagReport.summary.warnings * 5;

    return Math.max(0, score);
  }

  private generateRecommendations(
    validation: CheckResult,
    domainReport: any,
    redFlagReport: any
  ): string[] {
    const recommendations: string[] = [];

    if (validation.violations.length > 0) {
      recommendations.push(`Fix ${validation.violations.length} RFC violations`);
    }

    if (domainReport.qualificationRate < 80) {
      recommendations.push('Add more domain qualifiers to improve clarity');
    }

    if (redFlagReport.requiresPause) {
      recommendations.push('CRITICAL: Review and address red flags before continuing');
    }

    if (recommendations.length === 0) {
      recommendations.push('Content is RFC compliant');
    }

    return recommendations;
  }
}

export interface NormalizeOptions {
  addDomainQualifiers?: boolean;
  applyStructuralFixes?: boolean;
  normalizeLanguage?: boolean;
}

export interface NormalizeResult {
  original: string;
  normalized: string;
  changes: Change[];
  violations: any[];
  redFlags: any[];
  metrics: {
    original: BasicMetrics;
    normalized: BasicMetrics;
  };
}

export interface Change {
  type: string;
  description?: string;
  original?: string;
  replacement?: string;
  count?: number;
}

export interface LanguageChange extends Change {
  type: string;
  original: string;
  replacement: string;
  count: number;
}

export interface BasicMetrics {
  lineCount: number;
  wordCount: number;
  sentenceCount: number;
  avgWordsPerSentence: number;
  avgCharsPerLine: number;
}

export interface ComplianceReport {
  timestamp: Date;
  overall: 'COMPLIANT' | 'NON_COMPLIANT';
  score: number;
  violations: any[];
  domainReport: any;
  redFlagReport: any;
  recommendations: string[];
}