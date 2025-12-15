import { RFCNormalizer } from '../src/rfc-normalizer.js';

describe('RFCNormalizer', () => {
  let normalizer: RFCNormalizer;

  beforeEach(() => {
    normalizer = new RFCNormalizer();
  });

  describe('normalizeContent', () => {
    it('should replace metaphysical language with technical terms', () => {
      const content = 'This is reality admin for consciousness merging.';
      const result = normalizer.normalizeContent(content, {
        normalizeLanguage: true
      });

      expect(result.normalized).toBe('This is system administration for data federation.');
      expect(result.changes).toHaveLength(2);
    });

    it('should add domain qualifiers for mixed content', () => {
      const content = 'The compiler processes sacred geometry algorithms.';
      const result = normalizer.normalizeContent(content, {
        addDomainQualifiers: true
      });

      expect(result.normalized).toContain('@domain DIGITAL');
    });

    it('should break long explanations into smaller chunks', () => {
      const content = 'First claim. Second claim. Third claim. Fourth claim. Fifth claim.';
      const result = normalizer.normalizeContent(content, {
        applyStructuralFixes: true
      });

      const lines = result.normalized.split('\n');
      expect(lines.length).toBeGreaterThan(1);
    });
  });

  describe('validateContent', () => {
    it('should detect RFC violations', () => {
      const content = 'Urgent: We need everything connecting to everything now!';
      const result = normalizer.validateContent(content);

      expect(result.valid).toBe(false);
      expect(result.violations.length).toBeGreaterThan(0);
    });

    it('should pass compliant content', () => {
      const content = '// @domain DIGITAL - Technical system description\nThe compiler processes AST nodes efficiently.';
      const result = normalizer.validateContent(content);

      expect(result.valid).toBe(true);
    });
  });

  describe('generateComplianceReport', () => {
    it('should generate comprehensive compliance report', () => {
      const content = 'This system needs urgent attention for consciousness merging.';
      const report = normalizer.generateComplianceReport(content);

      expect(report.overall).toBe('NON_COMPLIANT');
      expect(report.score).toBeLessThan(100);
      expect(report.violations.length).toBeGreaterThan(0);
      expect(report.recommendations.length).toBeGreaterThan(0);
    });
  });
});