import { ConstraintChecker } from '../src/constraint-checker.js';

describe('ConstraintChecker', () => {
  let checker: ConstraintChecker;

  beforeEach(() => {
    checker = new ConstraintChecker();
  });

  describe('one-step rule', () => {
    it('should detect more than 3 claims in a line', () => {
      const content = 'First claim. Second claim. Third claim. Fourth claim. Fifth claim.';
      const result = checker.checkDocument(content);

      expect(result.valid).toBe(false);
      expect(result.violations.some(v => v.type === 'one-step-rule')).toBe(true);
    });

    it('should pass with 3 or fewer claims', () => {
      const content = 'First claim. Second claim. Third claim.';
      const result = checker.checkDocument(content);

      expect(result.violations.some(v => v.type === 'one-step-rule')).toBe(false);
    });
  });

  describe('connection limit', () => {
    it('should detect too many connected concepts', () => {
      const content = 'System + Component + Module + Service + API + Database + Cache';
      const result = checker.checkDocument(content);

      expect(result.violations.some(v => v.type === 'connection-limit')).toBe(true);
    });
  });

  describe('domain separation', () => {
    it('should detect mixed domains without qualifiers', () => {
      const content = 'The compiler processes sacred geometry algorithms.';
      const result = checker.checkDocument(content);

      expect(result.violations.some(v => v.type === 'domain-separation')).toBe(true);
    });

    it('should pass with domain qualifiers', () => {
      const content = '// @domain DIGITAL - Technical system\nThe compiler processes algorithms.';
      const result = checker.checkDocument(content);

      expect(result.violations.some(v => v.type === 'domain-separation')).toBe(false);
    });
  });

  describe('urgency tone', () => {
    it('should detect urgency language', () => {
      const content = 'This is urgent and needs immediate attention now!';
      const result = checker.checkDocument(content);

      expect(result.violations.some(v => v.type === 'urgency-tone')).toBe(true);
    });
  });

  describe('compiler understandable', () => {
    it('should detect non-compiler-friendly language', () => {
      const content = 'This system provides reality admin capabilities.';
      const result = checker.checkDocument(content);

      expect(result.violations.some(v => v.type === 'compiler-understandable')).toBe(true);
    });
  });
});