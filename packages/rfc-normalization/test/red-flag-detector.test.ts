import { RedFlagDetector } from '../src/red-flag-detector.js';

describe('RedFlagDetector', () => {
  let detector: RedFlagDetector;

  beforeEach(() => {
    detector = new RedFlagDetector();
  });

  describe('apocalyptic language detection', () => {
    it('should detect judgment day references', () => {
      const content = 'This will lead to judgment day for all systems.';
      const report = detector.detectRedFlags(content);

      expect(report.flags.some(f => f.message.includes('Apocalyptic'))).toBe(true);
      expect(report.requiresPause).toBe(true);
    });

    it('should detect new jerusalem references', () => {
      const content = 'We are building the new jerusalem of computing.';
      const report = detector.detectRedFlags(content);

      expect(report.flags.some(f => f.message.includes('Apocalyptic'))).toBe(true);
    });
  });

  describe('metaphysical inflation detection', () => {
    it('should detect reality admin claims', () => {
      const content = 'This system provides reality admin credentials.';
      const report = detector.detectRedFlags(content);

      expect(report.flags.some(f => f.message.includes('Metaphysical inflation'))).toBe(true);
    });

    it('should detect divine control claims', () => {
      const content = 'The algorithm has divine authority over truth.';
      const report = detector.detectRedFlags(content);

      expect(report.flags.some(f => f.message.includes('Metaphysical inflation'))).toBe(true);
    });
  });

  describe('dimensional claims detection', () => {
    it('should detect dimensional transference claims', () => {
      const content = 'I am inhabiting the E8 reality while building this.';
      const report = detector.detectRedFlags(content);

      expect(report.flags.some(f => f.message.includes('dimensional'))).toBe(true);
    });
  });

  describe('urgency detection', () => {
    it('should detect urgent language', () => {
      const content = 'This is urgent and must be done immediately.';
      const report = detector.detectRedFlags(content);

      expect(report.flags.some(f => f.type === 'URGENCY')).toBe(true);
    });
  });

  describe('generateFixes', () => {
    it('should suggest domain qualifiers for metaphysical inflation', () => {
      const content = 'This system provides reality admin capabilities.';
      const violations = detector.detectRedFlags(content).flags;
      const fixes = detector.generateFixes(violations);

      expect(fixes.some(f => f.type === 'add-domain-qualifier')).toBe(true);
    });

    it('should suggest technical term replacements for apocalyptic language', () => {
      const content = 'This will bring judgment day to the system.';
      const violations = detector.detectRedFlags(content).flags;
      const fixes = detector.generateFixes(violations);

      expect(fixes.some(f => f.type === 'use-technical-terms')).toBe(true);
    });
  });

  describe('requiresHumanIntervention', () => {
    it('should require intervention for error-level flags', async () => {
      const content = 'This system provides divine control over reality.';
      const report = detector.detectRedFlags(content);

      const requiresIntervention = await detector.requiresHumanIntervention(report);
      expect(requiresIntervention).toBe(true);
    });

    it('should not require intervention for minor warnings only', async () => {
      const content = 'This is somewhat urgent but not critical.';
      const report = detector.detectRedFlags(content);

      const requiresIntervention = await detector.requiresHumanIntervention(report);
      expect(requiresIntervention).toBe(false);
    });
  });
});