export interface Violation {
  type: string;
  section: string;
  message: string;
  line?: number;
  column?: number;
  severity: 'error' | 'warning' | 'info';
}

export interface CheckResult {
  valid: boolean;
  violations: Violation[];
  metrics: ComplianceMetrics;
}

export interface ComplianceMetrics {
  rfcViolationsPerCommit: number;
  domainQualifiersPerKLOC: number;
  averageConceptsPerExplanation: number;
  forbiddenClaimsCount: number;
  redFlagCount: number;
  totalLines: number;
  totalFiles: number;
}

export interface RFCConstraint {
  id: string;
  section: string;
  description: string;
  check: (content: string) => Violation[];
}

export interface DomainQualifier {
  domain: string;
  description: string;
  requiredFor: string[];
}

export interface RedFlag {
  type: string;
  pattern: RegExp;
  section: string;
  description: string;
  severity: 'error' | 'warning';
}

export enum Phase {
  Validation = "Validation",
  Testing = "Testing",
  Documentation = "Documentation", 
  Production = "Production"
}

export interface TransitionResult {
  allowed: boolean;
  reason: string;
  required?: string[];
}