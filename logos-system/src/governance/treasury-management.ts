/**
 * Treasury Management with Multi-Currency Support
 * 
 * Implements comprehensive treasury management for DAOs with support for
 * multiple currencies, budget allocation, financial controls, and audit trails.
 */

import { PolyF2 } from '../core/polynomial/index';
import { AALType } from '../core/aal/types';
import { DIDDocument } from '../identity/did-core';
import { CubicSignature } from '../core/cryptography/cubic-signature';
import { ProductionCryptography } from '../core/cryptography/production-crypto';
import { Token, TokenBalance } from './token-economics';

export interface Treasury {
  treasuryId: string;
  name: string;
  daoId: string;
  currencies: Map<string, CurrencyBalance>;
  allocations: Map<string, Allocation>;
  budgets: Map<string, Budget>;
  transactions: Map<string, TreasuryTransaction>;
  controls: TreasuryControls;
  audit: AuditTrail;
  metadata: TreasuryMetadata;
}

export interface CurrencyBalance {
  currencyId: string;
  balance: number;
  lockedBalance: number;
  allocatedBalance: number;
  availableBalance: number;
  lastUpdated: string;
  metadata: CurrencyMetadata;
}

export interface CurrencyMetadata {
  decimals: number;
  symbol: string;
  name: string;
  type: 'native' | 'wrapped' | 'stablecoin' | 'governance';
  lastPrice: number;
  priceSource: string;
  priceTimestamp: string;
}

export interface Allocation {
  allocationId: string;
  budgetId: string;
  recipient: string;
  amount: number;
  currencyId: string;
  purpose: string;
  status: 'pending' | 'approved' | 'executed' | 'completed' | 'cancelled';
  createdAt: string;
  approvedAt?: string;
  executedAt?: string;
  completedAt?: string;
  conditions: AllocationCondition[];
  milestones: AllocationMilestone[];
  vesting: VestingSchedule;
  approvals: Approval[];
  metadata: AllocationMetadata;
}

export interface AllocationCondition {
  conditionId: string;
  type: 'time_lock' | 'milestone' | 'oracle' | 'governance' | 'legal' | 'technical';
  description: string;
  parameters: any;
  verified: boolean;
  verifiedAt?: string;
  verificationProof?: string;
}

export interface AllocationMilestone {
  milestoneId: string;
  title: string;
  description: string;
  deliverables: string[];
  deadline: string;
  amount: number;
  status: 'pending' | 'in_progress' | 'completed' | 'failed' | 'cancelled';
  completedAt?: string;
  evidence: MilestoneEvidence[];
  approvers: string[];
}

export interface MilestoneEvidence {
  evidenceId: string;
  type: 'document' | 'code_commit' | 'test_result' | 'audit_report' | 'screenshot' | 'video';
  url?: string;
  hash: string;
  description: string;
  uploadedAt: string;
  verified: boolean;
}

export interface VestingSchedule {
  scheduleId: string;
  totalAmount: number;
  cliffPeriod: number;
  vestingPeriod: number;
  releaseInterval: number;
  startDate: string;
  endDate: string;
  releasedAmount: number;
  remainingAmount: number;
  releases: VestingRelease[];
}

export interface VestingRelease {
  releaseId: string;
  timestamp: string;
  amount: number;
  percentage: number;
  reason: string;
  transactionId: string;
}

export interface Approval {
  approvalId: string;
  approver: string;
  role: 'treasurer' | 'governor' | 'multi_sig' | 'oracle';
  decision: 'approve' | 'reject' | 'conditional';
  timestamp: string;
  reason: string;
  conditions?: string[];
  signature: string;
}

export interface AllocationMetadata {
  category: string;
  priority: 'low' | 'medium' | 'high' | 'critical';
  tags: string[];
  references: string[];
  attachments: Attachment[];
  riskAssessment: RiskAssessment;
}

export interface RiskAssessment {
  riskLevel: 'low' | 'medium' | 'high' | 'critical';
  riskFactors: RiskFactor[];
  mitigation: string[];
  insurance: boolean;
  insuranceProvider?: string;
  insuranceCoverage?: number;
}

export interface RiskFactor {
  factor: string;
  impact: 'low' | 'medium' | 'high' | 'critical';
  probability: 'low' | 'medium' | 'high' | 'critical';
  description: string;
}

export interface Budget {
  budgetId: string;
  name: string;
  description: string;
  currencyId: string;
  totalAmount: number;
  allocatedAmount: number;
  spentAmount: number;
  department?: string;
  project?: string;
  costCenter?: string;
  manager?: string;
  reviewers: string[];
  tags: string[];
  notes: string;
  remainingAmount: number;
  period: BudgetPeriod;
  categories: BudgetCategory[];
  status: 'draft' | 'active' | 'completed' | 'cancelled';
  createdAt: string;
  approvedAt?: string;
  expiresAt?: string;
  controls: BudgetControls;
  metadata: BudgetMetadata;
}

export interface BudgetPeriod {
  periodId: string;
  type: 'monthly' | 'quarterly' | 'annual' | 'custom';
  startDate: string;
  endDate: string;
  fiscalYear?: number;
  quarter?: number;
  month?: number;
}

export interface BudgetCategory {
  categoryId: string;
  name: string;
  description: string;
  allocatedAmount: number;
  spentAmount: number;
  remainingAmount: number;
  subcategories: BudgetSubcategory[];
}

export interface BudgetSubcategory {
  subcategoryId: string;
  name: string;
  allocatedAmount: number;
  spentAmount: number;
  remainingAmount: number;
  items: BudgetItem[];
}

export interface BudgetItem {
  itemId: string;
  name: string;
  description: string;
  allocatedAmount: number;
  spentAmount: number;
  vendor?: string;
  invoiceId?: string;
  receiptId?: string;
  status: 'planned' | 'approved' | 'in_progress' | 'completed' | 'cancelled';
}

export interface BudgetControls {
  requireApproval: boolean;
  approvalThreshold: number;
  spendingLimits: SpendingLimit[];
  timeLocks: TimeLock[];
  multiSigRequired: boolean;
  multiSigThreshold: number;
  oracleVerification: boolean;
}

export interface SpendingLimit {
  limitId: string;
  type: 'daily' | 'weekly' | 'monthly' | 'quarterly' | 'annual' | 'per_transaction';
  amount: number;
  currencyId: string;
  categories: string[];
  exceptions: string[];
}

export interface TimeLock {
  lockId: string;
  type: 'minimum_age' | 'time_delay' | 'vesting_period' | 'emergency_override';
  duration: number;
  conditions: string[];
  overrideConditions: string[];
}

export interface BudgetMetadata {
  department?: string;
  project?: string;
  costCenter?: string;
  manager: string;
  reviewers: string[];
  tags: string[];
  notes: string;
}

export interface TreasuryTransaction {
  transactionId: string;
  type: 'deposit' | 'withdrawal' | 'allocation' | 'refund' | 'adjustment' | 'fee' | 'interest' | 'swap';
  amount: number;
  currencyId: string;
  fromAddress?: string;
  toAddress?: string;
  referenceId?: string;
  referenceType?: 'allocation' | 'budget' | 'invoice' | 'payment' | 'refund';
  status: 'pending' | 'confirmed' | 'failed' | 'reverted';
  timestamp: string;
  confirmedAt?: string;
  blockNumber?: number;
  transactionHash?: string;
  gasUsed?: number;
  gasPrice?: number;
  fee: number;
  feeCurrency: string;
  metadata: TransactionMetadata;
}

export interface TransactionMetadata {
  description: string;
  category: string;
  tags: string[];
  attachments: Attachment[];
  approvals: Approval[];
  riskScore: number;
  compliance: ComplianceInfo;
}

export interface ComplianceInfo {
  kycVerified: boolean;
  amlChecked: boolean;
  sanctionsScreened: boolean;
  riskRating: string;
  jurisdiction: string;
  reportingRequirements: string[];
}

export interface TreasuryControls {
  multiSigRequired: boolean;
  multiSigThreshold: number;
  spendingLimits: SpendingLimit[];
  timeLocks: TimeLock[];
  oracleVerification: boolean;
  emergencyProcedures: EmergencyProcedure[];
  auditFrequency: number;
  auditThreshold: number;
  reportingRequirements: ReportingRequirement[];
}

export interface EmergencyProcedure {
  procedureId: string;
  triggerConditions: string[];
  authorizedSignatories: string[];
  reducedRequirements: EmergencyReduction;
  timeWindow: number;
  reporting: string[];
}

export interface EmergencyReduction {
  multiSigThreshold: number;
  timeLockReduction: number;
  spendingLimitIncrease: number;
  approvalThresholdReduction: number;
}

export interface ReportingRequirement {
  requirementId: string;
  type: 'financial' | 'operational' | 'compliance' | 'performance';
  frequency: 'daily' | 'weekly' | 'monthly' | 'quarterly' | 'annual';
  format: string[];
  recipients: string[];
  content: string[];
  deadline: number;
  autoGenerate: boolean;
}

export interface AuditTrail {
  auditId: string;
  entries: AuditEntry[];
  reports: AuditReport[];
  findings: AuditFinding[];
  recommendations: AuditRecommendation[];
  lastAudit: string;
  nextAudit: string;
}

export interface AuditEntry {
  entryId: string;
  timestamp: string;
  actor: string;
  action: string;
  resource: string;
  details: any;
  ipAddress?: string;
  userAgent?: string;
  sessionId?: string;
  riskLevel: 'low' | 'medium' | 'high' | 'critical';
}

export interface AuditReport {
  reportId: string;
  type: 'financial' | 'operational' | 'compliance' | 'security';
  period: AuditPeriod;
  scope: string[];
  findings: AuditFinding[];
  recommendations: AuditRecommendation[];
  status: 'in_progress' | 'completed' | 'failed';
  createdAt: string;
  completedAt?: string;
  auditor: string;
  score: number;
}

export interface AuditPeriod {
  startDate: string;
  endDate: string;
  type: 'regular' | 'emergency' | 'investigation';
}

export interface AuditFinding {
  findingId: string;
  severity: 'low' | 'medium' | 'high' | 'critical';
  category: string;
  description: string;
  impact: string;
  recommendation: string;
  status: 'open' | 'in_progress' | 'resolved' | 'accepted_risk';
  discoveredAt: string;
  resolvedAt?: string;
}

export interface AuditRecommendation {
  recommendationId: string;
  priority: 'low' | 'medium' | 'high' | 'critical';
  description: string;
  implementation: string;
  deadline: string;
  assignee?: string;
  status: 'pending' | 'in_progress' | 'completed' | 'overdue';
  createdAt: string;
  completedAt?: string;
}

export interface TreasuryMetadata {
  description: string;
  jurisdiction: string;
  taxId?: string;
  regulatoryCompliance: RegulatoryCompliance;
  insurance: InsuranceInfo;
  custodian: string;
  auditors: string[];
  created: string;
  lastUpdated: string;
}

export interface RegulatoryCompliance {
  frameworks: string[];
  licenses: string[];
  reportingObligations: ReportingObligation[];
  amlKycRequirements: AMLKYCRequirement[];
  dataProtection: DataProtectionRequirement[];
}

export interface ReportingObligation {
  obligationId: string;
  type: string;
  frequency: string;
  format: string[];
  authority: string;
  deadline: number;
  status: 'compliant' | 'non_compliant' | 'pending';
  lastFiled?: string;
}

export interface AMLKYCRequirement {
  requirementId: string;
  type: 'kyc' | 'aml' | 'sanctions' | 'transaction_monitoring';
  level: 'basic' | 'enhanced' | 'institutional';
  procedures: string[];
  thresholds: any[];
  status: 'compliant' | 'non_compliant' | 'pending';
  lastVerified?: string;
}

export interface DataProtectionRequirement {
  requirementId: string;
  framework: string;
  dataTypes: string[];
  storageLocation: string;
  retentionPeriod: number;
  encryption: string;
  accessControls: string[];
  breachProcedures: string[];
  status: 'compliant' | 'non_compliant' | 'pending';
  lastAssessed?: string;
}

export interface InsuranceInfo {
  provider: string;
  policyNumber: string;
  coverage: InsuranceCoverage[];
  premium: number;
  currency: string;
  deductible: number;
  coverageLimit: number;
  validFrom: string;
  validTo: string;
  claims: InsuranceClaim[];
}

export interface InsuranceCoverage {
  coverageId: string;
  type: 'theft' | 'loss' | 'fraud' | 'error' | 'business_interruption';
  amount: number;
  currency: string;
  conditions: string[];
  exclusions: string[];
}

export interface InsuranceClaim {
  claimId: string;
  type: string;
  amount: number;
  description: string;
  incidentDate: string;
  reportedDate: string;
  status: 'pending' | 'investigating' | 'approved' | 'rejected' | 'paid';
  resolvedAt?: string;
  paidAmount?: number;
  evidence: Attachment[];
}

/**
 * Treasury Manager
 */
export class TreasuryManager {
  private crypto: ProductionCrypto;
  private cubicSignature: CubicSignature;
  private treasuries: Map<string, Treasury> = new Map();
  private tokens: Map<string, Token> = new Map();

  constructor() {
    this.crypto = new ProductionCrypto();
    this.cubicSignature = new CubicSignature();
  }

  /**
   * Create new treasury
   */
  async createTreasury(
    name: string,
    daoId: string,
    currencies: string[],
    controls: Partial<TreasuryControls> = {},
    metadata: Partial<TreasuryMetadata> = {}
  ): Promise<Treasury> {
    const treasuryId = await this.generateTreasuryId();
    const timestamp = new Date().toISOString();

    // Initialize currency balances
    const currencyBalances = new Map<string, CurrencyBalance>();
    for (const currencyId of currencies) {
      const token = this.tokens.get(currencyId);
      if (!token) {
        throw new Error(`Token not found: ${currencyId}`);
      }

      currencyBalances.set(currencyId, {
        currencyId,
        balance: 0,
        lockedBalance: 0,
        allocatedBalance: 0,
        availableBalance: 0,
        lastUpdated: timestamp,
        metadata: {
          decimals: token.decimals,
          symbol: token.symbol,
          name: token.name,
          type: token.type as "native" | "wrapped" | "stablecoin" | "governance",
          lastPrice: 1,
          priceSource: 'internal',
          priceTimestamp: timestamp
        }
      });
    }

    const treasury: Treasury = {
      treasuryId,
      name,
      daoId,
      currencies: currencyBalances,
      allocations: new Map(),
      budgets: new Map(),
      transactions: new Map(),
      controls: {
        multiSigRequired: true,
        multiSigThreshold: 2,
        spendingLimits: [],
        timeLocks: [],
        oracleVerification: false,
        emergencyProcedures: [],
        auditFrequency: 30 * 24 * 60 * 60 * 1000, // 30 days
        auditThreshold: 10000,
        reportingRequirements: [],
        ...controls
      },
      audit: {
        auditId: await this.generateAuditId(),
        entries: [],
        reports: [],
        findings: [],
        recommendations: [],
        lastAudit: timestamp,
        nextAudit: new Date(Date.now() + (30 * 24 * 60 * 60 * 1000)).toISOString()
      },
      metadata: {
        description: '',
        jurisdiction: 'global',
        regulatoryCompliance: {
          frameworks: [],
          licenses: [],
          reportingObligations: [],
          amlKycRequirements: [],
          dataProtection: []
        },
        insurance: {
          provider: '',
          policyNumber: '',
          coverage: [],
          premium: 0,
          currency: 'USD',
          deductible: 0,
          coverageLimit: 0,
          validFrom: timestamp,
          validTo: new Date(Date.now() + 365 * 24 * 60 * 60 * 1000).toISOString(),
          claims: []
        },
        custodian: '',
        auditors: [],
        created: timestamp,
        lastUpdated: timestamp,
        ...metadata
      }
    };

    this.treasuries.set(treasuryId, treasury);
    
    console.log(`Treasury created: ${name} (${treasuryId})`);
    return treasury;
  }

  /**
   * Deposit funds to treasury
   */
  async depositFunds(
    treasuryId: string,
    currencyId: string,
    amount: number,
    fromAddress: string,
    reason: string
  ): Promise<string> {
    const treasury = this.treasuries.get(treasuryId);
    if (!treasury) {
      throw new Error(`Treasury not found: ${treasuryId}`);
    }

    const currencyBalance = treasury.currencies.get(currencyId);
    if (!currencyBalance) {
      throw new Error(`Currency not supported: ${currencyId}`);
    }

    // Create transaction
    const transactionId = await this.generateTransactionId();
    const transaction: TreasuryTransaction = {
      transactionId,
      type: 'deposit',
      amount,
      currencyId,
      fromAddress,
      status: 'pending',
      timestamp: new Date().toISOString(),
      fee: 0,
      feeCurrency: currencyId,
      metadata: {
        description: reason,
        category: 'deposit',
        tags: [],
        attachments: [],
        approvals: [],
        riskScore: 0,
        compliance: {
          kycVerified: false,
          amlChecked: false,
          sanctionsScreened: false,
          riskRating: 'low',
          jurisdiction: treasury.metadata.jurisdiction,
          reportingRequirements: []
        }
      }
    };

    // Update currency balance
    currencyBalance.balance += amount;
    currencyBalance.availableBalance += amount;
    currencyBalance.lastUpdated = new Date().toISOString();

    // Add transaction
    treasury.transactions.set(transactionId, transaction);

    // Add audit entry
    await this.addAuditEntry(treasuryId, 'deposit', 'currency_balance', {
      currencyId,
      amount,
      fromAddress,
      transactionId
    });

    console.log(`Deposited ${amount} ${currencyId} to treasury ${treasuryId}`);
    return transactionId;
  }

  /**
   * Create allocation
   */
  async createAllocation(
    treasuryId: string,
    budgetId: string,
    recipient: string,
    amount: number,
    currencyId: string,
    purpose: string,
    conditions: AllocationCondition[] = [],
    milestones: AllocationMilestone[] = [],
    vesting: Partial<VestingSchedule> = {},
    metadata: Partial<AllocationMetadata> = {}
  ): Promise<Allocation> {
    const treasury = this.treasuries.get(treasuryId);
    if (!treasury) {
      throw new Error(`Treasury not found: ${treasuryId}`);
    }

    const currencyBalance = treasury.currencies.get(currencyId);
    if (!currencyBalance || currencyBalance.availableBalance < amount) {
      throw new Error('Insufficient funds available');
    }

    const allocationId = await this.generateAllocationId();
    const timestamp = new Date().toISOString();

    const allocation: Allocation = {
      allocationId,
      budgetId,
      recipient,
      amount,
      currencyId,
      purpose,
      status: 'pending',
      createdAt: timestamp,
      conditions,
      milestones,
      vesting: {
        scheduleId: await this.generateVestingId(),
        totalAmount: amount,
        cliffPeriod: 0,
        vestingPeriod: 0,
        releaseInterval: 0,
        startDate: timestamp,
        endDate: timestamp,
        releasedAmount: 0,
        remainingAmount: amount,
        releases: [],
        ...vesting
      },
      approvals: [],
      metadata: {
        category: 'general',
        priority: 'medium',
        tags: [],
        references: [],
        attachments: [],
        riskAssessment: {
          riskLevel: 'low',
          riskFactors: [],
          mitigation: [],
          insurance: false
        },
        ...metadata
      }
    };

    // Lock funds
    currencyBalance.allocatedBalance += amount;
    currencyBalance.availableBalance -= amount;
    currencyBalance.lastUpdated = timestamp;

    // Add allocation
    treasury.allocations.set(allocationId, allocation);

    // Add audit entry
    await this.addAuditEntry(treasuryId, 'create_allocation', 'allocation', {
      allocationId,
      recipient,
      amount,
      currencyId,
      purpose
    });

    console.log(`Allocation created: ${allocationId} for ${recipient} (${amount} ${currencyId})`);
    return allocation;
  }

  /**
   * Approve allocation
   */
  async approveAllocation(
    treasuryId: string,
    allocationId: string,
    approver: string,
    decision: 'approve' | 'reject' | 'conditional',
    reason: string,
    conditions?: string[]
  ): Promise<void> {
    const treasury = this.treasuries.get(treasuryId);
    if (!treasury) {
      throw new Error(`Treasury not found: ${treasuryId}`);
    }

    const allocation = treasury.allocations.get(allocationId);
    if (!allocation) {
      throw new Error(`Allocation not found: ${allocationId}`);
    }

    if (allocation.status !== 'pending') {
      throw new Error('Allocation is not pending approval');
    }

    // Create approval
    const approval: Approval = {
      approvalId: await this.generateApprovalId(),
      approver,
      role: 'treasurer',
      decision,
      timestamp: new Date().toISOString(),
      reason,
      conditions,
      signature: await this.createApprovalSignature(allocationId, approver, decision)
    };

    allocation.approvals.push(approval);

    // Check if allocation is approved
    const approvalCount = allocation.approvals.filter(a => a.decision === 'approve').length;
    const requiredApprovals = treasury.controls.multiSigThreshold || 1;

    if (approvalCount >= requiredApprovals) {
      allocation.status = 'approved';
      allocation.approvedAt = new Date().toISOString();

      // Execute allocation if conditions are met
      if (await this.checkAllocationConditions(allocation)) {
        await this.executeAllocation(treasuryId, allocationId);
      }
    } else if (decision === 'reject') {
      allocation.status = 'cancelled';
    }

    // Add audit entry
    await this.addAuditEntry(treasuryId, 'approve_allocation', 'allocation', {
      allocationId,
      approver,
      decision,
      reason
    });

    console.log(`Allocation ${allocationId} ${decision} by ${approver}`);
  }

  /**
   * Execute allocation
   */
  async executeAllocation(
    treasuryId: string,
    allocationId: string
  ): Promise<string> {
    const treasury = this.treasuries.get(treasuryId);
    if (!treasury) {
      throw new Error(`Treasury not found: ${treasuryId}`);
    }

    const allocation = treasury.allocations.get(allocationId);
    if (!allocation) {
      throw new Error(`Allocation not found: ${allocationId}`);
    }

    if (allocation.status !== 'approved') {
      throw new Error('Allocation is not approved');
    }

    const currencyBalance = treasury.currencies.get(allocation.currencyId);
    if (!currencyBalance) {
      throw new Error(`Currency not found: ${allocation.currencyId}`);
    }

    // Create transaction
    const transactionId = await this.generateTransactionId();
    const transaction: TreasuryTransaction = {
      transactionId,
      type: 'allocation',
      amount: allocation.amount,
      currencyId: allocation.currencyId,
      toAddress: allocation.recipient,
      referenceId: allocationId,
      referenceType: 'allocation',
      status: 'confirmed',
      timestamp: new Date().toISOString(),
      confirmedAt: new Date().toISOString(),
      fee: 0,
      feeCurrency: allocation.currencyId,
      metadata: {
        description: allocation.purpose,
        category: 'allocation',
        tags: [],
        attachments: [],
        approvals: allocation.approvals,
        riskScore: allocation.metadata.riskAssessment.riskLevel === 'critical' ? 10 : 1,
        compliance: {
          kycVerified: true,
          amlChecked: true,
          sanctionsScreened: true,
          riskRating: 'low',
          jurisdiction: treasury.metadata.jurisdiction,
          reportingRequirements: []
        }
      }
    };

    // Update currency balance
    currencyBalance.allocatedBalance -= allocation.amount;
    currencyBalance.lastUpdated = new Date().toISOString();

    // Update allocation status
    allocation.status = 'executed';
    allocation.executedAt = new Date().toISOString();

    // Add transaction
    treasury.transactions.set(transactionId, transaction);

    // Add audit entry
    await this.addAuditEntry(treasuryId, 'execute_allocation', 'allocation', {
      allocationId,
      recipient: allocation.recipient,
      amount: allocation.amount,
      currencyId: allocation.currencyId,
      transactionId
    });

    console.log(`Allocation executed: ${allocationId} (${allocation.amount} ${allocation.currencyId})`);
    return transactionId;
  }

  /**
   * Create budget
   */
  async createBudget(
    treasuryId: string,
    name: string,
    description: string,
    currencyId: string,
    totalAmount: number,
    period: BudgetPeriod,
    categories: BudgetCategory[] = [],
    controls: Partial<BudgetControls> = {},
    metadata: Partial<BudgetMetadata> = {}
  ): Promise<Budget> {
    const treasury = this.treasuries.get(treasuryId);
    if (!treasury) {
      throw new Error(`Treasury not found: ${treasuryId}`);
    }

    const budgetId = await this.generateBudgetId();
    const timestamp = new Date().toISOString();

    const budget: Budget = {
      budgetId,
      name,
      description,
      currencyId,
      totalAmount,
      allocatedAmount: 0,
      spentAmount: 0,
      remainingAmount: totalAmount,
      period,
      categories,
      status: 'draft',
      createdAt: timestamp,
      controls: {
        requireApproval: true,
        approvalThreshold: 0.5,
        spendingLimits: [],
        timeLocks: [],
        multiSigRequired: false,
        multiSigThreshold: 1,
        oracleVerification: false,
        ...controls
      },
      metadata: {
        tags: [],
        notes: '',
        reviewers: [],
        ...metadata
      }
    };

    treasury.budgets.set(budgetId, budget);

    // Add audit entry
    await this.addAuditEntry(treasuryId, 'create_budget', 'budget', {
      budgetId,
      name,
      totalAmount,
      currencyId
    });

    console.log(`Budget created: ${budgetId} (${name})`);
    return budget;
  }

  /**
   * Get treasury by ID
   */
  getTreasury(treasuryId: string): Treasury | null {
    return this.treasuries.get(treasuryId) || null;
  }

  /**
   * Get treasury balance
   */
  getTreasuryBalance(treasuryId: string): Map<string, CurrencyBalance> {
    const treasury = this.treasuries.get(treasuryId);
    return treasury ? treasury.currencies : new Map();
  }

  /**
   * Get allocations
   */
  getAllocations(
    treasuryId: string,
    filters: {
      status?: Allocation['status'];
      recipient?: string;
      currencyId?: string;
      limit?: number;
      offset?: number;
    } = {}
  ): Allocation[] {
    const treasury = this.treasuries.get(treasuryId);
    if (!treasury) return [];

    let allocations = Array.from(treasury.allocations.values());

    // Apply filters
    if (filters.status) {
      allocations = allocations.filter(a => a.status === filters.status);
    }
    if (filters.recipient) {
      allocations = allocations.filter(a => a.recipient === filters.recipient);
    }
    if (filters.currencyId) {
      allocations = allocations.filter(a => a.currencyId === filters.currencyId);
    }

    // Sort by creation date (newest first)
    allocations.sort((a, b) => new Date(b.createdAt).getTime() - new Date(a.createdAt).getTime());

    // Apply pagination
    if (filters.offset) {
      allocations = allocations.slice(filters.offset);
    }
    if (filters.limit) {
      allocations = allocations.slice(0, filters.limit);
    }

    return allocations;
  }

  /**
   * Get budgets
   */
  getBudgets(
    treasuryId: string,
    filters: {
      status?: Budget['status'];
      currencyId?: string;
      period?: BudgetPeriod;
      limit?: number;
      offset?: number;
    } = {}
  ): Budget[] {
    const treasury = this.treasuries.get(treasuryId);
    if (!treasury) return [];

    let budgets = Array.from(treasury.budgets.values());

    // Apply filters
    if (filters.status) {
      budgets = budgets.filter(b => b.status === filters.status);
    }
    if (filters.currencyId) {
      budgets = budgets.filter(b => b.currencyId === filters.currencyId);
    }
    if (filters.period) {
      budgets = budgets.filter(b => 
        b.period.startDate === filters.period.startDate &&
        b.period.endDate === filters.period.endDate
      );
    }

    // Sort by creation date (newest first)
    budgets.sort((a, b) => new Date(b.createdAt).getTime() - new Date(a.createdAt).getTime());

    // Apply pagination
    if (filters.offset) {
      budgets = budgets.slice(filters.offset);
    }
    if (filters.limit) {
      budgets = budgets.slice(0, filters.limit);
    }

    return budgets;
  }

  /**
   * Get transactions
   */
  getTransactions(
    treasuryId: string,
    filters: {
      type?: TreasuryTransaction['type'];
      currencyId?: string;
      status?: TreasuryTransaction['status'];
      startDate?: string;
      endDate?: string;
      limit?: number;
      offset?: number;
    } = {}
  ): TreasuryTransaction[] {
    const treasury = this.treasuries.get(treasuryId);
    if (!treasury) return [];

    let transactions = Array.from(treasury.transactions.values());

    // Apply filters
    if (filters.type) {
      transactions = transactions.filter(t => t.type === filters.type);
    }
    if (filters.currencyId) {
      transactions = transactions.filter(t => t.currencyId === filters.currencyId);
    }
    if (filters.status) {
      transactions = transactions.filter(t => t.status === filters.status);
    }
    if (filters.startDate) {
      transactions = transactions.filter(t => new Date(t.timestamp) >= new Date(filters.startDate));
    }
    if (filters.endDate) {
      transactions = transactions.filter(t => new Date(t.timestamp) <= new Date(filters.endDate));
    }

    // Sort by timestamp (newest first)
    transactions.sort((a, b) => new Date(b.timestamp).getTime() - new Date(a.timestamp).getTime());

    // Apply pagination
    if (filters.offset) {
      transactions = transactions.slice(filters.offset);
    }
    if (filters.limit) {
      transactions = transactions.slice(0, filters.limit);
    }

    return transactions;
  }

  /**
   * Get treasury statistics
   */
  getTreasuryStatistics(treasuryId: string): TreasuryStatistics {
    const treasury = this.treasuries.get(treasuryId);
    if (!treasury) {
      throw new Error(`Treasury not found: ${treasuryId}`);
    }

    const allocations = Array.from(treasury.allocations.values());
    const budgets = Array.from(treasury.budgets.values());
    const transactions = Array.from(treasury.transactions.values());

    const totalValue = Array.from(treasury.currencies.values())
      .reduce((sum, currency) => {
        const token = this.tokens.get(currency.currencyId);
        const price = token ? 1 : 1; // Simplified price calculation
        return sum + (currency.balance * price);
      }, 0);

    const allocatedValue = Array.from(treasury.currencies.values())
      .reduce((sum, currency) => {
        const token = this.tokens.get(currency.currencyId);
        const price = token ? 1 : 1;
        return sum + (currency.allocatedBalance * price);
      }, 0);

    const totalAllocations = allocations.length;
    const pendingAllocations = allocations.filter(a => a.status === 'pending').length;
    const activeAllocations = allocations.filter(a => a.status === 'executed').length;
    const totalBudgets = budgets.length;
    const activeBudgets = budgets.filter(b => b.status === 'active').length;

    return {
      totalValue,
      allocatedValue,
      availableValue: totalValue - allocatedValue,
      currencyBreakdown: new Map(Array.from(treasury.currencies.entries())),
      totalAllocations,
      pendingAllocations,
      activeAllocations,
      totalBudgets,
      activeBudgets,
      totalTransactions: transactions.length,
      recentTransactions: transactions
        .filter(t => Date.now() - new Date(t.timestamp).getTime() < 7 * 24 * 60 * 60 * 1000)
        .length,
      complianceScore: this.calculateComplianceScore(treasury),
      riskMetrics: this.calculateRiskMetrics(treasury),
      auditStatus: treasury.audit.findings.filter(f => f.severity === 'critical').length
    };
  }

  /**
   * Register token for treasury
   */
  registerToken(token: Token): void {
    this.tokens.set(token.tokenId, token);
  }

  /**
   * Private helper methods
   */
  private async checkAllocationConditions(allocation: Allocation): Promise<boolean> {
    // Check if all conditions are verified
    for (const condition of allocation.conditions) {
      if (!condition.verified) {
        return false;
      }
    }
    return true;
  }

  private async createApprovalSignature(
    allocationId: string,
    approver: string,
    decision: string
  ): Promise<string> {
    const signatureData = {
      allocationId,
      approver,
      decision,
      timestamp: new Date().toISOString()
    };

    return await this.crypto.hashData(JSON.stringify(signatureData));
  }

  private async addAuditEntry(
    treasuryId: string,
    action: string,
    resource: string,
    details: any
  ): Promise<void> {
    const treasury = this.treasuries.get(treasuryId);
    if (!treasury) return;

    const entry: AuditEntry = {
      entryId: await this.generateAuditEntryId(),
      timestamp: new Date().toISOString(),
      actor: 'system',
      action,
      resource,
      details,
      riskLevel: 'low'
    };

    treasury.audit.entries.push(entry);
  }

  private calculateComplianceScore(treasury: Treasury): number {
    // Simplified compliance score calculation
    let score = 100;

    // Deduct for critical audit findings
    score -= treasury.audit.findings.filter(f => f.severity === 'critical').length * 20;

    // Deduct for high audit findings
    score -= treasury.audit.findings.filter(f => f.severity === 'high').length * 10;

    // Deduct for overdue recommendations
    const now = Date.now();
    treasury.audit.recommendations.forEach(rec => {
      if (rec.status === 'overdue' || 
          (rec.status === 'pending' && new Date(rec.deadline).getTime() < now)) {
        score -= 5;
      }
    });

    return Math.max(0, score);
  }

  private calculateRiskMetrics(treasury: Treasury): RiskMetrics {
    const allocations = Array.from(treasury.allocations.values());
    const transactions = Array.from(treasury.transactions.values());

    const highRiskAllocations = allocations.filter(a => 
      a.metadata.riskAssessment.riskLevel === 'high' || 
      a.metadata.riskAssessment.riskLevel === 'critical'
    ).length;

    const failedTransactions = transactions.filter(t => t.status === 'failed').length;
    const totalTransactions = transactions.length;

    return {
      highRiskAllocations,
      totalAllocations: allocations.length,
      failedTransactions,
      totalTransactions,
      riskScore: totalTransactions > 0 ? (failedTransactions / totalTransactions) * 100 : 0,
      largestAllocation: allocations.length > 0 ? Math.max(...allocations.map(a => a.amount)) : 0,
      averageAllocationSize: allocations.length > 0 ? allocations.reduce((sum, a) => sum + a.amount, 0) / allocations.length : 0
    };
  }

  private async generateTreasuryId(): Promise<string> {
    const data = `treasury:${Date.now()}:${Math.random()}`;
    const hash = await this.crypto.hashData(data);
    return `treasury_${hash.substring(0, 16)}`;
  }

  private async generateAllocationId(): Promise<string> {
    const data = `allocation:${Date.now()}:${Math.random()}`;
    const hash = await this.crypto.hashData(data);
    return `alloc_${hash.substring(0, 16)}`;
  }

  private async generateBudgetId(): Promise<string> {
    const data = `budget:${Date.now()}:${Math.random()}`;
    const hash = await this.crypto.hashData(data);
    return `budget_${hash.substring(0, 16)}`;
  }

  private async generateTransactionId(): Promise<string> {
    const data = `transaction:${Date.now()}:${Math.random()}`;
    const hash = await this.crypto.hashData(data);
    return `tx_${hash.substring(0, 16)}`;
  }

  private async generateVestingId(): Promise<string> {
    const data = `vesting:${Date.now()}:${Math.random()}`;
    const hash = await this.crypto.hashData(data);
    return `vest_${hash.substring(0, 16)}`;
  }

  private async generateApprovalId(): Promise<string> {
    const data = `approval:${Date.now()}:${Math.random()}`;
    const hash = await this.crypto.hashData(data);
    return `approval_${hash.substring(0, 16)}`;
  }

  private async generateAuditId(): Promise<string> {
    const data = `audit:${Date.now()}:${Math.random()}`;
    const hash = await this.crypto.hashData(data);
    return `audit_${hash.substring(0, 16)}`;
  }

  private async generateAuditEntryId(): Promise<string> {
    const data = `audit_entry:${Date.now()}:${Math.random()}`;
    const hash = await this.crypto.hashData(data);
    return `audit_entry_${hash.substring(0, 16)}`;
  }
}

// Supporting interfaces
export interface TreasuryStatistics {
  totalValue: number;
  allocatedValue: number;
  availableValue: number;
  currencyBreakdown: Map<string, CurrencyBalance>;
  totalAllocations: number;
  pendingAllocations: number;
  activeAllocations: number;
  totalBudgets: number;
  activeBudgets: number;
  totalTransactions: number;
  recentTransactions: number;
  complianceScore: number;
  riskMetrics: RiskMetrics;
  auditStatus: number;
}

export interface RiskMetrics {
  highRiskAllocations: number;
  totalAllocations: number;
  failedTransactions: number;
  totalTransactions: number;
  riskScore: number;
  largestAllocation: number;
  averageAllocationSize: number;
}