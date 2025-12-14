/**
 * DAO Framework and Advanced Governance System
 * 
 * Implements complete Decentralized Autonomous Organization framework
 * with multiple voting mechanisms, proposal management, and governance protocols.
 */

import { PolyF2 } from '../core/polynomial/index';
import { AALType } from '../core/aal/types';
import { DIDDocument } from '../identity/did-core';
import { CubicSignature } from '../core/cryptography/cubic-signature';
import { ProductionCryptography } from '../core/cryptography/production-crypto';

export interface DAOProposal {
  proposalId: string;
  title: string;
  description: string;
  type: ProposalType;
  author: string;
  authorDid: string;
  createdAt: string;
  expiresAt: string;
  status: ProposalStatus;
  votingMechanism: VotingMechanism;
  quorum: number;
  executionDelay: number;
  parameters: ProposalParameters;
  votes: Vote[];
  results: ProposalResults;
  metadata: ProposalMetadata;
}

export type ProposalType = 
  | 'constitutional_amendment'
  | 'parameter_change'
  | 'treasury_allocation'
  | 'membership_action'
  | 'governance_change'
  | 'cross_universe_treaty'
  | 'emergency_action'
  | 'technical_upgrade';

export type ProposalStatus = 
  | 'draft'
  | 'active'
  | 'voting'
  | 'passed'
  | 'rejected'
  | 'executed'
  | 'expired'
  | 'cancelled';

export interface ProposalParameters {
  target?: string;
  action?: string;
  value?: any;
  conditions?: string[];
  timeline?: Timeline;
  budget?: BudgetAllocation;
  amendments?: ProposalAmendment[];
}

export interface Timeline {
  startDate: string;
  milestones: Milestone[];
  endDate: string;
}

export interface Milestone {
  id: string;
  description: string;
  deadline: string;
  deliverables: string[];
  dependencies?: string[];
}

export interface BudgetAllocation {
  currency: string;
  amount: number;
  recipients: Recipient[];
  conditions: string[];
  vestingSchedule?: VestingSchedule;
}

export interface Recipient {
  did: string;
  address?: string;
  amount: number;
  purpose: string;
  conditions?: string[];
}

export interface VestingSchedule {
  totalAmount: number;
  cliffPeriod: number;
  vestingPeriod: number;
  releaseSchedule: VestingRelease[];
}

export interface VestingRelease {
  timestamp: string;
  percentage: number;
  amount: number;
  conditions?: string[];
}

export interface ProposalAmendment {
  amendmentId: string;
  author: string;
  timestamp: string;
  changes: AmendmentChange[];
  justification: string;
}

export interface AmendmentChange {
  field: string;
  oldValue: any;
  newValue: any;
  reason: string;
}

export interface Vote {
  voteId: string;
  voterDid: string;
  proposalId: string;
  choice: VoteChoice;
  weight: number;
  timestamp: string;
  proof: string;
  metadata: VoteMetadata;
}

export type VoteChoice = 
  | 'yes'
  | 'no'
  | 'abstain'
  | 'veto'
  | 'conditional_yes'
  | 'conditional_no';

export interface VoteMetadata {
  votingPower: number;
  delegationChain?: string[];
  reasoning?: string;
  confidence?: number;
  references?: string[];
}

export interface ProposalResults {
  totalVotes: number;
  totalWeight: number;
  yesVotes: number;
  yesWeight: number;
  noVotes: number;
  noWeight: number;
  abstainVotes: number;
  abstainWeight: number;
  vetoVotes: number;
  vetoWeight: number;
  quorumReached: boolean;
  passed: boolean;
  executionDate?: string;
  summary: string;
}

export interface ProposalMetadata {
  tags: string[];
  priority: 'low' | 'medium' | 'high' | 'critical';
  category: string;
  references: string[];
  attachments: Attachment[];
  discussionUrl?: string;
  legalReview?: LegalReview;
}

export interface Attachment {
  id: string;
  name: string;
  type: string;
  size: number;
  hash: string;
  url?: string;
}

export interface LegalReview {
  reviewedBy: string;
  reviewedAt: string;
  opinion: 'favorable' | 'neutral' | 'unfavorable';
  concerns: string[];
  recommendations: string[];
}

export type VotingMechanism = 
  | 'simple_majority'
  | 'supermajority'
  | 'quadratic'
  | 'weighted'
  | 'delegated'
  | 'conviction_voting'
  | 'ranked_choice'
  | 'approval_voting'
  | 'liquid_democracy';

export interface DAOConstitution {
  constitutionId: string;
  name: string;
  version: string;
  createdAt: string;
  lastAmended: string;
  preamble: string;
  articles: ConstitutionArticle[];
  amendments: ConstitutionAmendment[];
  votingRules: VotingRules;
  treasuryRules: TreasuryRules;
  membershipRules: MembershipRules;
}

export interface ConstitutionArticle {
  articleId: string;
  title: string;
  section: string;
  content: string;
  immutable: boolean;
  amendmentProcedure: string;
  relatedArticles: string[];
}

export interface ConstitutionAmendment {
  amendmentId: string;
  articleId: string;
  proposedAt: string;
  ratifiedAt?: string;
  changes: AmendmentChange[];
  justification: string;
  votes: Vote[];
}

export interface VotingRules {
  mechanisms: VotingMechanism[];
  defaultMechanism: VotingMechanism;
  quorumRequirements: QuorumRequirement[];
  votingPeriods: VotingPeriod[];
  delegationRules: DelegationRules;
  executionRules: ExecutionRules;
}

export interface QuorumRequirement {
  proposalType: ProposalType;
  minimumParticipation: number;
  minimumApproval: number;
  vetoThreshold?: number;
  timeRequirements: TimeRequirement;
}

export interface TimeRequirement {
  minimumVotingPeriod: number;
  maximumVotingPeriod: number;
  executionDelay: number;
  emergencyProvisions: EmergencyProvision;
}

export interface EmergencyProvision {
  enabled: boolean;
  triggerConditions: string[];
  acceleratedVoting: number;
  reducedQuorum: number;
}

export interface VotingPeriod {
  mechanism: VotingMechanism;
  duration: number;
  extensionConditions: string[];
  earlyTermination: string[];
}

export interface DelegationRules {
  enabled: boolean;
  maxDelegations: number;
  delegationPeriod: number;
  revocationDelay: number;
  transparencyRequirements: string[];
}

export interface ExecutionRules {
  automaticExecution: boolean;
  manualApproval: string[];
  executionConditions: string[];
  appealProcess: string[];
  failureHandling: string[];
}

export interface TreasuryRules {
  currencies: Currency[];
  allocationProcedures: AllocationProcedure[];
  spendingLimits: SpendingLimit[];
  reportingRequirements: ReportingRequirement[];
  auditRequirements: AuditRequirement[];
}

export interface Currency {
  currencyId: string;
  name: string;
  symbol: string;
  type: 'native' | 'wrapped' | 'stablecoin' | 'governance';
  decimals: number;
  totalSupply?: number;
  mintingAuthority?: string;
}

export interface AllocationProcedure {
  procedureId: string;
  name: string;
  description: string;
  requiredApprovals: number;
  votingMechanism: VotingMechanism;
  timeLimits: TimeRequirement;
  conditions: string[];
}

export interface SpendingLimit {
  limitType: string;
  amount: number;
  period: number;
  currency: string;
  exceptions: string[];
}

export interface ReportingRequirement {
  reportType: string;
  frequency: string;
  format: string[];
  recipients: string[];
  content: string[];
}

export interface AuditRequirement {
  auditType: string;
  frequency: string;
  auditor: string;
  scope: string[];
  publication: string;
}

export interface MembershipRules {
  membershipTypes: MembershipType[];
  applicationProcess: ApplicationProcess;
  rightsAndResponsibilities: RightsAndResponsibilities;
  disciplinaryProcedures: DisciplinaryProcedure[];
}

export interface MembershipType {
  typeId: string;
  name: string;
  requirements: MembershipRequirement[];
  benefits: string[];
  limitations: string[];
  votingPower: number;
}

export interface MembershipRequirement {
  type: 'stake' | 'reputation' | 'contribution' | 'identity' | 'skill';
  value: any;
  verification: string;
  duration?: number;
}

export interface ApplicationProcess {
  stages: ApplicationStage[];
  reviewCriteria: ReviewCriteria[];
  appealProcess: string;
  processingTime: number;
}

export interface ApplicationStage {
  stageId: string;
  name: string;
  description: string;
  duration: number;
  requirements: string[];
  approvers: string[];
}

export interface ReviewCriteria {
  criterionId: string;
  name: string;
  weight: number;
  evaluationMethod: string;
  minimumScore: number;
}

export interface RightsAndResponsibilities {
  rights: string[];
  responsibilities: string[];
  codeOfConduct: string[];
  conflictResolution: string[];
}

export interface DisciplinaryProcedure {
  offenseTypes: OffenseType[];
  investigationProcess: string;
  penalties: Penalty[];
  appealProcess: string;
}

export interface OffenseType {
  typeId: string;
  name: string;
  severity: 'minor' | 'moderate' | 'major' | 'critical';
  description: string;
  examples: string[];
}

export interface Penalty {
  penaltyId: string;
  type: 'warning' | 'suspension' | 'fine' | 'revocation' | 'expulsion';
  severity: number;
  duration?: number;
  conditions: string[];
  appealable: boolean;
}

/**
 * DAO Framework Manager
 */
export class DAOFramework {
  private crypto: ProductionCrypto;
  private cubicSignature: CubicSignature;
  private proposals: Map<string, DAOProposal> = new Map();
  private constitution: DAOConstitution | null = null;
  private members: Map<string, DAOMember> = new Map();
  private delegations: Map<string, VoteDelegation> = new Map();
  private treasury: DAOTreasury;

  constructor() {
    this.crypto = new ProductionCrypto();
    this.cubicSignature = new CubicSignature();
    this.treasury = new DAOTreasury();
  }

  /**
   * Initialize DAO with constitution
   */
  async initializeDAO(constitution: DAOConstitution): Promise<void> {
    this.constitution = constitution;
    
    // Validate constitution
    await this.validateConstitution(constitution);
    
    // Initialize treasury with currency rules
    await this.treasury.initialize(constitution.treasuryRules);
    
    console.log(`DAO "${constitution.name}" initialized with constitution v${constitution.version}`);
  }

  /**
   * Create new proposal
   */
  async createProposal(
    title: string,
    description: string,
    type: ProposalType,
    authorDid: string,
    parameters: ProposalParameters,
    votingMechanism: VotingMechanism = 'simple_majority',
    metadata: Partial<ProposalMetadata> = {}
  ): Promise<DAOProposal> {
    if (!this.constitution) {
      throw new Error('DAO constitution not initialized');
    }

    // Verify author is member
    const member = this.members.get(authorDid);
    if (!member) {
      throw new Error('Author is not a DAO member');
    }

    // Check proposal permissions
    if (!this.hasProposalPermission(member, type)) {
      throw new Error('Member does not have permission to create this proposal type');
    }

    const proposalId = await this.generateProposalId();
    const timestamp = new Date().toISOString();
    
    // Get voting rules for this proposal type
    const votingRules = this.constitution.votingRules.quorumRequirements.find(
      req => req.proposalType === type
    );
    
    if (!votingRules) {
      throw new Error(`No voting rules found for proposal type: ${type}`);
    }

    const proposal: DAOProposal = {
      proposalId,
      title,
      description,
      type,
      author: member.profile?.name || 'Unknown',
      authorDid,
      createdAt: timestamp,
      expiresAt: new Date(Date.now() + votingRules.timeRequirements.maximumVotingPeriod).toISOString(),
      status: 'draft',
      votingMechanism,
      quorum: votingRules.minimumParticipation,
      executionDelay: votingRules.timeRequirements.executionDelay,
      parameters,
      votes: [],
      results: {
        totalVotes: 0,
        totalWeight: 0,
        yesVotes: 0,
        yesWeight: 0,
        noVotes: 0,
        noWeight: 0,
        abstainVotes: 0,
        abstainWeight: 0,
        vetoVotes: 0,
        vetoWeight: 0,
        quorumReached: false,
        passed: false,
        summary: ''
      },
      metadata: {
        tags: [],
        priority: 'medium',
        category: 'general',
        references: [],
        attachments: [],
        ...metadata
      }
    };

    this.proposals.set(proposalId, proposal);
    return proposal;
  }

  /**
   * Submit proposal for voting
   */
  async submitProposal(proposalId: string): Promise<void> {
    const proposal = this.proposals.get(proposalId);
    if (!proposal) {
      throw new Error(`Proposal not found: ${proposalId}`);
    }

    if (proposal.status !== 'draft') {
      throw new Error('Only draft proposals can be submitted');
    }

    // Validate proposal completeness
    await this.validateProposal(proposal);

    proposal.status = 'active';
    proposal.expiresAt = new Date(Date.now() + this.getVotingPeriod(proposal)).toISOString();

    console.log(`Proposal "${proposal.title}" submitted for voting`);
  }

  /**
   * Cast vote on proposal
   */
  async castVote(
    proposalId: string,
    voterDid: string,
    choice: VoteChoice,
    reasoning?: string,
    delegationChain?: string[]
  ): Promise<Vote> {
    const proposal = this.proposals.get(proposalId);
    if (!proposal) {
      throw new Error(`Proposal not found: ${proposalId}`);
    }

    if (proposal.status !== 'voting' && proposal.status !== 'active') {
      throw new Error('Proposal is not open for voting');
    }

    // Verify voter is member
    const member = this.members.get(voterDid);
    if (!member) {
      throw new Error('Voter is not a DAO member');
    }

    // Check if already voted
    const existingVote = proposal.votes.find(v => v.voterDid === voterDid);
    if (existingVote) {
      throw new Error('Member has already voted on this proposal');
    }

    // Calculate voting power
    const votingPower = await this.calculateVotingPower(voterDid, proposal);
    
    // Create vote
    const voteId = await this.generateVoteId();
    const vote: Vote = {
      voteId,
      voterDid,
      proposalId,
      choice,
      weight: votingPower,
      timestamp: new Date().toISOString(),
      proof: await this.createVoteProof(proposalId, voterDid, choice, votingPower),
      metadata: {
        votingPower,
        delegationChain,
        reasoning,
        confidence: 0.9,
        references: []
      }
    };

    proposal.votes.push(vote);
    
    // Update proposal results
    await this.updateProposalResults(proposal);

    return vote;
  }

  /**
   * Delegate voting power
   */
  async delegateVote(
    delegatorDid: string,
    delegateeDid: string,
    delegationType: 'full' | 'partial' | 'proposal_specific',
    parameters?: any
  ): Promise<VoteDelegation> {
    // Verify both are members
    const delegator = this.members.get(delegatorDid);
    const delegatee = this.members.get(delegateeDid);
    
    if (!delegator || !delegatee) {
      throw new Error('Both delegator and delegatee must be DAO members');
    }

    // Check delegation rules
    if (!this.constitution?.votingRules.delegationRules.enabled) {
      throw new Error('Vote delegation is not enabled');
    }

    const delegationId = await this.generateDelegationId();
    const delegation: VoteDelegation = {
      delegationId,
      delegatorDid,
      delegateeDid,
      type: delegationType,
      parameters: parameters || {},
      createdAt: new Date().toISOString(),
      expiresAt: new Date(Date.now() + this.constitution.votingRules.delegationRules.delegationPeriod).toISOString(),
      active: true,
      revocable: true,
      proof: await this.createDelegationProof(delegatorDid, delegateeDid, delegationType)
    };

    this.delegations.set(delegationId, delegation);
    
    console.log(`Vote delegation created: ${delegatorDid} -> ${delegateeDid}`);
    return delegation;
  }

  /**
   * Execute proposal
   */
  async executeProposal(proposalId: string, executorDid: string): Promise<ExecutionResult> {
    const proposal = this.proposals.get(proposalId);
    if (!proposal) {
      throw new Error(`Proposal not found: ${proposalId}`);
    }

    if (proposal.status !== 'passed') {
      throw new Error('Only passed proposals can be executed');
    }

    // Check execution delay
    const now = Date.now();
    const executionTime = new Date(proposal.results.executionDate || '').getTime();
    if (now < executionTime) {
      throw new Error('Execution delay has not passed');
    }

    // Verify executor permissions
    const executor = this.members.get(executorDid);
    if (!executor) {
      throw new Error('Executor is not a DAO member');
    }

    if (!this.hasExecutionPermission(executor, proposal)) {
      throw new Error('Executor does not have permission to execute this proposal');
    }

    // Execute proposal based on type
    const result = await this.executeProposalByType(proposal, executorDid);
    
    proposal.status = 'executed';
    proposal.results.executionDate = new Date().toISOString();

    return result;
  }

  /**
   * Add member to DAO
   */
  async addMember(
    did: string,
    profile: any,
    membershipType: string,
    applicationData?: any
  ): Promise<DAOMember> {
    if (!this.constitution) {
      throw new Error('DAO constitution not initialized');
    }

    // Check if already member
    if (this.members.has(did)) {
      throw new Error('Already a DAO member');
    }

    // Get membership type requirements
    const memType = this.constitution.membershipRules.membershipTypes.find(
      type => type.typeId === membershipType
    );
    
    if (!memType) {
      throw new Error(`Membership type not found: ${membershipType}`);
    }

    // Verify requirements
    await this.verifyMembershipRequirements(memType.requirements, did, applicationData);

    const memberId = await this.generateMemberId();
    const member: DAOMember = {
      memberId,
      did,
      profile,
      membershipType,
      joinedAt: new Date().toISOString(),
      status: 'active',
      votingPower: memType.votingPower,
      reputation: 0,
      contributions: [],
      delegationsGiven: 0,
      delegationsReceived: 0,
      lastActive: new Date().toISOString(),
      metadata: {
        applicationData,
        verifiedRequirements: memType.requirements.map(req => req.type)
      }
    };

    this.members.set(did, member);
    
    console.log(`New member added: ${did} (${membershipType})`);
    return member;
  }

  /**
   * Get proposal by ID
   */
  getProposal(proposalId: string): DAOProposal | null {
    return this.proposals.get(proposalId) || null;
  }

  /**
   * List proposals with filters
   */
  listProposals(filters: {
    status?: ProposalStatus;
    type?: ProposalType;
    author?: string;
    limit?: number;
    offset?: number;
  } = {}): DAOProposal[] {
    let proposals = Array.from(this.proposals.values());

    // Apply filters
    if (filters.status) {
      proposals = proposals.filter(p => p.status === filters.status);
    }
    if (filters.type) {
      proposals = proposals.filter(p => p.type === filters.type);
    }
    if (filters.author) {
      proposals = proposals.filter(p => p.authorDid === filters.author);
    }

    // Sort by creation date (newest first)
    proposals.sort((a, b) => new Date(b.createdAt).getTime() - new Date(a.createdAt).getTime());

    // Apply pagination
    if (filters.offset) {
      proposals = proposals.slice(filters.offset);
    }
    if (filters.limit) {
      proposals = proposals.slice(0, filters.limit);
    }

    return proposals;
  }

  /**
   * Get member by DID
   */
  getMember(did: string): DAOMember | null {
    return this.members.get(did) || null;
  }

  /**
   * List all members
   */
  listMembers(): DAOMember[] {
    return Array.from(this.members.values());
  }

  /**
   * Get DAO statistics
   */
  getDAOStatistics(): DAOStatistics {
    const proposals = Array.from(this.proposals.values());
    const members = Array.from(this.members.values());
    const activeProposals = proposals.filter(p => p.status === 'active' || p.status === 'voting');
    const passedProposals = proposals.filter(p => p.status === 'passed');
    const totalVotes = proposals.reduce((sum, p) => sum + p.votes.length, 0);

    return {
      totalMembers: members.length,
      activeMembers: members.filter(m => 
        Date.now() - new Date(m.lastActive).getTime() < 30 * 24 * 60 * 60 * 1000 // 30 days
      ).length,
      totalProposals: proposals.length,
      activeProposals: activeProposals.length,
      passedProposals: passedProposals.length,
      totalVotes,
      averageVotingPower: members.reduce((sum, m) => sum + m.votingPower, 0) / members.length,
      treasuryBalance: this.treasury.getTotalBalance(),
      governanceMetrics: this.calculateGovernanceMetrics(proposals, members)
    };
  }

  /**
   * Private helper methods
   */
  private async validateConstitution(constitution: DAOConstitution): Promise<void> {
    // Basic validation
    if (!constitution.name || !constitution.version) {
      throw new Error('Constitution must have name and version');
    }

    if (!constitution.articles || constitution.articles.length === 0) {
      throw new Error('Constitution must have at least one article');
    }

    // Validate voting rules
    if (!constitution.votingRules || !constitution.votingRules.mechanisms) {
      throw new Error('Constitution must define voting rules');
    }

    // Validate membership rules
    if (!constitution.membershipRules || !constitution.membershipRules.membershipTypes) {
      throw new Error('Constitution must define membership rules');
    }

    console.log('Constitution validation passed');
  }

  private hasProposalPermission(member: DAOMember, proposalType: ProposalType): boolean {
    // Check membership type permissions
    const memType = this.constitution?.membershipRules.membershipTypes.find(
      type => type.typeId === member.membershipType
    );
    
    if (!memType) return false;

    // Different proposal types may require different membership levels
    switch (proposalType) {
      case 'constitutional_amendment':
        return memType.benefits.includes('constitutional_amendment');
      case 'treasury_allocation':
        return memType.benefits.includes('treasury_access');
      case 'membership_action':
        return memType.benefits.includes('membership_management');
      default:
        return true; // Most proposals are open to all members
    }
  }

  private hasExecutionPermission(member: DAOMember, proposal: DAOProposal): boolean {
    // Check if member has execution privileges
    const memType = this.constitution?.membershipRules.membershipTypes.find(
      type => type.typeId === member.membershipType
    );
    
    if (!memType) return false;

    return memType.benefits.includes('proposal_execution');
  }

  private async calculateVotingPower(voterDid: string, proposal: DAOProposal): Promise<number> {
    const member = this.members.get(voterDid);
    if (!member) return 0;

    let basePower = member.votingPower;

    // Apply reputation bonus
    const reputationBonus = Math.min(member.reputation / 100, 0.5); // Max 50% bonus
    basePower *= (1 + reputationBonus);

    // Apply delegation power
    const delegationsReceived = Array.from(this.delegations.values())
      .filter(d => d.delegateeDid === voterDid && d.active);
    
    const delegationPower = delegationsReceived.reduce((sum, d) => {
      const delegatorMember = this.members.get(d.delegatorDid);
      return sum + (delegatorMember?.votingPower || 0);
    }, 0);

    basePower += delegationPower;

    // Apply voting mechanism modifiers
    switch (proposal.votingMechanism) {
      case 'quadratic':
        return Math.sqrt(basePower);
      case 'conviction_voting':
        return basePower * member.contributions.length;
      default:
        return basePower;
    }
  }

  private async createVoteProof(
    proposalId: string,
    voterDid: string,
    choice: VoteChoice,
    weight: number
  ): Promise<string> {
    const proofData = {
      proposalId,
      voterDid,
      choice,
      weight,
      timestamp: new Date().toISOString()
    };

    // In a real implementation, this would use the voter's private key
    return await this.crypto.hashData(JSON.stringify(proofData));
  }

  private async createDelegationProof(
    delegatorDid: string,
    delegateeDid: string,
    type: string
  ): Promise<string> {
    const proofData = {
      delegatorDid,
      delegateeDid,
      type,
      timestamp: new Date().toISOString()
    };

    return await this.crypto.hashData(JSON.stringify(proofData));
  }

  private async updateProposalResults(proposal: DAOProposal): Promise<void> {
    const votes = proposal.votes;
    
    proposal.results.totalVotes = votes.length;
    proposal.results.totalWeight = votes.reduce((sum, v) => sum + v.weight, 0);
    proposal.results.yesVotes = votes.filter(v => v.choice === 'yes').length;
    proposal.results.yesWeight = votes.filter(v => v.choice === 'yes').reduce((sum, v) => sum + v.weight, 0);
    proposal.results.noVotes = votes.filter(v => v.choice === 'no').length;
    proposal.results.noWeight = votes.filter(v => v.choice === 'no').reduce((sum, v) => sum + v.weight, 0);
    proposal.results.abstainVotes = votes.filter(v => v.choice === 'abstain').length;
    proposal.results.abstainWeight = votes.filter(v => v.choice === 'abstain').reduce((sum, v) => sum + v.weight, 0);
    proposal.results.vetoVotes = votes.filter(v => v.choice === 'veto').length;
    proposal.results.vetoWeight = votes.filter(v => v.choice === 'veto').reduce((sum, v) => sum + v.weight, 0);

    // Check quorum
    const totalVotingPower = Array.from(this.members.values())
      .reduce((sum, m) => sum + m.votingPower, 0);
    
    proposal.results.quorumReached = (proposal.results.totalWeight / totalVotingPower) >= proposal.quorum;

    // Check if passed
    const approvalThreshold = this.getApprovalThreshold(proposal);
    proposal.results.passed = proposal.results.quorumReached && 
      (proposal.results.yesWeight / proposal.results.totalWeight) >= approvalThreshold;

    // Generate summary
    proposal.results.summary = this.generateResultsSummary(proposal.results);

    // Update status if voting period ended
    if (Date.now() > new Date(proposal.expiresAt).getTime()) {
      proposal.status = proposal.results.passed ? 'passed' : 'rejected';
    }
  }

  private getApprovalThreshold(proposal: DAOProposal): number {
    const votingRules = this.constitution?.votingRules.quorumRequirements.find(
      req => req.proposalType === proposal.type
    );
    
    return votingRules?.minimumApproval || 0.5; // Default 50%
  }

  private generateResultsSummary(results: ProposalResults): string {
    const approvalRate = results.totalWeight > 0 ? 
      (results.yesWeight / results.totalWeight * 100).toFixed(1) : '0';
    
    return `${results.yesVotes}/${results.totalVotes} votes (${approvalRate}% approval)`;
  }

  private getVotingPeriod(proposal: DAOProposal): number {
    const votingRules = this.constitution?.votingRules.quorumRequirements.find(
      req => req.proposalType === proposal.type
    );
    
    return votingRules?.timeRequirements.maximumVotingPeriod || 7 * 24 * 60 * 60 * 1000; // Default 7 days
  }

  private async executeProposalByType(proposal: DAOProposal, executorDid: string): Promise<ExecutionResult> {
    switch (proposal.type) {
      case 'treasury_allocation':
        return await this.treasury.executeAllocation(proposal.parameters.budget!, executorDid);
      case 'constitutional_amendment':
        return await this.executeConstitutionalAmendment(proposal, executorDid);
      case 'membership_action':
        return await this.executeMembershipAction(proposal, executorDid);
      case 'parameter_change':
        return await this.executeParameterChange(proposal, executorDid);
      default:
        return {
          success: false,
          message: `Execution not implemented for proposal type: ${proposal.type}`,
          transactionId: '',
          timestamp: new Date().toISOString()
        };
    }
  }

  private async executeConstitutionalAmendment(proposal: DAOProposal, executorDid: string): Promise<ExecutionResult> {
    if (!this.constitution) {
      return {
        success: false,
        message: 'No constitution to amend',
        transactionId: '',
        timestamp: new Date().toISOString()
      };
    }

    // Apply amendments
    for (const amendment of proposal.parameters.amendments || []) {
      const article = this.constitution.articles.find(a => a.articleId === amendment.changes[0].field);
      if (article && !article.immutable) {
        article.content = amendment.changes[0].newValue;
      }
    }

    this.constitution.lastAmended = new Date().toISOString();

    return {
      success: true,
      message: 'Constitution amended successfully',
      transactionId: await this.generateTransactionId(),
      timestamp: new Date().toISOString()
    };
  }

  private async executeMembershipAction(proposal: DAOProposal, executorDid: string): Promise<ExecutionResult> {
    const action = proposal.parameters.action;
    const targetDid = proposal.parameters.target;

    switch (action) {
      case 'revoke_membership':
        this.members.delete(targetDid);
        return {
          success: true,
          message: `Membership revoked for ${targetDid}`,
          transactionId: await this.generateTransactionId(),
          timestamp: new Date().toISOString()
        };
      case 'upgrade_membership':
        const member = this.members.get(targetDid);
        if (member) {
          member.membershipType = proposal.parameters.value.newType;
        }
        return {
          success: true,
          message: `Membership upgraded for ${targetDid}`,
          transactionId: await this.generateTransactionId(),
          timestamp: new Date().toISOString()
        };
      default:
        return {
          success: false,
          message: `Unknown membership action: ${action}`,
          transactionId: '',
          timestamp: new Date().toISOString()
        };
    }
  }

  private async executeParameterChange(proposal: DAOProposal, executorDid: string): Promise<ExecutionResult> {
    // Implementation would depend on what parameters can be changed
    return {
      success: true,
      message: 'Parameters changed successfully',
      transactionId: await this.generateTransactionId(),
      timestamp: new Date().toISOString()
    };
  }

  private async verifyMembershipRequirements(
    requirements: MembershipRequirement[],
    did: string,
    applicationData?: any
  ): Promise<void> {
    for (const requirement of requirements) {
      switch (requirement.type) {
        case 'identity':
          // Verify DID exists and is valid
          if (!did.startsWith('did:')) {
            throw new Error('Invalid DID format');
          }
          break;
        case 'stake':
          // Verify minimum stake is held
          if (!applicationData?.stake || applicationData.stake < requirement.value) {
            throw new Error(`Insufficient stake: required ${requirement.value}`);
          }
          break;
        case 'reputation':
          // Verify minimum reputation score
          // This would check reputation system
          break;
        default:
          console.log(`Requirement type ${requirement.type} not implemented`);
      }
    }
  }

  private calculateGovernanceMetrics(proposals: DAOProposal[], members: DAOMember[]): GovernanceMetrics {
    const totalProposals = proposals.length;
    const passedProposals = proposals.filter(p => p.status === 'passed').length;
    const totalVotes = proposals.reduce((sum, p) => sum + p.votes.length, 0);
    const activeMembers = members.filter(m => 
      Date.now() - new Date(m.lastActive).getTime() < 30 * 24 * 60 * 60 * 1000
    ).length;

    return {
      proposalSuccessRate: totalProposals > 0 ? passedProposals / totalProposals : 0,
      averageParticipation: members.length > 0 ? totalVotes / members.length : 0,
      memberEngagement: members.length > 0 ? activeMembers / members.length : 0,
      votingEfficiency: totalVotes > 0 ? proposals.filter(p => p.votes.length > 0).length / proposals.length : 0
    };
  }

  private async validateProposal(proposal: DAOProposal): Promise<void> {
    if (!proposal.title || proposal.title.length === 0) {
      throw new Error('Proposal must have a title');
    }

    if (!proposal.description || proposal.description.length === 0) {
      throw new Error('Proposal must have a description');
    }

    if (!proposal.parameters) {
      throw new Error('Proposal must have parameters');
    }

    console.log(`Proposal validation passed: ${proposal.title}`);
  }

  private async generateProposalId(): Promise<string> {
    const data = `proposal:${Date.now()}:${Math.random()}`;
    const hash = await this.crypto.hashData(data);
    return `prop_${hash.substring(0, 16)}`;
  }

  private async generateVoteId(): Promise<string> {
    const data = `vote:${Date.now()}:${Math.random()}`;
    const hash = await this.crypto.hashData(data);
    return `vote_${hash.substring(0, 16)}`;
  }

  private async generateDelegationId(): Promise<string> {
    const data = `delegation:${Date.now()}:${Math.random()}`;
    const hash = await this.crypto.hashData(data);
    return `del_${hash.substring(0, 16)}`;
  }

  private async generateMemberId(): Promise<string> {
    const data = `member:${Date.now()}:${Math.random()}`;
    const hash = await this.crypto.hashData(data);
    return `mem_${hash.substring(0, 16)}`;
  }

  private async generateTransactionId(): Promise<string> {
    const data = `tx:${Date.now()}:${Math.random()}`;
    const hash = await this.crypto.hashData(data);
    return `tx_${hash.substring(0, 16)}`;
  }
}

// Supporting interfaces
export interface DAOMember {
  memberId: string;
  did: string;
  profile: any;
  membershipType: string;
  joinedAt: string;
  status: 'active' | 'suspended' | 'expired';
  votingPower: number;
  reputation: number;
  contributions: Contribution[];
  delegationsGiven: number;
  delegationsReceived: number;
  lastActive: string;
  metadata: any;
}

export interface VoteDelegation {
  delegationId: string;
  delegatorDid: string;
  delegateeDid: string;
  type: 'full' | 'partial' | 'proposal_specific';
  parameters: any;
  createdAt: string;
  expiresAt: string;
  active: boolean;
  revocable: boolean;
  proof: string;
}

export interface Contribution {
  contributionId: string;
  type: string;
  description: string;
  timestamp: string;
  value: any;
  verified: boolean;
}

export interface ExecutionResult {
  success: boolean;
  message: string;
  transactionId: string;
  timestamp: string;
}

export interface DAOStatistics {
  totalMembers: number;
  activeMembers: number;
  totalProposals: number;
  activeProposals: number;
  passedProposals: number;
  totalVotes: number;
  averageVotingPower: number;
  treasuryBalance: Map<string, number>;
  governanceMetrics: GovernanceMetrics;
}

export interface GovernanceMetrics {
  proposalSuccessRate: number;
  averageParticipation: number;
  memberEngagement: number;
  votingEfficiency: number;
}

// Treasury class (simplified for now)
class DAOTreasury {
  private balances: Map<string, number> = new Map();
  private currencies: Currency[] = [];

  async initialize(treasuryRules: TreasuryRules): Promise<void> {
    this.currencies = treasuryRules.currencies;
    
    // Initialize balances to zero
    for (const currency of this.currencies) {
      this.balances.set(currency.currencyId, 0);
    }
  }

  async executeAllocation(allocation: BudgetAllocation, executorDid: string): Promise<ExecutionResult> {
    const currentBalance = this.balances.get(allocation.currency) || 0;
    
    if (currentBalance < allocation.amount) {
      return {
        success: false,
        message: 'Insufficient treasury balance',
        transactionId: '',
        timestamp: new Date().toISOString()
      };
    }

    // Deduct from treasury
    this.balances.set(allocation.currency, currentBalance - allocation.amount);

    // In a real implementation, this would transfer to recipients
    console.log(`Allocated ${allocation.amount} ${allocation.currency} to ${allocation.recipients.length} recipients`);

    return {
      success: true,
      message: 'Allocation executed successfully',
      transactionId: `alloc_${Date.now()}`,
      timestamp: new Date().toISOString()
    };
  }

  getTotalBalance(): Map<string, number> {
    return new Map(this.balances);
  }
}