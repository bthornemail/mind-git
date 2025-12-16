/**
 * Token Economics and Reputation System
 * 
 * Implements comprehensive token economics with multiple token types,
 * reputation scoring, staking mechanisms, and economic incentives.
 */

import { PolyF2 } from '../core/polynomial/index';
import { AALType } from '../core/aal/types';
import { DIDDocument } from '../identity/did-core';
import { CubicSignature } from '../core/cryptography/cubic-signature';
import { ProductionCryptography } from '@cryptography/production-crypto';

export interface Token {
  tokenId: string;
  name: string;
  symbol: string;
  type: TokenType;
  decimals: number;
  totalSupply: number;
  circulatingSupply: number;
  mintingAuthority: string;
  burningEnabled: boolean;
  metadata: TokenMetadata;
  economics: TokenEconomics;
}

export type TokenType = 
  | 'governance'
  | 'utility'
  | 'reputation'
  | 'staking'
  | 'reward'
  | 'stablecoin'
  | 'wrapped'
  | 'multiverse';

export interface TokenMetadata {
  description: string;
  icon?: string;
  website?: string;
  whitepaper?: string;
  auditReports?: AuditReport[];
  legalStatus: string;
  jurisdiction: string;
  compliance: ComplianceInfo;
}

export interface AuditReport {
  auditor: string;
  date: string;
  score: number;
  findings: string[];
  recommendations: string[];
}

export interface ComplianceInfo {
  kycRequired: boolean;
  amlRequired: boolean;
  restrictedJurisdictions: string[];
  accreditedInvestorOnly: boolean;
  taxClassification: string;
}

export interface TokenEconomics {
  distribution: TokenDistribution;
  inflation: InflationModel;
  staking: StakingModel;
  governance: GovernanceRights;
  utility: UtilityFunction;
  bonding: BondingCurve;
}

export interface TokenDistribution {
  total: number;
  allocations: Allocation[];
  vestingSchedules: VestingSchedule[];
  lockupPeriods: LockupPeriod[];
}

export interface Allocation {
  recipient: string;
  percentage: number;
  amount: number;
  type: 'team' | 'investors' | 'community' | 'treasury' | 'ecosystem' | 'airdrop';
  vesting?: VestingSchedule;
  lockup?: LockupPeriod;
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
}

export interface LockupPeriod {
  lockupId: string;
  amount: number;
  duration: number;
  startDate: string;
  endDate: string;
  releaseConditions: string[];
  earlyReleasePenalty: number;
}

export interface InflationModel {
  enabled: boolean;
  type: 'fixed' | 'dynamic' | 'supply_elastic' | 'algorithmic';
  rate: number;
  adjustmentPeriod: number;
  maxSupply?: number;
  targetMetrics?: string[];
  halvingSchedule?: HalvingEvent[];
}

export interface HalvingEvent {
  blockNumber?: number;
  timestamp?: string;
  newRate: number;
  description: string;
}

export interface StakingModel {
  enabled: boolean;
  minimumStake: number;
  maximumStake: number;
  stakingPeriods: StakingPeriod[];
  rewards: RewardModel;
  penalties: PenaltyModel;
  unbondingPeriod: number;
}

export interface StakingPeriod {
  periodId: string;
  duration: number;
  rewardMultiplier: number;
  minimumLockup: number;
  description: string;
}

export interface RewardModel {
  type: 'fixed' | 'proportional' | 'tiered' | 'dynamic';
  baseRate: number;
  bonusMultipliers: BonusMultiplier[];
  compounding: boolean;
  distributionFrequency: number;
}

export interface BonusMultiplier {
  condition: string;
  multiplier: number;
  description: string;
}

export interface PenaltyModel {
  earlyUnbondingPenalty: number;
  slashConditions: SlashCondition[];
  penaltyCalculation: 'linear' | 'exponential' | 'fixed';
}

export interface SlashCondition {
  condition: string;
  penaltyPercentage: number;
  description: string;
}

export interface GovernanceRights {
  votingPower: boolean;
  proposalCreation: boolean;
  delegation: boolean;
  vetoPower: boolean;
  votingWeight: 'linear' | 'quadratic' | 'logarithmic';
  minimumHoldTime: number;
}

export interface UtilityFunction {
  primaryUse: string;
  secondaryUses: string[];
  networkEffects: NetworkEffect[];
  burnMechanisms: BurnMechanism[];
  feeDiscounts: FeeDiscount[];
}

export interface NetworkEffect {
  effect: string;
  description: string;
  impact: 'positive' | 'negative' | 'neutral';
  magnitude: number;
}

export interface BurnMechanism {
  type: string;
  rate: number;
  conditions: string[];
  description: string;
}

export interface FeeDiscount {
  service: string;
  discountPercentage: number;
  minimumHold: number;
  description: string;
}

export interface BondingCurve {
  type: 'linear' | 'exponential' | 'logarithmic' | 'sigmoid';
  formula: string;
  parameters: CurveParameters;
  buyFee: number;
  sellFee: number;
}

export interface CurveParameters {
  slope?: number;
  intercept?: number;
  maxPrice?: number;
  minPrice?: number;
  saturation?: number;
}

export interface ReputationSystem {
  systemId: string;
  name: string;
  version: string;
  scoring: ReputationScoring;
  categories: ReputationCategory[];
  decay: ReputationDecay;
  rewards: ReputationRewards;
  penalties: ReputationPenalties;
}

export interface ReputationScoring {
  algorithm: 'weighted_average' | 'exponential_moving' | 'bayesian' | 'machine_learning';
  baseScore: number;
  maxScore: number;
  minScore: number;
  factors: ReputationFactor[];
  normalization: NormalizationMethod;
}

export interface ReputationFactor {
  factorId: string;
  name: string;
  weight: number;
  type: 'positive' | 'negative' | 'neutral';
  calculation: string;
  decayRate: number;
  caps: ScoreCap;
}

export interface ScoreCap {
  dailyCap?: number;
  weeklyCap?: number;
  monthlyCap?: number;
  totalCap?: number;
}

export interface NormalizationMethod {
  type: 'z_score' | 'min_max' | 'percentile' | 'sigmoid';
  parameters: any;
}

export interface ReputationCategory {
  categoryId: string;
  name: string;
  description: string;
  factors: string[];
  weights: Map<string, number>;
  thresholds: ReputationThreshold[];
}

export interface ReputationThreshold {
  level: string;
  minScore: number;
  maxScore: number;
  benefits: string[];
  requirements: string[];
}

export interface ReputationDecay {
  enabled: boolean;
  type: 'linear' | 'exponential' | 'step_function';
  rate: number;
  period: number;
  inactivityPenalty: number;
  recoveryRate: number;
}

export interface ReputationRewards {
  positiveActions: ReputationAction[];
  milestoneBonuses: MilestoneBonus[];
  streakBonuses: StreakBonus[];
  referralBonuses: ReferralBonus[];
}

export interface ReputationAction {
  actionId: string;
  name: string;
  description: string;
  baseReward: number;
  multipliers: RewardMultiplier[];
  cooldown: number;
  maxDaily: number;
}

export interface RewardMultiplier {
  condition: string;
  multiplier: number;
  description: string;
}

export interface MilestoneBonus {
  milestoneId: string;
  scoreThreshold: number;
  bonusAmount: number;
  description: string;
  oneTime: boolean;
}

export interface StreakBonus {
  streakId: string;
  consecutiveDays: number;
  bonusMultiplier: number;
  description: string;
  maxMultiplier: number;
}

export interface ReferralBonus {
  referralId: string;
  referrerBonus: number;
  refereeBonus: number;
  conditions: string[];
  vestingPeriod: number;
}

export interface ReputationPenalties {
  negativeActions: ReputationAction[];
  slashConditions: SlashCondition[];
  appealProcess: AppealProcess;
}

export interface AppealProcess {
  enabled: boolean;
  timeframe: number;
  requiredStake: number;
  votingMechanism: string;
  successRefund: number;
}

export interface TokenBalance {
  accountId: string;
  tokenId: string;
  balance: number;
  lockedBalance: number;
  stakedBalance: number;
  vestingBalance: number;
  lastUpdated: string;
  metadata: BalanceMetadata;
}

export interface BalanceMetadata {
  source: string[];
  history: BalanceHistory[];
  rewards: RewardHistory[];
  penalties: PenaltyHistory[];
}

export interface BalanceHistory {
  transactionId: string;
  type: 'mint' | 'burn' | 'transfer' | 'stake' | 'unstake' | 'lock' | 'unlock';
  amount: number;
  balance: number;
  timestamp: string;
  reason: string;
}

export interface RewardHistory {
  rewardId: string;
  type: string;
  amount: number;
  reason: string;
  timestamp: string;
}

export interface PenaltyHistory {
  penaltyId: string;
  type: string;
  amount: number;
  reason: string;
  timestamp: string;
  appealed: boolean;
  successful: boolean;
}

export interface StakingPosition {
  positionId: string;
  accountId: string;
  tokenId: string;
  amount: number;
  stakingPeriodId: string;
  startTime: string;
  endTime?: string;
  unbondingTime?: string;
  rewards: StakingReward[];
  status: 'active' | 'unbonding' | 'completed' | 'slashed';
  metadata: StakingMetadata;
}

export interface StakingReward {
  rewardId: string;
  tokenId: string;
  amount: number;
  calculatedAt: string;
  claimed: boolean;
  claimedAt?: string;
}

export interface StakingMetadata {
  autoRestake: boolean;
  rewardDestination: string;
  compoundFrequency: number;
  riskLevel: 'low' | 'medium' | 'high';
}

export interface LiquidityPool {
  poolId: string;
  tokenA: string;
  tokenB: string;
  reserveA: number;
  reserveB: number;
  totalLiquidity: number;
  lpTokens: number;
  feeRate: number;
  apr: number;
  volume24h: number;
  fees24h: number;
  metadata: PoolMetadata;
}

export interface PoolMetadata {
  created: string;
  lastUpdated: string;
  creator: string;
  description: string;
  tags: string[];
  riskLevel: 'low' | 'medium' | 'high';
}

/**
 * Token Economics Manager
 */
export class TokenEconomicsManager {
  private crypto: ProductionCrypto;
  private cubicSignature: CubicSignature;
  private tokens: Map<string, Token> = new Map();
  private balances: Map<string, TokenBalance[]> = new Map();
  private reputationSystems: Map<string, ReputationSystem> = new Map();
  private stakingPositions: Map<string, StakingPosition> = new Map();
  private liquidityPools: Map<string, LiquidityPool> = new Map();

  constructor() {
    this.crypto = new ProductionCrypto();
    this.cubicSignature = new CubicSignature();
  }

  /**
   * Create new token
   */
  async createToken(
    name: string,
    symbol: string,
    type: TokenType,
    totalSupply: number,
    mintingAuthority: string,
    economics: TokenEconomics,
    metadata: Partial<TokenMetadata> = {}
  ): Promise<Token> {
    const tokenId = await this.generateTokenId();
    const timestamp = new Date().toISOString();

    const token: Token = {
      tokenId,
      name,
      symbol,
      type,
      decimals: 18, // Default 18 decimals
      totalSupply,
      circulatingSupply: 0,
      mintingAuthority,
      burningEnabled: true,
      metadata: {
        description: `${name} (${symbol}) token`,
        legalStatus: 'unregulated',
        jurisdiction: 'global',
        compliance: {
          kycRequired: false,
          amlRequired: false,
          restrictedJurisdictions: [],
          accreditedInvestorOnly: false,
          taxClassification: 'utility'
        },
        ...metadata
      },
      economics
    };

    this.tokens.set(tokenId, token);
    
    console.log(`Token created: ${symbol} (${tokenId})`);
    return token;
  }

  /**
   * Mint tokens to account
   */
  async mintTokens(
    tokenId: string,
    accountId: string,
    amount: number,
    reason: string
  ): Promise<string> {
    const token = this.tokens.get(tokenId);
    if (!token) {
      throw new Error(`Token not found: ${tokenId}`);
    }

    if (token.circulatingSupply + amount > token.totalSupply) {
      throw new Error('Minting would exceed total supply');
    }

    // Update token supply
    token.circulatingSupply += amount;

    // Update account balance
    const balance = this.getOrCreateBalance(accountId, tokenId);
    balance.balance += amount;
    balance.lastUpdated = new Date().toISOString();

    // Add to history
    const transactionId = await this.generateTransactionId();
    balance.metadata.history.push({
      transactionId,
      type: 'mint',
      amount,
      balance: balance.balance,
      timestamp: new Date().toISOString(),
      reason
    });

    return transactionId;
  }

  /**
   * Burn tokens from account
   */
  async burnTokens(
    tokenId: string,
    accountId: string,
    amount: number,
    reason: string
  ): Promise<string> {
    const token = this.tokens.get(tokenId);
    if (!token) {
      throw new Error(`Token not found: ${tokenId}`);
    }

    if (!token.burningEnabled) {
      throw new Error('Burning is not enabled for this token');
    }

    const balance = this.getBalance(accountId, tokenId);
    if (!balance || balance.balance < amount) {
      throw new Error('Insufficient balance to burn');
    }

    // Update token supply
    token.circulatingSupply -= amount;

    // Update account balance
    balance.balance -= amount;
    balance.lastUpdated = new Date().toISOString();

    // Add to history
    const transactionId = await this.generateTransactionId();
    balance.metadata.history.push({
      transactionId,
      type: 'burn',
      amount,
      balance: balance.balance,
      timestamp: new Date().toISOString(),
      reason
    });

    return transactionId;
  }

  /**
   * Transfer tokens between accounts
   */
  async transferTokens(
    tokenId: string,
    fromAccountId: string,
    toAccountId: string,
    amount: number,
    reason: string
  ): Promise<string> {
    const fromBalance = this.getBalance(fromAccountId, tokenId);
    if (!fromBalance || fromBalance.balance < amount) {
      throw new Error('Insufficient balance for transfer');
    }

    const toBalance = this.getOrCreateBalance(toAccountId, tokenId);
    const transactionId = await this.generateTransactionId();
    const timestamp = new Date().toISOString();

    // Update from balance
    fromBalance.balance -= amount;
    fromBalance.lastUpdated = timestamp;
    fromBalance.metadata.history.push({
      transactionId,
      type: 'transfer',
      amount: -amount,
      balance: fromBalance.balance,
      timestamp,
      reason: `Transfer to ${toAccountId}: ${reason}`
    });

    // Update to balance
    toBalance.balance += amount;
    toBalance.lastUpdated = timestamp;
    toBalance.metadata.history.push({
      transactionId,
      type: 'transfer',
      amount,
      balance: toBalance.balance,
      timestamp,
      reason: `Transfer from ${fromAccountId}: ${reason}`
    });

    return transactionId;
  }

  /**
   * Stake tokens
   */
  async stakeTokens(
    accountId: string,
    tokenId: string,
    amount: number,
    stakingPeriodId: string,
    metadata: Partial<StakingMetadata> = {}
  ): Promise<StakingPosition> {
    const token = this.tokens.get(tokenId);
    if (!token) {
      throw new Error(`Token not found: ${tokenId}`);
    }

    if (!token.economics.staking.enabled) {
      throw new Error('Staking is not enabled for this token');
    }

    const balance = this.getBalance(accountId, tokenId);
    if (!balance || balance.balance < amount) {
      throw new Error('Insufficient balance for staking');
    }

    const positionId = await this.generatePositionId();
    const stakingPeriod = token.economics.staking.stakingPeriods.find(
      period => period.periodId === stakingPeriodId
    );

    if (!stakingPeriod) {
      throw new Error(`Staking period not found: ${stakingPeriodId}`);
    }

    // Create staking position
    const position: StakingPosition = {
      positionId,
      accountId,
      tokenId,
      amount,
      stakingPeriodId,
      startTime: new Date().toISOString(),
      rewards: [],
      status: 'active',
      metadata: {
        autoRestake: false,
        rewardDestination: accountId,
        compoundFrequency: 24 * 60 * 60 * 1000, // Daily
        riskLevel: 'low',
        ...metadata
      }
    };

    // Lock tokens
    balance.balance -= amount;
    balance.stakedBalance += amount;
    balance.lastUpdated = new Date().toISOString();

    this.stakingPositions.set(positionId, position);

    console.log(`Staked ${amount} ${token.symbol} for position ${positionId}`);
    return position;
  }

  /**
   * Unstake tokens
   */
  async unstakeTokens(
    positionId: string,
    accountId: string
  ): Promise<string> {
    const position = this.stakingPositions.get(positionId);
    if (!position) {
      throw new Error(`Staking position not found: ${positionId}`);
    }

    if (position.accountId !== accountId) {
      throw new Error('Not authorized to unstake this position');
    }

    if (position.status !== 'active') {
      throw new Error('Position is not active');
    }

    const token = this.tokens.get(position.tokenId);
    if (!token) {
      throw new Error(`Token not found: ${position.tokenId}`);
    }

    // Calculate rewards
    const rewards = await this.calculateStakingRewards(position);
    position.rewards = rewards;

    // Start unbonding period
    position.status = 'unbonding';
    position.unbondingTime = new Date().toISOString();

    const transactionId = await this.generateTransactionId();
    
    console.log(`Unstaking started for position ${positionId}`);
    return transactionId;
  }

  /**
   * Create reputation system
   */
  async createReputationSystem(
    name: string,
    scoring: ReputationScoring,
    categories: ReputationCategory[],
    decay: ReputationDecay,
    rewards: ReputationRewards,
    penalties: ReputationPenalties
  ): Promise<ReputationSystem> {
    const systemId = await this.generateSystemId();
    const timestamp = new Date().toISOString();

    const system: ReputationSystem = {
      systemId,
      name,
      version: '1.0',
      scoring,
      categories,
      decay,
      rewards,
      penalties
    };

    this.reputationSystems.set(systemId, system);
    
    console.log(`Reputation system created: ${name} (${systemId})`);
    return system;
  }

  /**
   * Update reputation score
   */
  async updateReputation(
    systemId: string,
    accountId: string,
    action: string,
    value: number,
    metadata: any = {}
  ): Promise<number> {
    const system = this.reputationSystems.get(systemId);
    if (!system) {
      throw new Error(`Reputation system not found: ${systemId}`);
    }

    // Get current reputation (simplified - in production would use proper storage)
    const currentScore = await this.getCurrentReputation(systemId, accountId);
    
    // Apply scoring algorithm
    const newScore = await this.calculateReputationScore(
      system.scoring,
      currentScore,
      action,
      value,
      metadata
    );

    // Store updated reputation
    await this.storeReputation(systemId, accountId, newScore, action, metadata);

    return newScore;
  }

  /**
   * Get token balance
   */
  getBalance(accountId: string, tokenId: string): TokenBalance | null {
    const balances = this.balances.get(accountId);
    if (!balances) return null;
    
    return balances.find(b => b.tokenId === tokenId) || null;
  }

  /**
   * Get all balances for account
   */
  getAccountBalances(accountId: string): TokenBalance[] {
    return this.balances.get(accountId) || [];
  }

  /**
   * Get staking position
   */
  getStakingPosition(positionId: string): StakingPosition | null {
    return this.stakingPositions.get(positionId) || null;
  }

  /**
   * Get all staking positions for account
   */
  getStakingPositions(accountId: string): StakingPosition[] {
    return Array.from(this.stakingPositions.values())
      .filter(position => position.accountId === accountId);
  }

  /**
   * Get token information
   */
  getToken(tokenId: string): Token | null {
    return this.tokens.get(tokenId) || null;
  }

  /**
   * List all tokens
   */
  listTokens(filters: {
    type?: TokenType;
    mintingAuthority?: string;
    limit?: number;
    offset?: number;
  } = {}): Token[] {
    let tokens = Array.from(this.tokens.values());

    // Apply filters
    if (filters.type) {
      tokens = tokens.filter(t => t.type === filters.type);
    }
    if (filters.mintingAuthority) {
      tokens = tokens.filter(t => t.mintingAuthority === filters.mintingAuthority);
    }

    // Sort by creation date (newest first)
    tokens.sort((a, b) => b.tokenId.localeCompare(a.tokenId));

    // Apply pagination
    if (filters.offset) {
      tokens = tokens.slice(filters.offset);
    }
    if (filters.limit) {
      tokens = tokens.slice(0, filters.limit);
    }

    return tokens;
  }

  /**
   * Get economic statistics
   */
  getEconomicStatistics(): EconomicStatistics {
    const tokens = Array.from(this.tokens.values());
    const balances = Array.from(this.balances.values()).flat();
    const positions = Array.from(this.stakingPositions.values());

    const totalMarketCap = tokens.reduce((sum, token) => {
      const totalBalance = balances
        .filter(b => b.tokenId === token.tokenId)
        .reduce((balanceSum, b) => balanceSum + b.balance, 0);
      return sum + (totalBalance * 1); // Simplified - would use actual price
    }, 0);

    const totalStaked = positions.reduce((sum, position) => sum + position.amount, 0);
    const totalLocked = balances.reduce((sum, balance) => 
      sum + balance.lockedBalance + balance.stakedBalance + balance.vestingBalance, 0
    );

    return {
      totalTokens: tokens.length,
      totalMarketCap,
      totalCirculatingSupply: tokens.reduce((sum, t) => sum + t.circulatingSupply, 0),
      totalStaked,
      totalLocked,
      averageAPR: this.calculateAverageAPR(positions),
      tokenDistribution: this.calculateTokenDistribution(balances),
      stakingDistribution: this.calculateStakingDistribution(positions),
      reputationMetrics: this.calculateReputationMetrics()
    };
  }

  /**
   * Private helper methods
   */
  private getOrCreateBalance(accountId: string, tokenId: string): TokenBalance {
    const balances = this.balances.get(accountId) || [];
    let balance = balances.find(b => b.tokenId === tokenId);
    
    if (!balance) {
      balance = {
        accountId,
        tokenId,
        balance: 0,
        lockedBalance: 0,
        stakedBalance: 0,
        vestingBalance: 0,
        lastUpdated: new Date().toISOString(),
        metadata: {
          source: [],
          history: [],
          rewards: [],
          penalties: []
        }
      };
      balances.push(balance);
      this.balances.set(accountId, balances);
    }
    
    return balance;
  }

  private async calculateStakingRewards(position: StakingPosition): Promise<StakingReward[]> {
    const token = this.tokens.get(position.tokenId);
    if (!token) return [];

    const stakingPeriod = token.economics.staking.stakingPeriods.find(
      period => period.periodId === position.stakingPeriodId
    );
    
    if (!stakingPeriod) return [];

    const now = Date.now();
    const startTime = new Date(position.startTime).getTime();
    const stakingDuration = now - startTime;
    const rewardModel = token.economics.staking.rewards;

    // Simplified reward calculation
    const baseReward = position.amount * rewardModel.baseRate * (stakingDuration / (365 * 24 * 60 * 60 * 1000));
    const multiplier = stakingPeriod.rewardMultiplier;
    const totalReward = baseReward * multiplier;

    return [{
      rewardId: await this.generateRewardId(),
      tokenId: position.tokenId,
      amount: totalReward,
      calculatedAt: new Date().toISOString(),
      claimed: false
    }];
  }

  private async calculateReputationScore(
    scoring: ReputationScoring,
    currentScore: number,
    action: string,
    value: number,
    metadata: any
  ): Promise<number> {
    // Find the factor for this action
    const factor = scoring.factors.find(f => f.calculation.includes(action));
    if (!factor) return currentScore;

    // Apply factor weight and decay
    let adjustedValue = value * factor.weight;
    
    // Apply decay if enabled
    if (scoring.algorithm === 'exponential_moving') {
      adjustedValue = currentScore * 0.9 + adjustedValue * 0.1;
    } else {
      adjustedValue = currentScore + adjustedValue;
    }

    // Apply caps
    if (factor.caps.totalCap) {
      adjustedValue = Math.min(adjustedValue, factor.caps.totalCap);
    }

    // Apply min/max bounds
    return Math.max(scoring.minScore, Math.min(scoring.maxScore, adjustedValue));
  }

  private async getCurrentReputation(systemId: string, accountId: string): Promise<number> {
    // In a real implementation, this would query storage
    return 50; // Default neutral score
  }

  private async storeReputation(
    systemId: string,
    accountId: string,
    score: number,
    action: string,
    metadata: any
  ): Promise<void> {
    // In a real implementation, this would store to database
    console.log(`Reputation updated for ${accountId}: ${score} (${action})`);
  }

  private calculateAverageAPR(positions: StakingPosition[]): number {
    if (positions.length === 0) return 0;
    
    const totalAPR = positions.reduce((sum, position) => {
      // Simplified APR calculation
      return sum + 5; // Would calculate actual APR based on rewards
    }, 0);
    
    return totalAPR / positions.length;
  }

  private calculateTokenDistribution(balances: TokenBalance[]): Map<string, number> {
    const distribution = new Map<string, number>();
    
    balances.forEach(balance => {
      const current = distribution.get(balance.tokenId) || 0;
      distribution.set(balance.tokenId, current + balance.balance);
    });
    
    return distribution;
  }

  private calculateStakingDistribution(positions: StakingPosition[]): Map<string, number> {
    const distribution = new Map<string, number>();
    
    positions.forEach(position => {
      const current = distribution.get(position.tokenId) || 0;
      distribution.set(position.tokenId, current + position.amount);
    });
    
    return distribution;
  }

  private calculateReputationMetrics(): ReputationMetrics {
    const systems = Array.from(this.reputationSystems.values());
    
    return {
      totalSystems: systems.length,
      averageScore: 75, // Simplified
      totalUsers: 1000, // Simplified
      activeUsers: 800, // Simplified
      scoreDistribution: new Map([
        ['low', 100],
        ['medium', 500],
        ['high', 300],
        ['excellent', 100]
      ])
    };
  }

  private async generateTokenId(): Promise<string> {
    const data = `token:${Date.now()}:${Math.random()}`;
    const hash = await this.crypto.hashData(data);
    return `token_${hash.substring(0, 16)}`;
  }

  private async generateTransactionId(): Promise<string> {
    const data = `tx:${Date.now()}:${Math.random()}`;
    const hash = await this.crypto.hashData(data);
    return `tx_${hash.substring(0, 16)}`;
  }

  private async generatePositionId(): Promise<string> {
    const data = `pos:${Date.now()}:${Math.random()}`;
    const hash = await this.crypto.hashData(data);
    return `pos_${hash.substring(0, 16)}`;
  }

  private async generateSystemId(): Promise<string> {
    const data = `sys:${Date.now()}:${Math.random()}`;
    const hash = await this.crypto.hashData(data);
    return `sys_${hash.substring(0, 16)}`;
  }

  private async generateRewardId(): Promise<string> {
    const data = `reward:${Date.now()}:${Math.random()}`;
    const hash = await this.crypto.hashData(data);
    return `reward_${hash.substring(0, 16)}`;
  }
}

// Supporting interfaces
export interface EconomicStatistics {
  totalTokens: number;
  totalMarketCap: number;
  totalCirculatingSupply: number;
  totalStaked: number;
  totalLocked: number;
  averageAPR: number;
  tokenDistribution: Map<string, number>;
  stakingDistribution: Map<string, number>;
  reputationMetrics: ReputationMetrics;
}

export interface ReputationMetrics {
  totalSystems: number;
  averageScore: number;
  totalUsers: number;
  activeUsers: number;
  scoreDistribution: Map<string, number>;
}