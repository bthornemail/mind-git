/**
 * Identity Integration with MindGit Operations
 * 
 * Integrates sovereign identity management, DID resolution, and multiverse
 * addressing with MindGit's version control and computational organism evolution.
 */

import { Polynomial } from '../core/polynomial/polynomial';
import { AALType } from '../core/aal/types';
import { MindGitMain } from '../mindgit/mindgit-main';
import { SovereignIdentityManager } from './sovereign-identity';
import { MultiverseAddressManager } from './multiverse-addressing';
import { IdentityVerifier, CredentialManager, AttestationManager } from './identity-verification';
import { DIDDocument } from './did-core';
import { ProductionCrypto } from '../production/production-crypto';

export interface IdentityGitConfig {
  defaultNamespace: string;
  requireIdentityForCommits: boolean;
  requireVerificationForMerges: boolean;
  enableMultiverseSync: boolean;
  trustThreshold: number;
  verificationLevel: 'basic' | 'standard' | 'enhanced' | 'maximum';
}

export interface IdentityCommit {
  commitHash: string;
  authorDid: string;
  committerDid: string;
  authorAddress?: string;
  committerAddress?: string;
  identityProof: string;
  verificationStatus: 'verified' | 'pending' | 'rejected' | 'expired';
  credentials: string[];
  attestations: string[];
  metadata: IdentityCommitMetadata;
}

export interface IdentityCommitMetadata {
  trustLevel: string;
  riskScore: number;
  verificationLevel: string;
  jurisdiction: string;
  complianceFrameworks: string[];
  multiverseCoordinates?: {
    universeId: string;
    realmId: string;
    coordinate: { x: number; y: number; z: number; dimension: number };
  };
}

export interface IdentityBranch {
  branchName: string;
  ownerDid: string;
  accessControl: AccessControlEntry[];
  requiredCredentials: string[];
  mergePolicy: MergePolicy;
  created: string;
  lastModified: string;
}

export interface AccessControlEntry {
  entityDid: string;
  permissions: ('read' | 'write' | 'merge' | 'admin')[];
  grantedBy: string;
  grantedAt: string;
  expires?: string;
}

export interface MergePolicy {
  requireVerification: boolean;
  minTrustLevel: string;
  requiredAttestors: string[];
  votingRequired: boolean;
  votingPeriod: number;
  quorum: number;
}

export interface IdentityRepository {
  repositoryId: string;
  ownerDid: string;
  name: string;
  description: string;
  defaultBranch: string;
  branches: Map<string, IdentityBranch>;
  contributors: Map<string, ContributorRole>;
  governance: RepositoryGovernance;
  metadata: RepositoryMetadata;
}

export interface ContributorRole {
  did: string;
  role: 'owner' | 'maintainer' | 'contributor' | 'viewer';
  permissions: string[];
  joinedAt: string;
  lastActivity: string;
}

export interface RepositoryGovernance {
  type: 'benevolent_dictator' | 'democracy' | 'meritocracy' | 'technocracy' | 'dao';
  rules: GovernanceRule[];
  votingMechanism?: VotingMechanism;
  treasury?: TreasuryConfig;
}

export interface GovernanceRule {
  ruleId: string;
  description: string;
  type: 'access_control' | 'merge_policy' | 'code_quality' | 'identity_verification';
  enforcement: 'automatic' | 'manual' | 'consensus';
  parameters: Record<string, any>;
}

export interface VotingMechanism {
  type: 'simple' | 'weighted' | 'quadratic' | 'reputation_based';
  quorum: number;
  votingPeriod: number;
  executionDelay: number;
}

export interface TreasuryConfig {
  currency: string;
  fundingMechanism: 'donations' | 'subscription' | 'token_based' | 'bounty_based';
  distributionRules: DistributionRule[];
}

export interface DistributionRule {
  condition: string;
  recipients: string[];
  percentage: number;
  description: string;
}

export interface RepositoryMetadata {
  topics: string[];
  languages: string[];
  license: string;
  visibility: 'public' | 'private' | 'restricted';
  multiverse: {
    primaryUniverse: string;
    supportedUniverses: string[];
    syncEnabled: boolean;
  };
}

/**
 * Identity-Integrated MindGit
 */
export class IdentityMindGit {
  private mindgit: MindGitMain;
  private identityManager: SovereignIdentityManager;
  private addressManager: MultiverseAddressManager;
  private identityVerifier: IdentityVerifier;
  private credentialManager: CredentialManager;
  private attestationManager: AttestationManager;
  private crypto: ProductionCrypto;
  private config: IdentityGitConfig;
  private repositories: Map<string, IdentityRepository> = new Map();
  private identityCommits: Map<string, IdentityCommit> = new Map();

  constructor(config: Partial<IdentityGitConfig> = {}) {
    this.mindgit = new MindGitMain();
    this.identityManager = new SovereignIdentityManager();
    this.addressManager = new MultiverseAddressManager();
    this.identityVerifier = new IdentityVerifier();
    this.credentialManager = new CredentialManager();
    this.attestationManager = new AttestationManager();
    this.crypto = new ProductionCrypto();
    
    this.config = {
      defaultNamespace: 'mindgit',
      requireIdentityForCommits: true,
      requireVerificationForMerges: true,
      enableMultiverseSync: true,
      trustThreshold: 0.7,
      verificationLevel: 'standard',
      ...config
    };
  }

  /**
   * Initialize repository with identity integration
   */
  async initializeIdentityRepository(
    repositoryName: string,
    ownerDid: string,
    options: {
      description?: string;
      defaultBranch?: string;
      governance?: Partial<RepositoryGovernance>;
      metadata?: Partial<RepositoryMetadata>;
    } = {}
  ): Promise<IdentityRepository> {
    // Verify owner identity exists
    const ownerProfile = this.identityManager.getIdentityProfile(ownerDid);
    if (!ownerProfile) {
      throw new Error(`Owner identity not found: ${ownerDid}`);
    }

    // Initialize MindGit repository
    await this.mindgit.initializeRepository(repositoryName);

    const repositoryId = await this.generateRepositoryId(repositoryName, ownerDid);
    const defaultBranch = options.defaultBranch || 'main';

    // Create identity repository
    const repository: IdentityRepository = {
      repositoryId,
      ownerDid,
      name: repositoryName,
      description: options.description || '',
      defaultBranch,
      branches: new Map(),
      contributors: new Map(),
      governance: {
        type: 'meritocracy',
        rules: [],
        votingMechanism: {
          type: 'reputation_based',
          quorum: 0.5,
          votingPeriod: 7 * 24 * 60 * 60 * 1000, // 7 days
          executionDelay: 24 * 60 * 60 * 1000 // 24 hours
        },
        ...options.governance
      },
      metadata: {
        topics: [],
        languages: [],
        license: 'MIT',
        visibility: 'public',
        multiverse: {
          primaryUniverse: 'Prime Reality',
          supportedUniverses: ['Prime Reality', 'Complex Plane'],
          syncEnabled: this.config.enableMultiverseSync
        },
        ...options.metadata
      }
    };

    // Create default branch
    const defaultIdentityBranch: IdentityBranch = {
      branchName: defaultBranch,
      ownerDid,
      accessControl: [{
        entityDid: ownerDid,
        permissions: ['read', 'write', 'merge', 'admin'],
        grantedBy: ownerDid,
        grantedAt: new Date().toISOString()
      }],
      requiredCredentials: [],
      mergePolicy: {
        requireVerification: this.config.requireVerificationForMerges,
        minTrustLevel: 'medium',
        requiredAttestors: [],
        votingRequired: false,
        votingPeriod: 7 * 24 * 60 * 60 * 1000,
        quorum: 0.5
      },
      created: new Date().toISOString(),
      lastModified: new Date().toISOString()
    };

    repository.branches.set(defaultBranch, defaultIdentityBranch);

    // Add owner as contributor
    repository.contributors.set(ownerDid, {
      did: ownerDid,
      role: 'owner',
      permissions: ['read', 'write', 'merge', 'admin'],
      joinedAt: new Date().toISOString(),
      lastActivity: new Date().toISOString()
    });

    this.repositories.set(repositoryId, repository);
    return repository;
  }

  /**
   * Create identity-verified commit
   */
  async createIdentityCommit(
    repositoryId: string,
    branchName: string,
    authorDid: string,
    message: string,
    files: { path: string; content: string }[],
    options: {
      committerDid?: string;
      credentials?: string[];
      address?: {
        universeId: string;
        realmId: string;
        coordinate: { x: number; y: number; z: number; dimension: number };
      };
    } = {}
  ): Promise<IdentityCommit> {
    const repository = this.repositories.get(repositoryId);
    if (!repository) {
      throw new Error(`Repository not found: ${repositoryId}`);
    }

    const branch = repository.branches.get(branchName);
    if (!branch) {
      throw new Error(`Branch not found: ${branchName}`);
    }

    // Verify author identity
    const authorProfile = this.identityManager.getIdentityProfile(authorDid);
    if (!authorProfile) {
      throw new Error(`Author identity not found: ${authorDid}`);
    }

    // Check permissions
    if (!this.hasPermission(authorDid, branch, 'write')) {
      throw new Error(`No write permission for ${authorDid} on ${branchName}`);
    }

    // Verify credentials if required
    if (branch.requiredCredentials.length > 0) {
      await this.verifyRequiredCredentials(authorDid, branch.requiredCredentials);
    }

    // Create multiverse address if provided
    let authorAddress;
    if (options.address) {
      authorAddress = await this.addressManager.createAddress(
        authorDid,
        options.address.universeId,
        options.address.realmId,
        options.address.coordinate
      );
    }

    // Create regular MindGit commit
    const commitHash = await this.mindgit.createCommit(
      repositoryId,
      branchName,
      message,
      files
    );

    // Create identity proof
    const identityProof = await this.createIdentityProof(
      authorDid,
      commitHash,
      message,
      options.committerDid || authorDid
    );

    // Perform identity verification
    const verificationResult = await this.performIdentityVerification(
      authorDid,
      this.config.verificationLevel
    );

    // Create identity commit
    const identityCommit: IdentityCommit = {
      commitHash,
      authorDid,
      committerDid: options.committerDid || authorDid,
      authorAddress: authorAddress?.universeId,
      committerAddress: authorAddress?.universeId,
      identityProof,
      verificationStatus: this.determineVerificationStatus(verificationResult),
      credentials: options.credentials || [],
      attestations: [],
      metadata: {
        trustLevel: verificationResult.trustScore.toString(),
        riskScore: verificationResult.riskAssessment.riskScore,
        verificationLevel: this.config.verificationLevel,
        jurisdiction: 'global',
        complianceFrameworks: [],
        multiverseCoordinates: options.address
      }
    };

    this.identityCommits.set(commitHash, identityCommit);

    // Update contributor activity
    const contributor = repository.contributors.get(authorDid);
    if (contributor) {
      contributor.lastActivity = new Date().toISOString();
    }

    return identityCommit;
  }

  /**
   * Create identity-verified merge
   */
  async createIdentityMerge(
    repositoryId: string,
    sourceBranch: string,
    targetBranch: string,
    mergeAuthorDid: string,
    mergeMessage: string,
    options: {
      requireVerification?: boolean;
      votingRequired?: boolean;
    } = {}
  ): Promise<IdentityCommit> {
    const repository = this.repositories.get(repositoryId);
    if (!repository) {
      throw new Error(`Repository not found: ${repositoryId}`);
    }

    const targetBranch = repository.branches.get(targetBranch);
    if (!targetBranch) {
      throw new Error(`Target branch not found: ${targetBranch}`);
    }

    // Check merge permissions
    if (!this.hasPermission(mergeAuthorDid, targetBranch, 'merge')) {
      throw new Error(`No merge permission for ${mergeAuthorDid} on ${targetBranch}`);
    }

    // Verify merge requirements
    const requireVerification = options.requireVerification ?? targetBranch.mergePolicy.requireVerification;
    if (requireVerification) {
      const verification = await this.performIdentityVerification(
        mergeAuthorDid,
        'enhanced'
      );
      
      if (verification.trustScore < this.config.trustThreshold) {
        throw new Error(`Insufficient trust score for merge: ${verification.trustScore}`);
      }
    }

    // Perform voting if required
    if (options.votingRequired ?? targetBranch.mergePolicy.votingRequired) {
      await this.performMergeVoting(repositoryId, sourceBranch, targetBranch, mergeAuthorDid);
    }

    // Create merge commit
    const mergeCommit = await this.mindgit.mergeBranch(
      repositoryId,
      sourceBranch,
      targetBranch,
      mergeMessage
    );

    // Create identity proof for merge
    const identityProof = await this.createIdentityProof(
      mergeAuthorDid,
      mergeCommit,
      mergeMessage,
      mergeAuthorDid
    );

    const identityCommit: IdentityCommit = {
      commitHash: mergeCommit,
      authorDid: mergeAuthorDid,
      committerDid: mergeAuthorDid,
      identityProof,
      verificationStatus: 'verified',
      credentials: [],
      attestations: [],
      metadata: {
        trustLevel: 'high',
        riskScore: 0.2,
        verificationLevel: 'enhanced',
        jurisdiction: 'global',
        complianceFrameworks: [],
        mergeType: 'identity_verified'
      }
    };

    this.identityCommits.set(mergeCommit, identityCommit);
    return identityCommit;
  }

  /**
   * Add contributor to repository
   */
  async addContributor(
    repositoryId: string,
    contributorDid: string,
    role: 'maintainer' | 'contributor' | 'viewer',
    addedBy: string
  ): Promise<void> {
    const repository = this.repositories.get(repositoryId);
    if (!repository) {
      throw new Error(`Repository not found: ${repositoryId}`);
    }

    // Check if adder has admin permission
    const defaultBranch = repository.branches.get(repository.defaultBranch);
    if (!defaultBranch || !this.hasPermission(addedBy, defaultBranch, 'admin')) {
      throw new Error(`No admin permission for ${addedBy}`);
    }

    // Verify contributor identity
    const contributorProfile = this.identityManager.getIdentityProfile(contributorDid);
    if (!contributorProfile) {
      throw new Error(`Contributor identity not found: ${contributorDid}`);
    }

    // Define permissions based on role
    const permissions = this.getPermissionsForRole(role);

    // Add contributor
    repository.contributors.set(contributorDid, {
      did: contributorDid,
      role,
      permissions,
      joinedAt: new Date().toISOString(),
      lastActivity: new Date().toISOString()
    });

    // Update default branch access control
    const accessControlEntry: AccessControlEntry = {
      entityDid: contributorDid,
      permissions,
      grantedBy: addedBy,
      grantedAt: new Date().toISOString()
    };

    defaultBranch.accessControl.push(accessControlEntry);
  }

  /**
   * Get repository by ID
   */
  getRepository(repositoryId: string): IdentityRepository | null {
    return this.repositories.get(repositoryId) || null;
  }

  /**
   * Get identity commit by hash
   */
  getIdentityCommit(commitHash: string): IdentityCommit | null {
    return this.identityCommits.get(commitHash) || null;
  }

  /**
   * List repositories for identity
   */
  listRepositoriesForIdentity(did: string): IdentityRepository[] {
    const repositories: IdentityRepository[] = [];
    for (const repository of this.repositories.values()) {
      if (repository.contributors.has(did)) {
        repositories.push(repository);
      }
    }
    return repositories;
  }

  /**
   * Sync repository across multiverse
   */
  async syncAcrossMultiverse(
    repositoryId: string,
    targetUniverses: string[]
  ): Promise<void> {
    const repository = this.repositories.get(repositoryId);
    if (!repository) {
      throw new Error(`Repository not found: ${repositoryId}`);
    }

    if (!repository.metadata.multiverse.syncEnabled) {
      throw new Error('Multiverse sync not enabled for this repository');
    }

    for (const universeId of targetUniverses) {
      // Create addresses for all contributors in target universe
      for (const [contributorDid] of repository.contributors) {
        const addresses = this.addressManager.getAddressesByIdentity(contributorDid);
        const hasAddressInUniverse = addresses.some(addr => addr.universeId === universeId);
        
        if (!hasAddressInUniverse) {
          // Create address in target universe
          await this.addressManager.createAddress(
            contributorDid,
            universeId,
            `${repositoryId}-realm`,
            { x: 0, y: 0, z: 0, dimension: 1 }
          );
        }
      }

      // Sync repository data
      console.log(`Syncing repository ${repositoryId} to universe ${universeId}`);
    }
  }

  /**
   * Private helper methods
   */
  private async generateRepositoryId(name: string, ownerDid: string): Promise<string> {
    const data = `${name}:${ownerDid}:${Date.now()}`;
    const hash = await this.crypto.hashData(data);
    return `repo_${hash.substring(0, 16)}`;
  }

  private hasPermission(did: string, branch: IdentityBranch, permission: string): boolean {
    const accessEntry = branch.accessControl.find(entry => entry.entityDid === did);
    if (!accessEntry) return false;
    
    return accessEntry.permissions.includes(permission as any);
  }

  private getPermissionsForRole(role: 'maintainer' | 'contributor' | 'viewer'): string[] {
    switch (role) {
      case 'maintainer':
        return ['read', 'write', 'merge'];
      case 'contributor':
        return ['read', 'write'];
      case 'viewer':
        return ['read'];
      default:
        return [];
    }
  }

  private async verifyRequiredCredentials(did: string, requiredCredentials: string[]): Promise<void> {
    const credentials = this.credentialManager.getCredentialsBySubject(did);
    
    for (const requiredCred of requiredCredentials) {
      const hasCredential = credentials.some(cred => 
        cred.type.includes(requiredCred)
      );
      
      if (!hasCredential) {
        throw new Error(`Missing required credential: ${requiredCred}`);
      }
    }
  }

  private async createIdentityProof(
    authorDid: string,
    commitHash: string,
    message: string,
    committerDid: string
  ): Promise<string> {
    const proofData = {
      authorDid,
      commitHash,
      message,
      committerDid,
      timestamp: new Date().toISOString()
    };

    // Get author's signing key
    const authorProfile = this.identityManager.getIdentityProfile(authorDid);
    if (!authorProfile) {
      throw new Error(`Author profile not found: ${authorDid}`);
    }

    const signingKey = authorProfile.keyPairs.find(
      kp => kp.keyId === authorProfile.currentSigningKey
    )?.privateKey;

    if (!signingKey) {
      throw new Error(`No signing key found for ${authorDid}`);
    }

    // Create proof using cubic signature
    const cubicSignature = new CubicSignature();
    return await cubicSignature.sign(JSON.stringify(proofData), signingKey);
  }

  private async performIdentityVerification(
    did: string,
    level: 'basic' | 'standard' | 'enhanced' | 'maximum'
  ): Promise<any> {
    const verificationRequest = await this.identityVerifier.createVerificationRequest(
      'system',
      did,
      ['identity', 'reputation'],
      level
    );

    return await this.identityVerifier.processVerificationRequest(verificationRequest);
  }

  private determineVerificationStatus(verificationResult: any): 'verified' | 'pending' | 'rejected' | 'expired' {
    return verificationResult.status;
  }

  private async performMergeVoting(
    repositoryId: string,
    sourceBranch: string,
    targetBranch: string,
    proposerDid: string
  ): Promise<void> {
    const repository = this.repositories.get(repositoryId);
    if (!repository) {
      throw new Error(`Repository not found: ${repositoryId}`);
    }

    const targetBranchObj = repository.branches.get(targetBranch);
    if (!targetBranchObj) {
      throw new Error(`Target branch not found: ${targetBranch}`);
    }

    const votingMechanism = repository.governance.votingMechanism;
    if (!votingMechanism) {
      return; // No voting required
    }

    // In a real implementation, this would:
    // 1. Create a voting proposal
    // 2. Notify eligible voters
    // 3. Collect votes
    // 4. Check quorum requirements
    // 5. Execute merge if approved

    console.log(`Voting initiated for merge ${sourceBranch} -> ${targetBranch} by ${proposerDid}`);
  }
}