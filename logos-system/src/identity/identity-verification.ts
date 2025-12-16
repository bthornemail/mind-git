/**
 * Identity Verification and Attestation System
 * 
 * Provides comprehensive identity verification, credential management,
 * and attestation services for sovereign identities across the multiverse.
 */

import { PolyF2 } from '../core/polynomial/index';
import { AALType } from '../core/aal/types';
import { DIDDocument } from './did-core';
import { CubicSignature } from '../core/cryptography/cubic-signature';
import { ProductionCryptography } from '@cryptography/production-crypto';

export interface VerifiableCredential {
  '@context': string[];
  type: string[];
  issuer: string;
  issuanceDate: string;
  expirationDate?: string;
  credentialSubject: CredentialSubject;
  credentialStatus?: CredentialStatus;
  credentialSchema?: CredentialSchema;
  evidence?: Evidence[];
  proof: CredentialProof;
}

export interface CredentialSubject {
  id: string;
  [key: string]: any;
}

export interface CredentialStatus {
  id: string;
  type: string;
  statusPurpose: string;
}

export interface CredentialSchema {
  id: string;
  type: string;
}

export interface Evidence {
  type: string;
  documentId: string;
  verifier: string;
  verificationDate: string;
  evidenceDocument: string;
}

export interface CredentialProof {
  type: string;
  created: string;
  proofPurpose: string;
  verificationMethod: string;
  jws?: string;
  proofValue?: string;
  challenge?: string;
  domain?: string;
}

export interface Attestation {
  attestationId: string;
  attestor: string;
  subject: string;
  claims: Claim[];
  issuanceDate: string;
  expirationDate?: string;
  revocationDate?: string;
  trustLevel: TrustLevel;
  verificationMethod: string;
  proof: string;
  metadata: AttestationMetadata;
}

export interface Claim {
  claimId: string;
  type: string;
  value: any;
  confidence: number;
  evidence?: Evidence[];
  verificationStatus: 'pending' | 'verified' | 'rejected' | 'expired';
}

export interface AttestationMetadata {
  jurisdiction: string;
  complianceFrameworks: string[];
  auditTrail: AuditEntry[];
  tags: string[];
  properties: Record<string, any>;
}

export interface AuditEntry {
  timestamp: string;
  action: string;
  actor: string;
  details: Record<string, any>;
}

export interface VerificationRequest {
  requestId: string;
  requester: string;
  subject: string;
  requiredClaims: string[];
  verificationLevel: VerificationLevel;
  constraints: VerificationConstraints;
  timestamp: string;
  expires: string;
}

export interface VerificationResponse {
  requestId: string;
  status: 'approved' | 'rejected' | 'pending' | 'expired';
  verifiedClaims: VerifiedClaim[];
  trustScore: number;
  riskAssessment: RiskAssessment;
  timestamp: string;
  evidence: Evidence[];
}

export interface VerifiedClaim {
  claimId: string;
  type: string;
  value: any;
  verified: boolean;
  confidence: number;
  sources: string[];
  verificationDate: string;
}

export interface RiskAssessment {
  riskLevel: 'low' | 'medium' | 'high' | 'critical';
  riskScore: number;
  factors: RiskFactor[];
  recommendations: string[];
}

export interface RiskFactor {
  factor: string;
  weight: number;
  value: number;
  description: string;
}

export interface VerificationConstraints {
  maxAge?: number;
  minTrustLevel?: TrustLevel;
  requiredAttestors?: string[];
  forbiddenAttestors?: string[];
  jurisdiction?: string;
  complianceFrameworks?: string[];
}

export type TrustLevel = 'unknown' | 'low' | 'medium' | 'high' | 'maximum';
export type VerificationLevel = 'basic' | 'standard' | 'enhanced' | 'maximum';

/**
 * Credential Manager
 */
export class CredentialManager {
  private crypto: ProductionCrypto;
  private cubicSignature: CubicSignature;
  private credentialStore: Map<string, VerifiableCredential> = new Map();
  private schemaRegistry: Map<string, CredentialSchema> = new Map();

  constructor() {
    this.crypto = new ProductionCrypto();
    this.cubicSignature = new CubicSignature();
    this.initializeDefaultSchemas();
  }

  /**
   * Create verifiable credential
   */
  async createCredential(
    issuerDid: string,
    subjectDid: string,
    claims: Record<string, any>,
    credentialType: string[],
    signingKey: string,
    options: {
      expirationDate?: Date;
      evidence?: Evidence[];
      schema?: string;
    } = {}
  ): Promise<VerifiableCredential> {
    const credentialId = await this.generateCredentialId();
    const timestamp = new Date().toISOString();

    const credential: VerifiableCredential = {
      '@context': [
        'https://www.w3.org/2018/credentials/v1',
        'https://www.w3.org/2018/credentials/examples/v1'
      ],
      type: ['VerifiableCredential', ...credentialType],
      issuer: issuerDid,
      issuanceDate: timestamp,
      expirationDate: options.expirationDate?.toISOString(),
      credentialSubject: {
        id: subjectDid,
        ...claims
      },
      evidence: options.evidence,
      credentialSchema: options.schema ? {
        id: options.schema,
        type: 'JsonSchemaValidator2018'
      } : undefined,
      proof: await this.createCredentialProof(
        credentialId,
        issuerDid,
        signingKey,
        'assertionMethod'
      )
    };

    this.credentialStore.set(credentialId, credential);
    return credential;
  }

  /**
   * Verify credential
   */
  async verifyCredential(
    credential: VerifiableCredential,
    issuerPublicKey: string
  ): Promise<{
    valid: boolean;
    expired: boolean;
    revoked: boolean;
    errors: string[];
  }> {
    const errors: string[] = [];
    let valid = true;
    let expired = false;
    let revoked = false;

    // Check expiration
    if (credential.expirationDate) {
      const expirationTime = new Date(credential.expirationDate).getTime();
      if (Date.now() > expirationTime) {
        expired = true;
        valid = false;
        errors.push('Credential has expired');
      }
    }

    // Verify proof
    if (credential.proof) {
      const proofValid = await this.verifyCredentialProof(
        credential,
        issuerPublicKey
      );
      if (!proofValid) {
        valid = false;
        errors.push('Invalid credential proof');
      }
    } else {
      valid = false;
      errors.push('Missing credential proof');
    }

    // Verify schema if present
    if (credential.credentialSchema) {
      const schemaValid = await this.verifyCredentialSchema(credential);
      if (!schemaValid) {
        valid = false;
        errors.push('Credential does not match schema');
      }
    }

    return { valid, expired, revoked, errors };
  }

  /**
   * Revoke credential
   */
  async revokeCredential(
    credentialId: string,
    reason: string,
    signingKey: string
  ): Promise<void> {
    const credential = this.credentialStore.get(credentialId);
    if (!credential) {
      throw new Error(`Credential not found: ${credentialId}`);
    }

    // Create revocation status
    const status: CredentialStatus = {
      id: `${credentialId}#status`,
      type: 'RevocationList2020Status',
      statusPurpose: 'revocation'
    };

    credential.credentialStatus = status;

    // In a real implementation, this would update a revocation list
    console.log(`Credential ${credentialId} revoked: ${reason}`);
  }

  /**
   * Get credentials by subject
   */
  getCredentialsBySubject(subjectDid: string): VerifiableCredential[] {
    const credentials: VerifiableCredential[] = [];
    for (const credential of this.credentialStore.values()) {
      if (credential.credentialSubject.id === subjectDid) {
        credentials.push(credential);
      }
    }
    return credentials;
  }

  /**
   * Get credentials by issuer
   */
  getCredentialsByIssuer(issuerDid: string): VerifiableCredential[] {
    const credentials: VerifiableCredential[] = [];
    for (const credential of this.credentialStore.values()) {
      if (credential.issuer === issuerDid) {
        credentials.push(credential);
      }
    }
    return credentials;
  }

  /**
   * Register credential schema
   */
  registerSchema(schema: CredentialSchema): void {
    this.schemaRegistry.set(schema.id, schema);
  }

  /**
   * Private helper methods
   */
  private async generateCredentialId(): Promise<string> {
    const data = `credential:${Date.now()}:${Math.random()}`;
    const hash = await this.crypto.hashData(data);
    return `cred_${hash.substring(0, 16)}`;
  }

  private async createCredentialProof(
    credentialId: string,
    issuerDid: string,
    signingKey: string,
    proofPurpose: string
  ): Promise<CredentialProof> {
    const timestamp = new Date().toISOString();
    const challenge = await this.crypto.generateSecureRandom(16);

    const proofData = {
      credentialId,
      issuerDid,
      timestamp,
      challenge: challenge.toString('hex')
    };

    const signature = await this.cubicSignature.sign(
      JSON.stringify(proofData),
      signingKey
    );

    return {
      type: 'Ed25519Signature2018',
      created: timestamp,
      proofPurpose,
      verificationMethod: `${issuerDid}#key-1`,
      proofValue: signature,
      challenge: challenge.toString('hex')
    };
  }

  private async verifyCredentialProof(
    credential: VerifiableCredential,
    publicKey: string
  ): Promise<boolean> {
    if (!credential.proof) return false;

    const proofData = {
      credentialId: credential.id || 'unknown',
      issuerDid: credential.issuer,
      timestamp: credential.proof.created,
      challenge: credential.proof.challenge
    };

    return await this.cubicSignature.verify(
      JSON.stringify(proofData),
      credential.proof.proofValue!,
      publicKey
    );
  }

  private async verifyCredentialSchema(credential: VerifiableCredential): Promise<boolean> {
    if (!credential.credentialSchema) return true;

    const schema = this.schemaRegistry.get(credential.credentialSchema.id);
    if (!schema) return false;

    // Simplified schema validation - in production use proper JSON Schema validation
    return true;
  }

  private initializeDefaultSchemas(): void {
    // Register common credential schemas
    const schemas = [
      {
        id: 'https://schemas.mindgit.dev/identity/1.0',
        type: 'JsonSchemaValidator2018'
      },
      {
        id: 'https://schemas.mindgit.dev/education/1.0',
        type: 'JsonSchemaValidator2018'
      },
      {
        id: 'https://schemas.mindgit.dev/professional/1.0',
        type: 'JsonSchemaValidator2018'
      }
    ];

    schemas.forEach(schema => this.registerSchema(schema));
  }
}

/**
 * Attestation Manager
 */
export class AttestationManager {
  private crypto: ProductionCrypto;
  private cubicSignature: CubicSignature;
  private attestationStore: Map<string, Attestation> = new Map();
  private trustRegistry: Map<string, TrustLevel> = new Map();

  constructor() {
    this.crypto = new ProductionCrypto();
    this.cubicSignature = new CubicSignature();
  }

  /**
   * Create attestation
   */
  async createAttestation(
    attestorDid: string,
    subjectDid: string,
    claims: Claim[],
    trustLevel: TrustLevel,
    signingKey: string,
    metadata: Partial<AttestationMetadata> = {}
  ): Promise<Attestation> {
    const attestationId = await this.generateAttestationId();
    const timestamp = new Date().toISOString();

    const attestation: Attestation = {
      attestationId,
      attestor: attestorDid,
      subject: subjectDid,
      claims,
      issuanceDate: timestamp,
      trustLevel,
      verificationMethod: `${attestorDid}#key-1`,
      proof: await this.createAttestationProof(
        attestationId,
        attestorDid,
        subjectDid,
        claims,
        signingKey
      ),
      metadata: {
        jurisdiction: 'global',
        complianceFrameworks: [],
        auditTrail: [{
          timestamp,
          action: 'created',
          actor: attestorDid,
          details: { claims: claims.length, trustLevel }
        }],
        tags: [],
        properties: {},
        ...metadata
      }
    };

    this.attestationStore.set(attestationId, attestation);
    return attestation;
  }

  /**
   * Verify attestation
   */
  async verifyAttestation(
    attestation: Attestation,
    attestorPublicKey: string
  ): Promise<{
    valid: boolean;
    expired: boolean;
    revoked: boolean;
    trustLevel: TrustLevel;
    errors: string[];
  }> {
    const errors: string[] = [];
    let valid = true;
    let expired = false;
    let revoked = false;

    // Check expiration
    if (attestation.expirationDate) {
      const expirationTime = new Date(attestation.expirationDate).getTime();
      if (Date.now() > expirationTime) {
        expired = true;
        valid = false;
        errors.push('Attestation has expired');
      }
    }

    // Check revocation
    if (attestation.revocationDate) {
      revoked = true;
      valid = false;
      errors.push('Attestation has been revoked');
    }

    // Verify proof
    const proofValid = await this.verifyAttestationProof(
      attestation,
      attestorPublicKey
    );
    if (!proofValid) {
      valid = false;
      errors.push('Invalid attestation proof');
    }

    return { valid, expired, revoked, trustLevel: attestation.trustLevel, errors };
  }

  /**
   * Revoke attestation
   */
  async revokeAttestation(
    attestationId: string,
    reason: string,
    signingKey: string
  ): Promise<void> {
    const attestation = this.attestationStore.get(attestationId);
    if (!attestation) {
      throw new Error(`Attestation not found: ${attestationId}`);
    }

    attestation.revocationDate = new Date().toISOString();
    
    // Add to audit trail
    attestation.metadata.auditTrail.push({
      timestamp: new Date().toISOString(),
      action: 'revoked',
      actor: 'system',
      details: { reason }
    });

    console.log(`Attestation ${attestationId} revoked: ${reason}`);
  }

  /**
   * Get attestations by subject
   */
  getAttestationsBySubject(subjectDid: string): Attestation[] {
    const attestations: Attestation[] = [];
    for (const attestation of this.attestationStore.values()) {
      if (attestation.subject === subjectDid) {
        attestations.push(attestation);
      }
    }
    return attestations;
  }

  /**
   * Get attestations by attestor
   */
  getAttestationsByAttestor(attestorDid: string): Attestation[] {
    const attestations: Attestation[] = [];
    for (const attestation of this.attestationStore.values()) {
      if (attestation.attestor === attestorDid) {
        attestations.push(attestation);
      }
    }
    return attestations;
  }

  /**
   * Set trust level for entity
   */
  setTrustLevel(entityDid: string, trustLevel: TrustLevel): void {
    this.trustRegistry.set(entityDid, trustLevel);
  }

  /**
   * Get trust level for entity
   */
  getTrustLevel(entityDid: string): TrustLevel {
    return this.trustRegistry.get(entityDid) || 'unknown';
  }

  /**
   * Private helper methods
   */
  private async generateAttestationId(): Promise<string> {
    const data = `attestation:${Date.now()}:${Math.random()}`;
    const hash = await this.crypto.hashData(data);
    return `attest_${hash.substring(0, 16)}`;
  }

  private async createAttestationProof(
    attestationId: string,
    attestorDid: string,
    subjectDid: string,
    claims: Claim[],
    signingKey: string
  ): Promise<string> {
    const proofData = {
      attestationId,
      attestorDid,
      subjectDid,
      claims: claims.map(c => ({ type: c.type, value: c.value })),
      timestamp: new Date().toISOString()
    };

    return await this.cubicSignature.sign(
      JSON.stringify(proofData),
      signingKey
    );
  }

  private async verifyAttestationProof(
    attestation: Attestation,
    publicKey: string
  ): Promise<boolean> {
    const proofData = {
      attestationId: attestation.attestationId,
      attestorDid: attestation.attestor,
      subjectDid: attestation.subject,
      claims: attestation.claims.map(c => ({ type: c.type, value: c.value })),
      timestamp: attestation.issuanceDate
    };

    return await this.cubicSignature.verify(
      JSON.stringify(proofData),
      attestation.proof,
      publicKey
    );
  }
}

/**
 * Identity Verifier
 */
export class IdentityVerifier {
  private credentialManager: CredentialManager;
  private attestationManager: AttestationManager;
  private crypto: ProductionCrypto;

  constructor() {
    this.credentialManager = new CredentialManager();
    this.attestationManager = new AttestationManager();
    this.crypto = new ProductionCrypto();
  }

  /**
   * Process verification request
   */
  async processVerificationRequest(
    request: VerificationRequest
  ): Promise<VerificationResponse> {
    const subjectCredentials = this.credentialManager.getCredentialsBySubject(request.subject);
    const subjectAttestations = this.attestationManager.getAttestationsBySubject(request.subject);

    const verifiedClaims: VerifiedClaim[] = [];
    const evidence: Evidence[] = [];
    let totalTrustScore = 0;
    let trustFactors = 0;

    // Verify credentials
    for (const credential of subjectCredentials) {
      const verification = await this.credentialManager.verifyCredential(
        credential,
        'placeholder-public-key' // In production, get from DID document
      );

      if (verification.valid) {
        // Extract claims from credential
        for (const [key, value] of Object.entries(credential.credentialSubject)) {
          if (key !== 'id' && request.requiredClaims?.includes(key)) {
            verifiedClaims.push({
              claimId: `${credential.id}:${key}`,
              type: key,
              value,
              verified: true,
              confidence: 0.9,
              sources: [credential.issuer],
              verificationDate: new Date().toISOString()
            });
          }
        }

        // Add evidence
        if (credential.evidence) {
          evidence.push(...credential.evidence);
        }

        // Calculate trust score
        const issuerTrust = this.attestationManager.getTrustLevel(credential.issuer);
        totalTrustScore += this.trustLevelToScore(issuerTrust);
        trustFactors++;
      }
    }

    // Verify attestations
    for (const attestation of subjectAttestations) {
      const verification = await this.attestationManager.verifyAttestation(
        attestation,
        'placeholder-public-key' // In production, get from DID document
      );

      if (verification.valid) {
        for (const claim of attestation.claims) {
          if (request.requiredClaims.includes(claim.type)) {
            verifiedClaims.push({
              claimId: claim.claimId,
              type: claim.type,
              value: claim.value,
              verified: claim.verificationStatus === 'verified',
              confidence: claim.confidence,
              sources: [attestation.attestor],
              verificationDate: new Date().toISOString()
            });
          }
        }

        totalTrustScore += this.trustLevelToScore(verification.trustLevel);
        trustFactors++;
      }
    }

    // Calculate final trust score
    const finalTrustScore = trustFactors > 0 ? totalTrustScore / trustFactors : 0;

    // Perform risk assessment
    const riskAssessment = this.performRiskAssessment(
      verifiedClaims,
      finalTrustScore,
      request.constraints
    );

    // Determine status
    const status = this.determineVerificationStatus(
      verifiedClaims,
      request.requiredClaims,
      riskAssessment,
      request.verificationLevel
    );

    return {
      requestId: request.requestId,
      status,
      verifiedClaims,
      trustScore: finalTrustScore,
      riskAssessment,
      timestamp: new Date().toISOString(),
      evidence
    };
  }

  /**
   * Create verification request
   */
  async createVerificationRequest(
    requesterDid: string,
    subjectDid: string,
    requiredClaims: string[],
    verificationLevel: VerificationLevel,
    constraints: VerificationConstraints = {},
    expiresIn: number = 3600
  ): Promise<VerificationRequest> {
    const requestId = await this.generateRequestId();
    const timestamp = new Date().toISOString();
    const expires = new Date(Date.now() + expiresIn * 1000).toISOString();

    return {
      requestId,
      requester: requesterDid,
      subject: subjectDid,
      requiredClaims,
      verificationLevel,
      constraints,
      timestamp,
      expires
    };
  }

  /**
   * Private helper methods
   */
  private async generateRequestId(): Promise<string> {
    const data = `verification:${Date.now()}:${Math.random()}`;
    const hash = await this.crypto.hashData(data);
    return `verify_${hash.substring(0, 16)}`;
  }

  private trustLevelToScore(trustLevel: TrustLevel): number {
    switch (trustLevel) {
      case 'unknown': return 0.1;
      case 'low': return 0.3;
      case 'medium': return 0.6;
      case 'high': return 0.8;
      case 'maximum': return 1.0;
      default: return 0;
    }
  }

  private performRiskAssessment(
    verifiedClaims: VerifiedClaim[],
    trustScore: number,
    constraints: VerificationConstraints
  ): RiskAssessment {
    const factors: RiskFactor[] = [];

    // Trust score factor
    factors.push({
      factor: 'trust_score',
      weight: 0.4,
      value: trustScore,
      description: `Overall trust score: ${(trustScore * 100).toFixed(1)}%`
    });

    // Claim completeness factor
    const requiredClaims = constraints.requiredClaims?.length || 0;
    const verifiedRequiredClaims = verifiedClaims.filter(c => 
      constraints.requiredClaims?.includes(c.type)
    ).length;
    const completenessScore = requiredClaims > 0 ? verifiedRequiredClaims / requiredClaims : 1;

    factors.push({
      factor: 'claim_completeness',
      weight: 0.3,
      value: completenessScore,
      description: `Verified ${verifiedRequiredClaims}/${requiredClaims} required claims`
    });

    // Confidence factor
    const avgConfidence = verifiedClaims.length > 0 
      ? verifiedClaims.reduce((sum, c) => sum + c.confidence, 0) / verifiedClaims.length
      : 0;

    factors.push({
      factor: 'confidence',
      weight: 0.3,
      value: avgConfidence,
      description: `Average claim confidence: ${(avgConfidence * 100).toFixed(1)}%`
    });

    // Calculate overall risk score
    const riskScore = factors.reduce((sum, factor) => sum + factor.value * factor.weight, 0);
    
    // Determine risk level
    let riskLevel: 'low' | 'medium' | 'high' | 'critical';
    if (riskScore >= 0.8) riskLevel = 'low';
    else if (riskScore >= 0.6) riskLevel = 'medium';
    else if (riskScore >= 0.4) riskLevel = 'high';
    else riskLevel = 'critical';

    // Generate recommendations
    const recommendations: string[] = [];
    if (trustScore < 0.5) recommendations.push('Require additional attestations from trusted sources');
    if (completenessScore < 0.8) recommendations.push('Request missing required claims');
    if (avgConfidence < 0.7) recommendations.push('Verify claims with additional evidence');

    return {
      riskLevel,
      riskScore,
      factors,
      recommendations
    };
  }

  private determineVerificationStatus(
    verifiedClaims: VerifiedClaim[],
    requiredClaims: string[],
    riskAssessment: RiskAssessment,
    verificationLevel: VerificationLevel
  ): 'approved' | 'rejected' | 'pending' | 'expired' {
    // Check if all required claims are verified
    const verifiedRequiredClaims = verifiedClaims.filter(c => 
      requiredClaims.includes(c.type) && c.verified
    );

    if (verifiedRequiredClaims.length < requiredClaims.length) {
      return 'rejected';
    }

    // Check risk level against verification level requirements
    const minRiskScore = this.getMinRiskScoreForLevel(verificationLevel);
    if (riskAssessment.riskScore < minRiskScore) {
      return 'rejected';
    }

    return 'approved';
  }

  private getMinRiskScoreForLevel(level: VerificationLevel): number {
    switch (level) {
      case 'basic': return 0.3;
      case 'standard': return 0.5;
      case 'enhanced': return 0.7;
      case 'maximum': return 0.9;
      default: return 0.5;
    }
  }
}