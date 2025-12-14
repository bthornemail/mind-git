/**
 * DID (Decentralized Identifier) Core System
 * 
 * Implements W3C DID specification with post-quantum security
 * and multiverse addressing support for sovereign identity management.
 */

import { Polynomial } from '../core/polynomial/polynomial';
import { AALType } from '../core/aal/types';
import { CubicSignature } from '../production/cubic-signature';
import { ProductionCrypto } from '../production/production-crypto';

export interface DIDDocument {
  '@context': string[];
  id: string;
  verificationMethod: VerificationMethod[];
  authentication: string[];
  assertionMethod: string[];
  keyAgreement: string[];
  capabilityInvocation: string[];
  capabilityDelegation: string[];
  service: DIDService[];
  created: string;
  updated: string;
  proof: DIDProof;
}

export interface VerificationMethod {
  id: string;
  type: string;
  controller: string;
  publicKeyBase58?: string;
  publicKeyJwk?: JsonWebKey;
  blockchainAccountId?: string;
}

export interface DIDService {
  id: string;
  type: string;
  serviceEndpoint: string;
  [key: string]: any;
}

export interface DIDProof {
  type: string;
  created: string;
  proofPurpose: string;
  verificationMethod: string;
  jws?: string;
  proofValue?: string;
  challenge?: string;
  domain?: string;
}

export interface DIDResolutionResult {
  didDocument: DIDDocument;
  didResolutionMetadata: Record<string, any>;
  didDocumentMetadata: Record<string, any>;
}

export interface DIDOperation {
  type: 'create' | 'update' | 'deactivate' | 'recover';
  did: string;
  operationNumber: number;
  previousOperationHash?: string;
  proof: DIDProof;
  document?: DIDDocument;
  timestamp: string;
}

/**
 * DID Method for MindGit Sovereign Identity
 */
export class MindGitDIDMethod {
  private static readonly METHOD_NAME = 'mindgit';
  private static readonly METHOD_SPECIFIC_ID_REGEX = /^[a-zA-Z0-9]+:[a-zA-Z0-9_-]+$/;

  /**
   * Generate a new DID with method-specific identifier
   */
  static generateDID(identityKey: string, namespace: string = 'default'): string {
    const methodSpecificId = `${namespace}:${identityKey}`;
    return `did:${this.METHOD_NAME}:${methodSpecificId}`;
  }

  /**
   * Validate DID format
   */
  static validateDID(did: string): boolean {
    const parts = did.split(':');
    if (parts.length !== 3) return false;
    if (parts[0] !== 'did') return false;
    if (parts[1] !== this.METHOD_NAME) return false;
    return this.METHOD_SPECIFIC_ID_REGEX.test(parts[2]);
  }

  /**
   * Extract method-specific ID from DID
   */
  static extractMethodSpecificId(did: string): string {
    if (!this.validateDID(did)) {
      throw new Error('Invalid DID format');
    }
    return did.split(':')[2];
  }

  /**
   * Parse method-specific ID into namespace and identity key
   */
  static parseMethodSpecificId(methodSpecificId: string): { namespace: string; identityKey: string } {
    const parts = methodSpecificId.split(':');
    if (parts.length !== 2) {
      throw new Error('Invalid method-specific ID format');
    }
    return {
      namespace: parts[0],
      identityKey: parts[1]
    };
  }
}

/**
 * DID Document Manager
 */
export class DIDDocumentManager {
  private crypto: ProductionCrypto;
  private cubicSignature: CubicSignature;

  constructor() {
    this.crypto = new ProductionCrypto();
    this.cubicSignature = new CubicSignature();
  }

  /**
   * Create a new DID document
   */
  async createDIDDocument(
    did: string,
    verificationKey: string,
    controller: string,
    services: DIDService[] = []
  ): Promise<DIDDocument> {
    if (!MindGitDIDMethod.validateDID(did)) {
      throw new Error('Invalid DID format');
    }

    const timestamp = new Date().toISOString();
    
    const document: DIDDocument = {
      '@context': [
        'https://www.w3.org/ns/did/v1',
        'https://w3id.org/security/v1'
      ],
      id: did,
      verificationMethod: [
        {
          id: `${did}#key-1`,
          type: 'Ed25519VerificationKey2018',
          controller: controller,
          publicKeyBase58: verificationKey
        }
      ],
      authentication: [`${did}#key-1`],
      assertionMethod: [`${did}#key-1`],
      keyAgreement: [],
      capabilityInvocation: [`${did}#key-1`],
      capabilityDelegation: [],
      service: services,
      created: timestamp,
      updated: timestamp,
      proof: await this.createProof(did, 'assertionMethod', verificationKey)
    };

    return document;
  }

  /**
   * Update DID document
   */
  async updateDIDDocument(
    document: DIDDocument,
    updates: Partial<DIDDocument>,
    signingKey: string
  ): Promise<DIDDocument> {
    const updatedDocument: DIDDocument = {
      ...document,
      ...updates,
      updated: new Date().toISOString()
    };

    // Re-sign the document
    updatedDocument.proof = await this.createProof(
      document.id,
      'assertionMethod',
      signingKey
    );

    return updatedDocument;
  }

  /**
   * Create DID proof
   */
  private async createProof(
    did: string,
    proofPurpose: string,
    signingKey: string
  ): Promise<DIDProof> {
    const timestamp = new Date().toISOString();
    const challenge = await this.crypto.generateSecureRandom(32);
    
    const proofData = {
      did,
      proofPurpose,
      timestamp,
      challenge
    };

    const signature = await this.cubicSignature.sign(
      JSON.stringify(proofData),
      signingKey
    );

    return {
      type: 'Ed25519Signature2018',
      created: timestamp,
      proofPurpose,
      verificationMethod: `${did}#key-1`,
      proofValue: signature,
      challenge: challenge.toString('hex')
    };
  }

  /**
   * Verify DID document proof
   */
  async verifyProof(document: DIDDocument, publicKey: string): Promise<boolean> {
    if (!document.proof) return false;

    const proofData = {
      did: document.id,
      proofPurpose: document.proof.proofPurpose,
      timestamp: document.proof.created,
      challenge: document.proof.challenge
    };

    return await this.cubicSignature.verify(
      JSON.stringify(proofData),
      document.proof.proofValue!,
      publicKey
    );
  }

  /**
   * Add verification method to DID document
   */
  async addVerificationMethod(
    document: DIDDocument,
    method: VerificationMethod,
    signingKey: string
  ): Promise<DIDDocument> {
    const updatedDocument = {
      ...document,
      verificationMethod: [...document.verificationMethod, method],
      updated: new Date().toISOString()
    };

    updatedDocument.proof = await this.createProof(
      document.id,
      'assertionMethod',
      signingKey
    );

    return updatedDocument;
  }

  /**
   * Add service to DID document
   */
  async addService(
    document: DIDDocument,
    service: DIDService,
    signingKey: string
  ): Promise<DIDDocument> {
    const updatedDocument = {
      ...document,
      service: [...document.service, service],
      updated: new Date().toISOString()
    };

    updatedDocument.proof = await this.createProof(
      document.id,
      'assertionMethod',
      signingKey
    );

    return updatedDocument;
  }

  /**
   * Deactivate DID document
   */
  async deactivateDIDDocument(
    document: DIDDocument,
    signingKey: string
  ): Promise<DIDDocument> {
    const deactivatedDocument = {
      ...document,
      verificationMethod: [],
      authentication: [],
      assertionMethod: [],
      keyAgreement: [],
      capabilityInvocation: [],
      capabilityDelegation: [],
      service: [],
      updated: new Date().toISOString()
    };

    deactivatedDocument.proof = await this.createProof(
      document.id,
      'capabilityDelegation',
      signingKey
    );

    return deactivatedDocument;
  }
}

/**
 * DID Resolver
 */
export class DIDResolver {
  private documentCache: Map<string, DIDDocument> = new Map();
  private operationLog: Map<string, DIDOperation[]> = new Map();

  /**
   * Resolve DID to DID document
   */
  async resolve(did: string): Promise<DIDResolutionResult> {
    if (!MindGitDIDMethod.validateDID(did)) {
      throw new Error('Invalid DID format');
    }

    // Check cache first
    if (this.documentCache.has(did)) {
      const document = this.documentCache.get(did)!;
      return {
        didDocument: document,
        didResolutionMetadata: { contentType: 'application/did+ld+json' },
        didDocumentMetadata: { updated: document.updated }
      };
    }

    // Resolve from operation log
    const operations = this.operationLog.get(did) || [];
    const document = this.buildDocumentFromOperations(operations);

    if (document) {
      this.documentCache.set(did, document);
      return {
        didDocument: document,
        didResolutionMetadata: { contentType: 'application/did+ld+json' },
        didDocumentMetadata: { updated: document.updated }
      };
    }

    throw new Error(`DID not found: ${did}`);
  }

  /**
   * Build DID document from operation log
   */
  private buildDocumentFromOperations(operations: DIDOperation[]): DIDDocument | null {
    if (operations.length === 0) return null;

    // Sort operations by operation number
    operations.sort((a, b) => a.operationNumber - b.operationNumber);

    let document: DIDDocument | null = null;

    for (const operation of operations) {
      switch (operation.type) {
        case 'create':
          document = operation.document!;
          break;
        case 'update':
          if (document && operation.document) {
            document = operation.document;
          }
          break;
        case 'deactivate':
          if (document && operation.document) {
            document = operation.document;
          }
          break;
        case 'recover':
          if (operation.document) {
            document = operation.document;
          }
          break;
      }
    }

    return document;
  }

  /**
   * Record DID operation
   */
  async recordOperation(operation: DIDOperation): Promise<void> {
    const operations = this.operationLog.get(operation.did) || [];
    operations.push(operation);
    this.operationLog.set(operation.did, operations);

    // Clear cache for this DID
    this.documentCache.delete(operation.did);
  }

  /**
   * Get operation history for DID
   */
  getOperationHistory(did: string): DIDOperation[] {
    return this.operationLog.get(did) || [];
  }

  /**
   * Clear cache
   */
  clearCache(): void {
    this.documentCache.clear();
  }
}

/**
 * DID Registry
 */
export class DIDRegistry {
  private resolver: DIDResolver;
  private documentManager: DIDDocumentManager;

  constructor() {
    this.resolver = new DIDResolver();
    this.documentManager = new DIDDocumentManager();
  }

  /**
   * Register new DID
   */
  async registerDID(
    identityKey: string,
    verificationKey: string,
    namespace: string = 'default',
    services: DIDService[] = []
  ): Promise<{ did: string; document: DIDDocument }> {
    const did = MindGitDIDMethod.generateDID(identityKey, namespace);
    const document = await this.documentManager.createDIDDocument(
      did,
      verificationKey,
      did,
      services
    );

    const operation: DIDOperation = {
      type: 'create',
      did,
      operationNumber: 1,
      proof: document.proof,
      document,
      timestamp: new Date().toISOString()
    };

    await this.resolver.recordOperation(operation);

    return { did, document };
  }

  /**
   * Update DID document
   */
  async updateDID(
    did: string,
    updates: Partial<DIDDocument>,
    signingKey: string
  ): Promise<DIDDocument> {
    const resolution = await this.resolver.resolve(did);
    const updatedDocument = await this.documentManager.updateDIDDocument(
      resolution.didDocument,
      updates,
      signingKey
    );

    const operations = this.resolver.getOperationHistory(did);
    const nextOperationNumber = Math.max(...operations.map(op => op.operationNumber), 0) + 1;

    const operation: DIDOperation = {
      type: 'update',
      did,
      operationNumber: nextOperationNumber,
      previousOperationHash: this.hashOperation(operations[operations.length - 1]),
      proof: updatedDocument.proof,
      document: updatedDocument,
      timestamp: new Date().toISOString()
    };

    await this.resolver.recordOperation(operation);

    return updatedDocument;
  }

  /**
   * Deactivate DID
   */
  async deactivateDID(did: string, signingKey: string): Promise<DIDDocument> {
    const resolution = await this.resolver.resolve(did);
    const deactivatedDocument = await this.documentManager.deactivateDIDDocument(
      resolution.didDocument,
      signingKey
    );

    const operations = this.resolver.getOperationHistory(did);
    const nextOperationNumber = Math.max(...operations.map(op => op.operationNumber), 0) + 1;

    const operation: DIDOperation = {
      type: 'deactivate',
      did,
      operationNumber: nextOperationNumber,
      previousOperationHash: this.hashOperation(operations[operations.length - 1]),
      proof: deactivatedDocument.proof,
      document: deactivatedDocument,
      timestamp: new Date().toISOString()
    };

    await this.resolver.recordOperation(operation);

    return deactivatedDocument;
  }

  /**
   * Resolve DID
   */
  async resolveDID(did: string): Promise<DIDResolutionResult> {
    return await this.resolver.resolve(did);
  }

  /**
   * Get DID operation history
   */
  getDIDHistory(did: string): DIDOperation[] {
    return this.resolver.getOperationHistory(did);
  }

  /**
   * Hash operation for chain integrity
   */
  private hashOperation(operation: DIDOperation | undefined): string {
    if (!operation) return '';
    // Simple hash implementation - in production use cryptographic hash
    return Buffer.from(JSON.stringify(operation)).toString('base64');
  }
}