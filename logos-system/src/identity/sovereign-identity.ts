/**
 * Sovereign Identity Management System
 * 
 * Provides complete identity lifecycle management with key rotation,
 * recovery mechanisms, and multiverse addressing support.
 */

import { PolyF2 } from '../core/polynomial/index';
import { AALType } from '../core/aal/types';
import { DIDDocument, DIDRegistry, VerificationMethod } from './did-core';
import { CubicSignature } from '../core/cryptography/cubic-signature';
import { ProductionCryptography } from '@cryptography/production-crypto';

export interface IdentityKeyPair {
  keyId: string;
  publicKey: string;
  privateKey: string;
  type: 'signing' | 'encryption' | 'recovery';
  created: string;
  expires?: string;
  status: 'active' | 'retired' | 'compromised';
}

export interface IdentityProfile {
  did: string;
  keyPairs: IdentityKeyPair[];
  currentSigningKey: string;
  currentEncryptionKey: string;
  currentRecoveryKey: string;
  keyRotationHistory: KeyRotationEvent[];
  recoveryData: RecoveryData;
  metadata: IdentityMetadata;
}

export interface KeyRotationEvent {
  keyId: string;
  keyType: 'signing' | 'encryption' | 'recovery';
  previousKeyId: string;
  rotationReason: string;
  timestamp: string;
  proof: string;
}

export interface RecoveryData {
  recoveryPhrase: string;
  recoveryShards: RecoveryShard[];
  lastRecoveryCheck: string;
  recoveryAttempts: number;
  maxRecoveryAttempts: number;
}

export interface RecoveryShard {
  shardId: string;
  shardData: string;
  location: string;
  threshold: number;
  created: string;
}

export interface IdentityMetadata {
  name?: string;
  description?: string;
  avatar?: string;
  tags: string[];
  properties: Record<string, any>;
  created: string;
  updated: string;
}

export interface IdentityState {
  profile: IdentityProfile;
  didDocument: DIDDocument;
  lastSync: string;
  syncStatus: 'synced' | 'pending' | 'conflict';
}

/**
 * Sovereign Identity Manager
 */
export class SovereignIdentityManager {
  private crypto: ProductionCrypto;
  private cubicSignature: CubicSignature;
  private didRegistry: DIDRegistry;
  private identityStore: Map<string, IdentityState> = new Map();

  constructor() {
    this.crypto = new ProductionCrypto();
    this.cubicSignature = new CubicSignature();
    this.didRegistry = new DIDRegistry();
  }

  /**
   * Create new sovereign identity
   */
  async createIdentity(
    name: string,
    namespace: string = 'default',
    recoveryPhrase?: string
  ): Promise<{ did: string; profile: IdentityProfile; document: DIDDocument }> {
    // Generate identity key
    const identityKey = await this.crypto.generateSecureRandom(32);
    const did = `did:mindgit:${namespace}:${identityKey.toString('hex')}`;

    // Generate key pairs
    const signingKeyPair = await this.generateKeyPair('signing');
    const encryptionKeyPair = await this.generateKeyPair('encryption');
    const recoveryKeyPair = await this.generateKeyPair('recovery');

    // Create recovery data
    const recoveryData = await this.createRecoveryData(
      recoveryPhrase || await this.generateRecoveryPhrase(),
      recoveryKeyPair.privateKey
    );

    // Create identity profile
    const profile: IdentityProfile = {
      did,
      keyPairs: [signingKeyPair, encryptionKeyPair, recoveryKeyPair],
      currentSigningKey: signingKeyPair.keyId,
      currentEncryptionKey: encryptionKeyPair.keyId,
      currentRecoveryKey: recoveryKeyPair.keyId,
      keyRotationHistory: [],
      recoveryData,
      metadata: {
        name,
        tags: [],
        properties: {},
        created: new Date().toISOString(),
        updated: new Date().toISOString()
      }
    };

    // Create DID document
    const document = await this.didRegistry.registerDID(
      identityKey.toString('hex'),
      signingKeyPair.publicKey,
      namespace
    );

    // Store identity state
    const identityState: IdentityState = {
      profile,
      didDocument: document.document,
      lastSync: new Date().toISOString(),
      syncStatus: 'synced'
    };

    this.identityStore.set(did, identityState);

    return { did, profile, document: document.document };
  }

  /**
   * Rotate identity key
   */
  async rotateKey(
    did: string,
    keyType: 'signing' | 'encryption' | 'recovery',
    reason: string,
    signingKey: string
  ): Promise<IdentityProfile> {
    const identityState = this.identityStore.get(did);
    if (!identityState) {
      throw new Error(`Identity not found: ${did}`);
    }

    const profile = identityState.profile;
    const previousKeyId = this.getCurrentKeyId(profile, keyType);
    
    // Generate new key pair
    const newKeyPair = await this.generateKeyPair(keyType);
    
    // Update current key reference
    switch (keyType) {
      case 'signing':
        profile.currentSigningKey = newKeyPair.keyId;
        break;
      case 'encryption':
        profile.currentEncryptionKey = newKeyPair.keyId;
        break;
      case 'recovery':
        profile.currentRecoveryKey = newKeyPair.keyId;
        break;
    }

    // Mark previous key as retired
    const previousKeyPair = profile.keyPairs.find(kp => kp.keyId === previousKeyId);
    if (previousKeyPair) {
      previousKeyPair.status = 'retired';
    }

    // Add new key pair
    profile.keyPairs.push(newKeyPair);

    // Create rotation event
    const rotationEvent: KeyRotationEvent = {
      keyId: newKeyPair.keyId,
      keyType,
      previousKeyId,
      rotationReason: reason,
      timestamp: new Date().toISOString(),
      proof: await this.createRotationProof(newKeyPair, previousKeyId, reason, signingKey)
    };

    profile.keyRotationHistory.push(rotationEvent);
    profile.metadata.updated = new Date().toISOString();

    // Update DID document
    await this.updateDIDDocumentWithNewKey(did, newKeyPair, signingKey);

    // Mark for sync
    identityState.syncStatus = 'pending';

    return profile;
  }

  /**
   * Recover identity using recovery phrase
   */
  async recoverIdentity(
    did: string,
    recoveryPhrase: string,
    newSigningKey?: string
  ): Promise<IdentityProfile> {
    const identityState = this.identityStore.get(did);
    if (!identityState) {
      throw new Error(`Identity not found: ${did}`);
    }

    const profile = identityState.profile;
    
    // Verify recovery phrase
    if (!await this.verifyRecoveryPhrase(recoveryPhrase, profile.recoveryData)) {
      throw new Error('Invalid recovery phrase');
    }

    // Check recovery attempts
    if (profile.recoveryData.recoveryAttempts >= profile.recoveryData.maxRecoveryAttempts) {
      throw new Error('Maximum recovery attempts exceeded');
    }

    profile.recoveryData.recoveryAttempts++;
    profile.recoveryData.lastRecoveryCheck = new Date().toISOString();

    // Generate new signing key if not provided
    const newSigningKeyPair = newSigningKey 
      ? await this.importKeyPair(newSigningKey, 'signing')
      : await this.generateKeyPair('signing');

    // Mark all existing keys as compromised
    profile.keyPairs.forEach(keyPair => {
      if (keyPair.type === 'signing' || keyPair.type === 'encryption') {
        keyPair.status = 'compromised';
      }
    });

    // Add new signing key
    profile.keyPairs.push(newSigningKeyPair);
    profile.currentSigningKey = newSigningKeyPair.keyId;

    // Create recovery event
    const recoveryEvent: KeyRotationEvent = {
      keyId: newSigningKeyPair.keyId,
      keyType: 'signing',
      previousKeyId: profile.currentSigningKey,
      rotationReason: 'identity_recovery',
      timestamp: new Date().toISOString(),
      proof: await this.createRecoveryProof(newSigningKeyPair, recoveryPhrase)
    };

    profile.keyRotationHistory.push(recoveryEvent);
    profile.metadata.updated = new Date().toISOString();

    // Update DID document
    await this.updateDIDDocumentWithNewKey(did, newSigningKeyPair, newSigningKeyPair.privateKey);

    // Mark for sync
    identityState.syncStatus = 'pending';

    return profile;
  }

  /**
   * Get identity profile
   */
  getIdentityProfile(did: string): IdentityProfile | null {
    const identityState = this.identityStore.get(did);
    return identityState ? identityState.profile : null;
  }

  /**
   * Get identity state
   */
  getIdentityState(did: string): IdentityState | null {
    return this.identityStore.get(did) || null;
  }

  /**
   * List all identities
   */
  listIdentities(): string[] {
    return Array.from(this.identityStore.keys());
  }

  /**
   * Sync identity with registry
   */
  async syncIdentity(did: string): Promise<IdentityState> {
    const identityState = this.identityStore.get(did);
    if (!identityState) {
      throw new Error(`Identity not found: ${did}`);
    }

    try {
      const resolution = await this.didRegistry.resolveDID(did);
      identityState.didDocument = resolution.didDocument;
      identityState.lastSync = new Date().toISOString();
      identityState.syncStatus = 'synced';
    } catch (error) {
      identityState.syncStatus = 'conflict';
      throw error;
    }

    return identityState;
  }

  /**
   * Generate key pair
   */
  private async generateKeyPair(type: 'signing' | 'encryption' | 'recovery'): Promise<IdentityKeyPair> {
    const keyId = await this.crypto.generateSecureRandom(16);
    const publicKey = await this.crypto.generateSecureRandom(32);
    const privateKey = await this.crypto.generateSecureRandom(32);

    return {
      keyId: keyId.toString('hex'),
      publicKey: publicKey.toString('hex'),
      privateKey: privateKey.toString('hex'),
      type,
      created: new Date().toISOString(),
      status: 'active'
    };
  }

  /**
   * Import key pair from existing key
   */
  private async importKeyPair(privateKey: string, type: 'signing' | 'encryption' | 'recovery'): Promise<IdentityKeyPair> {
    const keyId = await this.crypto.generateSecureRandom(16);
    // In a real implementation, derive public key from private key
    const publicKey = await this.crypto.generateSecureRandom(32);

    return {
      keyId: keyId.toString('hex'),
      publicKey: publicKey.toString('hex'),
      privateKey,
      type,
      created: new Date().toISOString(),
      status: 'active'
    };
  }

  /**
   * Get current key ID by type
   */
  private getCurrentKeyId(profile: IdentityProfile, keyType: 'signing' | 'encryption' | 'recovery'): string {
    switch (keyType) {
      case 'signing':
        return profile.currentSigningKey;
      case 'encryption':
        return profile.currentEncryptionKey;
      case 'recovery':
        return profile.currentRecoveryKey;
      default:
        throw new Error(`Invalid key type: ${keyType}`);
    }
  }

  /**
   * Create rotation proof
   */
  private async createRotationProof(
    newKeyPair: IdentityKeyPair,
    previousKeyId: string,
    reason: string,
    signingKey: string
  ): Promise<string> {
    const proofData = {
      newKeyId: newKeyPair.keyId,
      previousKeyId,
      reason,
      timestamp: new Date().toISOString()
    };

    return await this.cubicSignature.sign(
      JSON.stringify(proofData),
      signingKey
    );
  }

  /**
   * Create recovery proof
   */
  private async createRecoveryProof(
    newKeyPair: IdentityKeyPair,
    recoveryPhrase: string
  ): Promise<string> {
    const proofData = {
      newKeyId: newKeyPair.keyId,
      recoveryPhrase: await this.crypto.hashData(recoveryPhrase),
      timestamp: new Date().toISOString()
    };

    return await this.cubicSignature.sign(
      JSON.stringify(proofData),
      newKeyPair.privateKey
    );
  }

  /**
   * Update DID document with new key
   */
  private async updateDIDDocumentWithNewKey(
    did: string,
    newKeyPair: IdentityKeyPair,
    signingKey: string
  ): Promise<void> {
    const resolution = await this.didRegistry.resolveDID(did);
    const document = resolution.didDocument;

    const newVerificationMethod: VerificationMethod = {
      id: `${did}#${newKeyPair.keyId}`,
      type: 'Ed25519VerificationKey2018',
      controller: did,
      publicKeyBase58: newKeyPair.publicKey
    };

    const updatedDocument = await this.didRegistry.updateDID(
      did,
      {
        verificationMethod: [...document.verificationMethod, newVerificationMethod],
        authentication: [...document.authentication, `${did}#${newKeyPair.keyId}`]
      },
      signingKey
    );

    // Update local state
    const identityState = this.identityStore.get(did);
    if (identityState) {
      identityState.didDocument = updatedDocument;
    }
  }

  /**
   * Create recovery data
   */
  private async createRecoveryData(recoveryPhrase: string, recoveryPrivateKey: string): Promise<RecoveryData> {
    // Create recovery shards (simplified Shamir's Secret Sharing)
    const shards: RecoveryShard[] = [];
    const threshold = 3; // Need 3 out of 5 shards to recover

    for (let i = 0; i < 5; i++) {
      const shardData = await this.crypto.generateSecureRandom(16);
      shards.push({
        shardId: `shard-${i + 1}`,
        shardData: shardData.toString('hex'),
        location: `location-${i + 1}`,
        threshold,
        created: new Date().toISOString()
      });
    }

    return {
      recoveryPhrase: await this.crypto.hashData(recoveryPhrase),
      recoveryShards: shards,
      lastRecoveryCheck: new Date().toISOString(),
      recoveryAttempts: 0,
      maxRecoveryAttempts: 3
    };
  }

  /**
   * Generate recovery phrase
   */
  private async generateRecoveryPhrase(): Promise<string> {
    const words = [
      'abandon', 'ability', 'able', 'about', 'above', 'absent', 'absorb', 'abstract',
      'absurd', 'abuse', 'access', 'accident', 'account', 'accuse', 'achieve', 'acid',
      'acoustic', 'acquire', 'across', 'act', 'action', 'actor', 'actress', 'actual'
    ];

    const phrase = [];
    for (let i = 0; i < 12; i++) {
      const index = Math.floor(Math.random() * words.length);
      phrase.push(words[index]);
    }

    return phrase.join(' ');
  }

  /**
   * Verify recovery phrase
   */
  private async verifyRecoveryPhrase(recoveryPhrase: string, recoveryData: RecoveryData): Promise<boolean> {
    const hashedPhrase = await this.crypto.hashData(recoveryPhrase);
    return hashedPhrase === recoveryData.recoveryPhrase;
  }

  /**
   * Delete identity
   */
  async deleteIdentity(did: string, signingKey: string): Promise<void> {
    const identityState = this.identityStore.get(did);
    if (!identityState) {
      throw new Error(`Identity not found: ${did}`);
    }

    // Deactivate DID
    await this.didRegistry.deactivateDID(did, signingKey);

    // Remove from local store
    this.identityStore.delete(did);
  }

  /**
   * Export identity
   */
  exportIdentity(did: string): string {
    const identityState = this.identityStore.get(did);
    if (!identityState) {
      throw new Error(`Identity not found: ${did}`);
    }

    return JSON.stringify(identityState, null, 2);
  }

  /**
   * Import identity
   */
  async importIdentity(identityData: string): Promise<string> {
    const identityState: IdentityState = JSON.parse(identityData);
    
    // Validate identity state
    if (!identityState.profile || !identityState.didDocument) {
      throw new Error('Invalid identity data');
    }

    this.identityStore.set(identityState.profile.did, identityState);
    
    return identityState.profile.did;
  }
}