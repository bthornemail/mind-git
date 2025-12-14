/**
 * Comprehensive Identity Testing Suite
 * 
 * Tests all Phase 2.2 identity management functionality including
 * DID operations, sovereign identity, multiverse addressing, verification,
 * and MindGit integration.
 */

import { 
  DIDRegistry, 
  DIDDocumentManager, 
  MindGitDIDMethod 
} from '../../identity/did-core';
import { 
  SovereignIdentityManager 
} from '../../identity/sovereign-identity';
import { 
  MultiverseAddressManager 
} from '../../identity/multiverse-addressing';
import { 
  CredentialManager,
  AttestationManager,
  IdentityVerifier
} from '../../identity/identity-verification';
import { 
  IdentityMindGit 
} from '../../identity/identity-mindgit-integration';
import { ProductionCrypto } from '../../core/cryptography/production-crypto';

describe('Phase 2.2 - Sovereign Identity Management', () => {
  let didRegistry: DIDRegistry;
  let identityManager: SovereignIdentityManager;
  let addressManager: MultiverseAddressManager;
  let credentialManager: CredentialManager;
  let attestationManager: AttestationManager;
  let identityVerifier: IdentityVerifier;
  let identityMindGit: IdentityMindGit;
  let crypto: ProductionCrypto;

  beforeEach(() => {
    didRegistry = new DIDRegistry();
    identityManager = new SovereignIdentityManager();
    addressManager = new MultiverseAddressManager();
    credentialManager = new CredentialManager();
    attestationManager = new AttestationManager();
    identityVerifier = new IdentityVerifier();
    identityMindGit = new IdentityMindGit();
    crypto = new ProductionCrypto();
  });

  describe('DID Core System', () => {
    test('should generate valid DID format', () => {
      const identityKey = 'test-identity-key';
      const namespace = 'test-namespace';
      
      const did = MindGitDIDMethod.generateDID(identityKey, namespace);
      
      expect(did).toBe('did:mindgit:test-namespace:test-identity-key');
      expect(MindGitDIDMethod.validateDID(did)).toBe(true);
    });

    test('should extract method-specific ID from DID', () => {
      const did = 'did:mindgit:namespace:identity-key';
      const methodSpecificId = MindGitDIDMethod.extractMethodSpecificId(did);
      
      expect(methodSpecificId).toBe('namespace:identity-key');
    });

    test('should parse method-specific ID', () => {
      const methodSpecificId = 'namespace:identity-key';
      const parsed = MindGitDIDMethod.parseMethodSpecificId(methodSpecificId);
      
      expect(parsed.namespace).toBe('namespace');
      expect(parsed.identityKey).toBe('identity-key');
    });

    test('should register and resolve DID', async () => {
      const { did, document } = await didRegistry.registerDID(
        'test-identity-key',
        'test-public-key',
        'test-namespace'
      );

      expect(did).toMatch(/^did:mindgit:/);
      expect(document.id).toBe(did);
      expect(document.verificationMethod).toHaveLength(1);

      const resolution = await didRegistry.resolveDID(did);
      expect(resolution.didDocument.id).toBe(did);
    });

    test('should update DID document', async () => {
      const { did, document } = await didRegistry.registerDID(
        'test-identity-key',
        'test-public-key'
      );

      const updatedDocument = await didRegistry.updateDID(
        did,
        { 
          service: [{
            id: `${did}#service-1`,
            type: 'Repository',
            serviceEndpoint: 'https://example.com/repo'
          }]
        },
        'test-signing-key'
      );

      expect(updatedDocument.service).toHaveLength(1);
      expect(updatedDocument.updated).not.toBe(document.updated);
    });

    test('should deactivate DID', async () => {
      const { did } = await didRegistry.registerDID(
        'test-identity-key',
        'test-public-key'
      );

      const deactivatedDocument = await didRegistry.deactivateDID(
        did,
        'test-signing-key'
      );

      expect(deactivatedDocument.verificationMethod).toHaveLength(0);
      expect(deactivatedDocument.authentication).toHaveLength(0);
    });
  });

  describe('Sovereign Identity Management', () => {
    test('should create new sovereign identity', async () => {
      const { did, profile, document } = await identityManager.createIdentity(
        'Test Identity',
        'test-namespace'
      );

      expect(did).toMatch(/^did:mindgit:/);
      expect(profile.did).toBe(did);
      expect(profile.metadata.name).toBe('Test Identity');
      expect(profile.keyPairs).toHaveLength(3); // signing, encryption, recovery
      expect(document.id).toBe(did);
    });

    test('should rotate identity key', async () => {
      const { did, profile } = await identityManager.createIdentity(
        'Test Identity'
      );

      const originalSigningKey = profile.currentSigningKey;
      
      const updatedProfile = await identityManager.rotateKey(
        did,
        'signing',
        'Key rotation test',
        profile.keyPairs.find(kp => kp.keyId === originalSigningKey)?.privateKey!
      );

      expect(updatedProfile.currentSigningKey).not.toBe(originalSigningKey);
      expect(updatedProfile.keyRotationHistory).toHaveLength(1);
    });

    test('should recover identity with recovery phrase', async () => {
      const recoveryPhrase = 'test recovery phrase twelve words';
      const { did, profile } = await identityManager.createIdentity(
        'Test Identity',
        'default',
        recoveryPhrase
      );

      const recoveredProfile = await identityManager.recoverIdentity(
        did,
        recoveryPhrase
      );

      expect(recoveredProfile.keyRotationHistory).toHaveLength(1);
      expect(recoveredProfile.recoveryData.recoveryAttempts).toBe(1);
    });

    test('should fail recovery with invalid phrase', async () => {
      const { did } = await identityManager.createIdentity('Test Identity');

      await expect(
        identityManager.recoverIdentity(did, 'invalid phrase')
      ).rejects.toThrow('Invalid recovery phrase');
    });

    test('should export and import identity', async () => {
      const { did } = await identityManager.createIdentity('Test Identity');
      
      const exportedData = identityManager.exportIdentity(did);
      expect(exportedData).toContain(did);

      const importedDid = await identityManager.importIdentity(exportedData);
      expect(importedDid).toBe(did);
    });
  });

  describe('Multiverse Addressing System', () => {
    test('should create new universe', async () => {
      const universe = await addressManager.createUniverse(
        'Test Universe',
        'A test universe for testing',
        2 // Complex plane
      );

      expect(universe.name).toBe('Test Universe');
      expect(universe.dimension).toBe(2);
      expect(universe.physicsConstants.speedOfLight).toBe(299792458);
    });

    test('should reject invalid dimensions', async () => {
      await expect(
        addressManager.createUniverse('Invalid', 'Invalid dimension', 3)
      ).rejects.toThrow('Dimension must be 1, 2, 4, or 8');
    });

    test('should create new realm', async () => {
      const universe = await addressManager.createUniverse('Test', 'Test', 2);
      
      const realm = await addressManager.createRealm(
        universe.universeId,
        'Test Realm',
        {
          min: { x: 0, y: 0, z: 0, dimension: 2 },
          max: { x: 100, y: 100, z: 0, dimension: 2 }
        },
        {
          type: 'democracy',
          rules: [],
          leaders: []
        }
      );

      expect(realm.name).toBe('Test Realm');
      expect(realm.universeId).toBe(universe.universeId);
    });

    test('should create multiverse address', async () => {
      const { did } = await identityManager.createIdentity('Test Identity');
      const universe = await addressManager.createUniverse('Test', 'Test', 2);
      const realm = await addressManager.createRealm(
        universe.universeId,
        'Test Realm',
        {
          min: { x: 0, y: 0, z: 0, dimension: 2 },
          max: { x: 100, y: 100, z: 0, dimension: 2 }
        },
        { type: 'democracy', rules: [], leaders: [] }
      );

      const address = await addressManager.createAddress(
        did,
        universe.universeId,
        realm.realmId,
        { x: 50, y: 50, z: 0, dimension: 2 }
      );

      expect(address.identityDid).toBe(did);
      expect(address.universeId).toBe(universe.universeId);
      expect(address.realmId).toBe(realm.realmId);
      expect(address.coordinate.x).toBe(50);
    });

    test('should calculate distance between addresses', async () => {
      const { did: did1 } = await identityManager.createIdentity('Identity 1');
      const { did: did2 } = await identityManager.createIdentity('Identity 2');
      const universe = await addressManager.createUniverse('Test', 'Test', 2);
      const realm = await addressManager.createRealm(
        universe.universeId,
        'Test Realm',
        {
          min: { x: 0, y: 0, z: 0, dimension: 2 },
          max: { x: 100, y: 100, z: 0, dimension: 2 }
        },
        { type: 'democracy', rules: [], leaders: [] }
      );

      const address1 = await addressManager.createAddress(
        did1,
        universe.universeId,
        realm.realmId,
        { x: 0, y: 0, z: 0, dimension: 2 }
      );

      const address2 = await addressManager.createAddress(
        did2,
        universe.universeId,
        realm.realmId,
        { x: 3, y: 4, z: 0, dimension: 2 }
      );

      const distance = addressManager.calculateDistance(address1, address2);
      expect(distance).toBe(5); // 3-4-5 triangle
    });

    test('should find route between addresses', async () => {
      const { did: sourceDid } = await identityManager.createIdentity('Source');
      const { did: destDid } = await identityManager.createIdentity('Destination');
      const universe = await addressManager.createUniverse('Test', 'Test', 2);
      const realm = await addressManager.createRealm(
        universe.universeId,
        'Test Realm',
        {
          min: { x: 0, y: 0, z: 0, dimension: 2 },
          max: { x: 100, y: 100, z: 0, dimension: 2 }
        },
        { type: 'democracy', rules: [], leaders: [] }
      );

      const sourceAddress = await addressManager.createAddress(
        sourceDid,
        universe.universeId,
        realm.realmId,
        { x: 0, y: 0, z: 0, dimension: 2 }
      );

      const destAddress = await addressManager.createAddress(
        destDid,
        universe.universeId,
        realm.realmId,
        { x: 10, y: 10, z: 0, dimension: 2 }
      );

      const route = await addressManager.findRoute(sourceAddress, destAddress);
      expect(route).toHaveLength(2); // Source and destination
      expect(route[0].identityDid).toBe(sourceDid);
      expect(route[1].identityDid).toBe(destDid);
    });
  });

  describe('Identity Verification and Attestation', () => {
    test('should create verifiable credential', async () => {
      const { did: issuerDid } = await identityManager.createIdentity('Issuer');
      const { did: subjectDid } = await identityManager.createIdentity('Subject');

      const credential = await credentialManager.createCredential(
        issuerDid,
        subjectDid,
        { name: 'John Doe', age: 30 },
        ['NameCredential'],
        'test-signing-key'
      );

      expect(credential.issuer).toBe(issuerDid);
      expect(credential.credentialSubject.id).toBe(subjectDid);
      expect(credential.credentialSubject.name).toBe('John Doe');
      expect(credential.type).toContain('NameCredential');
    });

    test('should verify credential', async () => {
      const { did: issuerDid } = await identityManager.createIdentity('Issuer');
      const { did: subjectDid } = await identityManager.createIdentity('Subject');

      const credential = await credentialManager.createCredential(
        issuerDid,
        subjectDid,
        { name: 'John Doe' },
        ['NameCredential'],
        'test-signing-key'
      );

      const verification = await credentialManager.verifyCredential(
        credential,
        'test-public-key'
      );

      expect(verification.valid).toBe(true);
      expect(verification.expired).toBe(false);
      expect(verification.revoked).toBe(false);
    });

    test('should create attestation', async () => {
      const { did: attestorDid } = await identityManager.createIdentity('Attestor');
      const { did: subjectDid } = await identityManager.createIdentity('Subject');

      const claims = [
        {
          claimId: 'claim-1',
          type: 'identity_verified',
          value: true,
          confidence: 0.95,
          verificationStatus: 'verified' as const
        }
      ];

      const attestation = await attestationManager.createAttestation(
        attestorDid,
        subjectDid,
        claims,
        'high',
        'test-signing-key'
      );

      expect(attestation.attestor).toBe(attestorDid);
      expect(attestation.subject).toBe(subjectDid);
      expect(attestation.claims).toHaveLength(1);
      expect(attestation.trustLevel).toBe('high');
    });

    test('should process verification request', async () => {
      const { did: subjectDid } = await identityManager.createIdentity('Subject');
      const { did: requesterDid } = await identityManager.createIdentity('Requester');

      const verificationRequest = await identityVerifier.createVerificationRequest(
        requesterDid,
        subjectDid,
        ['identity', 'reputation'],
        'standard'
      );

      const response = await identityVerifier.processVerificationRequest(verificationRequest);

      expect(response.requestId).toBe(verificationRequest.requestId);
      expect(['approved', 'rejected', 'pending', 'expired']).toContain(response.status);
      expect(response.trustScore).toBeGreaterThanOrEqual(0);
      expect(response.trustScore).toBeLessThanOrEqual(1);
    });
  });

  describe('Identity-MindGit Integration', () => {
    test('should initialize identity repository', async () => {
      const { did: ownerDid } = await identityManager.createIdentity('Owner');

      const repository = await identityMindGit.initializeIdentityRepository(
        'test-repo',
        ownerDid,
        {
          description: 'Test repository with identity integration',
          governance: {
            type: 'meritocracy',
            rules: []
          }
        }
      );

      expect(repository.name).toBe('test-repo');
      expect(repository.ownerDid).toBe(ownerDid);
      expect(repository.contributors.has(ownerDid)).toBe(true);
      expect(repository.branches.has('main')).toBe(true);
    });

    test('should create identity-verified commit', async () => {
      const { did: authorDid } = await identityManager.createIdentity('Author');
      
      const repository = await identityMindGit.initializeIdentityRepository(
        'test-repo',
        authorDid
      );

      const identityCommit = await identityMindGit.createIdentityCommit(
        repository.repositoryId,
        'main',
        authorDid,
        'Initial commit with identity verification',
        [
          { path: 'README.md', content: '# Test Repository' }
        ]
      );

      expect(identityCommit.authorDid).toBe(authorDid);
      expect(identityCommit.commitHash).toBeTruthy();
      expect(identityCommit.identityProof).toBeTruthy();
      expect(['verified', 'pending', 'rejected', 'expired']).toContain(identityCommit.verificationStatus);
    });

    test('should add contributor to repository', async () => {
      const { did: ownerDid } = await identityManager.createIdentity('Owner');
      const { did: contributorDid } = await identityManager.createIdentity('Contributor');

      const repository = await identityMindGit.initializeIdentityRepository(
        'test-repo',
        ownerDid
      );

      await identityMindGit.addContributor(
        repository.repositoryId,
        contributorDid,
        'contributor',
        ownerDid
      );

      const updatedRepository = identityMindGit.getRepository(repository.repositoryId);
      expect(updatedRepository?.contributors.has(contributorDid)).toBe(true);
      
      const contributor = updatedRepository?.contributors.get(contributorDid);
      expect(contributor?.role).toBe('contributor');
    });

    test('should create identity-verified merge', async () => {
      const { did: authorDid } = await identityManager.createIdentity('Author');
      
      const repository = await identityMindGit.initializeIdentityRepository(
        'test-repo',
        authorDid
      );

      // Create feature branch and commit
      await identityMindGit.createIdentityCommit(
        repository.repositoryId,
        'feature',
        authorDid,
        'Feature commit',
        [{ path: 'feature.txt', content: 'Feature content' }]
      );

      // Merge to main
      const mergeCommit = await identityMindGit.createIdentityMerge(
        repository.repositoryId,
        'feature',
        'main',
        authorDid,
        'Merge feature branch'
      );

      expect(mergeCommit.authorDid).toBe(authorDid);
      expect(mergeCommit.metadata.verificationLevel).toBe('enhanced');
    });

    test('should sync repository across multiverse', async () => {
      const { did: ownerDid } = await identityManager.createIdentity('Owner');
      
      const repository = await identityMindGit.initializeIdentityRepository(
        'test-repo',
        ownerDid,
        {
          metadata: {
            multiverse: {
              primaryUniverse: 'Prime Reality',
              supportedUniverses: ['Prime Reality', 'Complex Plane'],
              syncEnabled: true
            }
          }
        }
      );

      await identityMindGit.syncAcrossMultiverse(
        repository.repositoryId,
        ['Complex Plane']
      );

      // Verify addresses were created for contributors
      const addresses = addressManager.getAddressesByIdentity(ownerDid);
      const hasComplexPlaneAddress = addresses.some(
        addr => addr.universeId === 'Complex Plane'
      );
      expect(hasComplexPlaneAddress).toBe(true);
    });

    test('should list repositories for identity', async () => {
      const { did: identityDid } = await identityManager.createIdentity('Developer');

      const repo1 = await identityMindGit.initializeIdentityRepository(
        'repo1',
        identityDid
      );

      const repo2 = await identityMindGit.initializeIdentityRepository(
        'repo2',
        identityDid
      );

      const repositories = identityMindGit.listRepositoriesForIdentity(identityDid);
      
      expect(repositories).toHaveLength(2);
      expect(repositories.map(r => r.repositoryId)).toContain(repo1.repositoryId);
      expect(repositories.map(r => r.repositoryId)).toContain(repo2.repositoryId);
    });
  });

  describe('Integration Tests', () => {
    test('should handle complete identity workflow', async () => {
      // 1. Create identities
      const { did: ownerDid } = await identityManager.createIdentity('Repository Owner');
      const { did: contributorDid } = await identityManager.createIdentity('Contributor');
      const { did: verifierDid } = await identityManager.createIdentity('Verifier');

      // 2. Create credentials for contributor
      const credential = await credentialManager.createCredential(
        verifierDid,
        contributorDid,
        { skill: 'TypeScript', experience: '5 years' },
        ['SkillCredential'],
        'test-signing-key'
      );

      // 3. Create attestation for contributor
      const attestation = await attestationManager.createAttestation(
        verifierDid,
        contributorDid,
        [
          {
            claimId: 'skill-claim',
            type: 'skill_verified',
            value: 'TypeScript',
            confidence: 0.9,
            verificationStatus: 'verified' as const
          }
        ],
        'high',
        'test-signing-key'
      );

      // 4. Initialize repository
      const repository = await identityMindGit.initializeIdentityRepository(
        'typescript-project',
        ownerDid,
        {
          governance: {
            type: 'meritocracy',
            rules: []
          }
        }
      );

      // 5. Add contributor
      await identityMindGit.addContributor(
        repository.repositoryId,
        contributorDid,
        'contributor',
        ownerDid
      );

      // 6. Create multiverse addresses
      const universe = await addressManager.createUniverse('Dev Universe', 'Development', 2);
      const realm = await addressManager.createRealm(
        universe.universeId,
        'Dev Realm',
        {
          min: { x: 0, y: 0, z: 0, dimension: 2 },
          max: { x: 100, y: 100, z: 0, dimension: 2 }
        },
        { type: 'democracy', rules: [], leaders: [] }
      );

      const ownerAddress = await addressManager.createAddress(
        ownerDid,
        universe.universeId,
        realm.realmId,
        { x: 10, y: 10, z: 0, dimension: 2 }
      );

      const contributorAddress = await addressManager.createAddress(
        contributorDid,
        universe.universeId,
        realm.realmId,
        { x: 20, y: 20, z: 0, dimension: 2 }
      );

      // 7. Create identity-verified commits
      const ownerCommit = await identityMindGit.createIdentityCommit(
        repository.repositoryId,
        'main',
        ownerDid,
        'Initial project setup',
        [
          { path: 'package.json', content: '{"name": "typescript-project"}' },
          { path: 'README.md', content: '# TypeScript Project' }
        ],
        {
          address: {
            universeId: universe.universeId,
            realmId: realm.realmId,
            coordinate: ownerAddress.coordinate
          }
        }
      );

      const contributorCommit = await identityMindGit.createIdentityCommit(
        repository.repositoryId,
        'feature',
        contributorDid,
        'Add TypeScript feature',
        [
          { path: 'src/index.ts', content: 'export function hello() { return "Hello"; }' }
        ],
        {
          credentials: ['cred-1'],
          address: {
            universeId: universe.universeId,
            realmId: realm.realmId,
            coordinate: contributorAddress.coordinate
          }
        }
      );

      // 8. Verify all components
      expect(repository.ownerDid).toBe(ownerDid);
      expect(repository.contributors.has(contributorDid)).toBe(true);
      expect(ownerCommit.authorDid).toBe(ownerDid);
      expect(contributorCommit.authorDid).toBe(contributorDid);
      expect(ownerAddress.identityDid).toBe(ownerDid);
      expect(contributorAddress.identityDid).toBe(contributorDid);

      // 9. Calculate distance and route
      const distance = addressManager.calculateDistance(ownerAddress, contributorAddress);
      expect(distance).toBeGreaterThan(0);

      const route = await addressManager.findRoute(ownerAddress, contributorAddress);
      expect(route.length).toBeGreaterThanOrEqual(2);

      // 10. Sync across multiverse
      await identityMindGit.syncAcrossMultiverse(
        repository.repositoryId,
        ['Complex Plane']
      );

      // Verify final state
      const finalRepository = identityMindGit.getRepository(repository.repositoryId);
      expect(finalRepository?.contributors.size).toBe(2);
      
      const ownerAddresses = addressManager.getAddressesByIdentity(ownerDid);
      const contributorAddresses = addressManager.getAddressesByIdentity(contributorDid);
      expect(ownerAddresses.length).toBeGreaterThanOrEqual(2); // Original + synced
      expect(contributorAddresses.length).toBeGreaterThanOrEqual(2); // Original + synced
    });
  });

  describe('Performance Tests', () => {
    test('should handle multiple identity operations efficiently', async () => {
      const startTime = Date.now();
      
      // Create 10 identities
      const identities = [];
      for (let i = 0; i < 10; i++) {
        const { did } = await identityManager.createIdentity(`Identity ${i}`);
        identities.push(did);
      }
      
      const creationTime = Date.now() - startTime;
      expect(creationTime).toBeLessThan(5000); // Should complete within 5 seconds

      // Create addresses for all identities
      const addressStartTime = Date.now();
      const universe = await addressManager.createUniverse('Perf Test', 'Performance', 2);
      const realm = await addressManager.createRealm(
        universe.universeId,
        'Perf Realm',
        {
          min: { x: 0, y: 0, z: 0, dimension: 2 },
          max: { x: 1000, y: 1000, z: 0, dimension: 2 }
        },
        { type: 'democracy', rules: [], leaders: [] }
      );

      for (let i = 0; i < identities.length; i++) {
        await addressManager.createAddress(
          identities[i],
          universe.universeId,
          realm.realmId,
          { x: i * 10, y: i * 10, z: 0, dimension: 2 }
        );
      }
      
      const addressTime = Date.now() - addressStartTime;
      expect(addressTime).toBeLessThan(3000); // Should complete within 3 seconds

      // Test route finding performance
      const routeStartTime = Date.now();
      const addresses = addressManager.getAddressesByUniverse(universe.universeId);
      
      for (let i = 0; i < addresses.length - 1; i++) {
        await addressManager.findRoute(addresses[i], addresses[i + 1]);
      }
      
      const routeTime = Date.now() - routeStartTime;
      expect(routeTime).toBeLessThan(2000); // Should complete within 2 seconds
    });
  });
});