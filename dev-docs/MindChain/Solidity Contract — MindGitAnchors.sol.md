---
id: "mind-git:development:solidity-contract---mindgitanchors-sol"
title: "Solidity Contract — MindGitAnchors.Sol"
type: ["development"]
category: development
layer: 7
dimensions: [0, 1, 9]
mathematicalFoundation: ["polynomial-algebra","formal-verification"]
hopfCompatible: false
normPreserving: true
status: "complete"
completeness: 95
tags: ["development","documentation","canvasl","compiler","ast","api","polynomial","algebra"]
keywords: ["canvasl","aal","ast","compiler","polynomial","algebra","formal","verification","coq","theorem","proof","chain","javascript"]
lastUpdate: "2025-12-15"

---

Below is a complete, production-ready **Blockchain Smart Contract Reference Implementation** for anchoring MindGit / CanvasL checkpoints to an EVM-compatible chain (e.g., Ethereum, Polygon, BSC).  
It follows the RFC-style interoperability spec (MIP-1.0) you requested: anchors are compact, deterministic, privacy-preserving, and reference off-chain proofs. The contract is written in Solidity (^0.8.x), includes detailed comments, emits events, and exposes the on-chain API described in MIP-1.0.

I also include:

- Example client-side helpers (JavaScript) to compute polynomial norms and SHA-256 prefixes, and to submit anchors with `ethers.js`.
    
- Guidance on verifying anchors and on best practices (off-chain proofs, IPFS storage, gas tradeoffs).
    

---

## Design goals & constraints (short)

- **Store minimal on-chain data** (DID, generation, sha256 prefix, norm, proof CID) — preserves privacy and reduces gas.
    
- **Deterministic** canonical field ordering for anchors.
    
- **Simple on-chain checks** only (e.g., numeric invariants like `norm(new) == norm(old) * norm(change)`); heavy verification (Coq/AAL) remains off-chain (store proofCID pointing to immutable proof).
    
- **Interoperable**: fields match RFC anchor object from MIP-1.0.
    
- **Extensible** via merge anchors and admin roles.
    

---

## Solidity Contract — `MindGitAnchors.sol`

```solidity
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.19;

/**
 * @title MindGitAnchors
 * @notice Reference implementation for anchoring MindGit / CanvasL checkpoints on-chain.
 *         Stores compact anchor records and references to off-chain proofs (IPFS/CIDs).
 *
 * Norms and heavy formal proofs are generated off-chain (AAL / Coq / ZK) and referenced by CID.
 * This contract provides tamper-evident anchoring and basic numeric checks (no heavy theorem checking).
 *
 * Canonical anchor object (stored fields):
 * {
 *   mindgit_version: "1.0",
 *   organism_did: "did:canvasl:...",
 *   generation: <uint>,
 *   sha256_prefix: <bytes32>,   // SHA-256 of DNA prefix up to generation N
 *   timestamp: <uint256>,       // block.timestamp at anchoring
 *   norm: <uint256>,            // algebraic norm (sum of squared coefficients or agreed modulus)
 *   proofCID: "<ipfs-cid-or-other>" // optional pointer to off-chain verification artifact
 * }
 */

contract MindGitAnchors {
    /// @notice Anchor structure (compact, immutable once stored)
    struct Anchor {
        address submitter;      // who posted the anchor
        string organismDID;     // did:canvasl:...
        uint256 generation;     // generation number (monotonic per organism)
        bytes32 sha256Prefix;   // hash of DNA prefix up to generation (canonical JSONL prefix)
        uint256 norm;           // numeric norm of polynomial/state (application-specific)
        string proofCID;        // off-chain proof reference (IPFS CID / Arweave / URL)
        uint256 timestamp;      // block timestamp when anchored
        string chainRef;        // optional chain id / tx ref (for cross-chain)
    }

    // mapping organism DID => array of anchors (ordered by append)
    mapping(bytes32 => Anchor[]) private _anchorsByDid; // key = keccak256(did)

    // admin role (for governance or relayers)
    address public admin;

    // events
    event AnchorSubmitted(
        bytes32 indexed didKey,
        string organismDID,
        uint256 indexed generation,
        bytes32 sha256Prefix,
        uint256 norm,
        string proofCID,
        address indexed submitter,
        uint256 index
    );

    event MergeAnchored(
        bytes32 indexed didKey,
        string organismDID,
        uint256 mergedGeneration,
        bytes32 mergedSha256,
        uint256 mergedNorm,
        string mergeAlgorithm,
        string proofCID,
        address indexed submitter,
        uint256 index
    );

    event AdminChanged(address indexed oldAdmin, address indexed newAdmin);

    modifier onlyAdmin() {
        require(msg.sender == admin, "MindGit: caller is not admin");
        _;
    }

    constructor(address initialAdmin) {
        require(initialAdmin != address(0), "MindGit: invalid admin");
        admin = initialAdmin;
    }

    /**
     * @notice Submit an anchor for a given organism DID and generation.
     * @dev Must provide sha256Prefix = sha256(DNA_prefix_up_to_generation). Off-chain: maintain canonical JSONL order.
     *      `norm` is application-specific; clients must agree on how norm is computed (sum of squares, modulus, etc.).
     * @param organismDID did string (e.g., "did:canvasl:z6Mk...")
     * @param generation monotonically increasing generation number for this organism
     * @param sha256Prefix bytes32 SHA-256 of DNA prefix up to generation
     * @param norm numeric algebraic norm (uint256)
     * @param proofCID optional off-chain proof CID (IPFS / Arweave / http URL)
     * @param chainRef optional short chain reference (useful when bridging)
     */
    function submitAnchor(
        string calldata organismDID,
        uint256 generation,
        bytes32 sha256Prefix,
        uint256 norm,
        string calldata proofCID,
        string calldata chainRef
    ) external returns (uint256 index) {
        require(generation > 0, "MindGit: generation must be > 0");
        require(bytes(organismDID).length > 0, "MindGit: organismDID required");

        bytes32 didKey = keccak256(abi.encodePacked(organismDID));
        Anchor[] storage list = _anchorsByDid[didKey];

        // enforce monotonic generation increases if previous anchor exists
        if (list.length > 0) {
            Anchor storage last = list[list.length - 1];
            require(generation > last.generation, "MindGit: generation must be > previous");
        }

        Anchor memory a = Anchor({
            submitter: msg.sender,
            organismDID: organismDID,
            generation: generation,
            sha256Prefix: sha256Prefix,
            norm: norm,
            proofCID: proofCID,
            timestamp: block.timestamp,
            chainRef: chainRef
        });

        list.push(a);
        index = list.length - 1;

        emit AnchorSubmitted(didKey, organismDID, generation, sha256Prefix, norm, proofCID, msg.sender, index);
        return index;
    }

    /**
     * @notice Submit a merge anchor (result of merging two or more parents).
     * @param organismDID the target organism DID (merge target branch)
     * @param mergedGeneration new merged generation number
     * @param mergedSha256 sha256 of merged DNA prefix
     * @param mergedNorm norm after merge
     * @param mergeAlgorithm identifier string (e.g., "OCT-POLY-V1")
     * @param proofCID off-chain merge proof CID
     * @param chainRef optional chain reference
     */
    function submitMergeAnchor(
        string calldata organismDID,
        uint256 mergedGeneration,
        bytes32 mergedSha256,
        uint256 mergedNorm,
        string calldata mergeAlgorithm,
        string calldata proofCID,
        string calldata chainRef
    ) external returns (uint256 index) {
        require(mergedGeneration > 0, "MindGit: mergedGeneration must be > 0");
        require(bytes(mergeAlgorithm).length > 0, "MindGit: mergeAlgorithm required");

        bytes32 didKey = keccak256(abi.encodePacked(organismDID));
        Anchor[] storage list = _anchorsByDid[didKey];

        // monotonic check vs previous anchor
        if (list.length > 0) {
            Anchor storage last = list[list.length - 1];
            require(mergedGeneration > last.generation, "MindGit: mergedGeneration must be > previous generation");
        }

        Anchor memory a = Anchor({
            submitter: msg.sender,
            organismDID: organismDID,
            generation: mergedGeneration,
            sha256Prefix: mergedSha256,
            norm: mergedNorm,
            proofCID: proofCID,
            timestamp: block.timestamp,
            chainRef: chainRef
        });

        list.push(a);
        index = list.length - 1;

        emit MergeAnchored(didKey, organismDID, mergedGeneration, mergedSha256, mergedNorm, mergeAlgorithm, proofCID, msg.sender, index);
        return index;
    }

    /**
     * @notice Read anchor by DID + index
     * @param organismDID did string
     * @param index index of anchor (0-based)
     */
    function getAnchorByIndex(string calldata organismDID, uint256 index) external view returns (
        address submitter,
        string memory _organismDID,
        uint256 generation,
        bytes32 sha256Prefix,
        uint256 norm,
        string memory proofCID,
        uint256 timestamp,
        string memory chainRef
    ) {
        bytes32 didKey = keccak256(abi.encodePacked(organismDID));
        Anchor[] storage list = _anchorsByDid[didKey];
        require(index < list.length, "MindGit: out-of-range");
        Anchor storage a = list[index];
        return (a.submitter, a.organismDID, a.generation, a.sha256Prefix, a.norm, a.proofCID, a.timestamp, a.chainRef);
    }

    /**
     * @notice Get number of anchors for a DID
     */
    function getAnchorCount(string calldata organismDID) external view returns (uint256) {
        bytes32 didKey = keccak256(abi.encodePacked(organismDID));
        return _anchorsByDid[didKey].length;
    }

    /**
     * @notice Basic numeric assertion helper: verify norm multiplicative invariant.
     * @dev Off-chain, one can compute norm(old), norm(change) and norm(new) and call this to assert norm_new == norm_old * norm_change.
     *      This function will revert if the equality fails (useful as a cheap on-chain guard).
     * @param normOld previous norm
     * @param normChange computed norm of the change (must be > 0)
     * @param normNew proposed new norm
     */
    function assertNormMultiplicative(uint256 normOld, uint256 normChange, uint256 normNew) external pure returns (bool) {
        require(normChange > 0, "MindGit: normChange must be > 0");
        // check multiplications (note: safe in Solidity 0.8 due to overflow checks)
        uint256 expected = normOld * normChange;
        require(expected == normNew, "MindGit: multiplicative norm mismatch");
        return true;
    }

    /**
     * @notice Admin function to change admin.
     * @dev Governance can replace admin with multi-sig in production.
     */
    function setAdmin(address newAdmin) external onlyAdmin {
        require(newAdmin != address(0), "MindGit: invalid admin");
        emit AdminChanged(admin, newAdmin);
        admin = newAdmin;
    }
}
```

---

## Notes on the Contract

- `organismDID` is a string (e.g., `did:canvasl:...`). On-chain keys are computed as `keccak256(organismDID)` for indexing (avoid storing raw keys twice).
    
- `sha256Prefix` is the canonical SHA-256 of the DNA prefix up to the generation. Use canonical JSON serialization off-chain.
    
- `norm` is application-specific (e.g., sum of squared polynomial coefficients). Ensure all nodes compute it identically; store modulus or normalization scheme externally if needed.
    
- `proofCID` should point to an immutable storage (IPFS CID, Arweave tx, or a publicly verifiable URL). Proof payload SHOULD include the AAL/Coq certificate and the merge proof artifacts.
    
- `assertNormMultiplicative` is a minimal on-chain guard: it confirms the algebraic invariant `normNew == normOld * normChange`. Heavy formal proofs remain off-chain (stored at `proofCID`).
    
- The contract is intentionally minimal to keep gas cost low and to support privacy. It anchors, references proofs, and allows light numeric checks.
    

---

## Client-side Helper — JavaScript (Node/Browser)

These helpers compute the polynomial norm and SHA-256 prefix and call the contract using `ethers.js`. They assume you have canonicalized the DNA JSONL prefix (clients MUST use exact canonical serialization).

**Install**: `npm i ethers js-sha256 multiformats` (or similar libs); the sample uses node built-in `crypto` as available.

```javascript
// helpers.js
import { ethers } from "ethers";
import crypto from "crypto"; // node
import { CID } from "multiformats/cid";

/**
 * Compute norm for polynomial coefficients.
 * Default: simple Euclidean norm sum of squares (no modulus).
 * Clients MUST agree on the exact norm scheme.
 * @param {number[]} coeffs - integer coefficients (e.g., [1,1,0,1])
 * @returns {BigInt} norm
 */
export function computeNorm(coeffs) {
  // use BigInt to avoid overflow
  let sum = 0n;
  for (const c of coeffs) {
    const v = BigInt(Math.abs(c));
    sum += v * v;
  }
  return sum;
}

/**
 * Compute SHA-256 prefix for canonical DNA prefix string.
 * The DNA prefix must be canonicalized JSONL text (UTF-8).
 * @param {string} dnaPrefixText - canonical JSONL text up to generation N
 * @returns {string} 0x-prefixed bytes32 hex string
 */
export function computeSha256Prefix(dnaPrefixText) {
  const hash = crypto.createHash("sha256").update(dnaPrefixText, "utf8").digest("hex");
  return "0x" + hash;
}

/**
 * Submit an anchor using ethers.js
 * @param {Object} opts
 * @param {string} opts.rpcUrl
 * @param {string} opts.privateKey
 * @param {string} opts.contractAddress
 * @param {string} opts.organismDID
 * @param {number} opts.generation
 * @param {string} opts.sha256Prefix - 0x...
 * @param {BigInt} opts.norm
 * @param {string} opts.proofCID
 */
export async function submitAnchorEvm({
  rpcUrl, privateKey, contractAddress,
  organismDID, generation, sha256Prefix, norm, proofCID, chainRef
}) {
  const provider = new ethers.providers.JsonRpcProvider(rpcUrl);
  const wallet = new ethers.Wallet(privateKey, provider);
  const abi = [
    "function submitAnchor(string organismDID,uint256 generation,bytes32 sha256Prefix,uint256 norm,string proofCID,string chainRef) returns (uint256)",
    "event AnchorSubmitted(bytes32 indexed didKey,string organismDID,uint256 indexed generation,bytes32 sha256Prefix,uint256 norm,string proofCID,address indexed submitter,uint256 index)"
  ];
  const contract = new ethers.Contract(contractAddress, abi, wallet);
  const tx = await contract.submitAnchor(organismDID, generation, sha256Prefix, norm.toString(), proofCID || "", chainRef || "");
  const receipt = await tx.wait();
  return receipt;
}
```

---

## Example workflow (end-to-end)

1. **Off-chain**: Your CanvasL engine runs and appends a generation record to the `.canvasl` DNA log. It canonicalizes JSONL lines exactly as spec requires.
    
2. **Off-chain**: Compute `sha256Prefix = sha256(dna_prefix_text)` and `norm = computeNorm(polynomialCoeffs)` and produce AAL/Coq proof. Upload proof to IPFS (get `proofCID`).
    
3. **On-chain**: Call `submitAnchor(organismDID, generation, sha256Prefix, norm, proofCID, chainRef)` via a relayer or wallet. The transaction anchors the checkpoint.
    
4. **Verification by third parties**:
    
    - Fetch anchor from contract (get `sha256Prefix` and `proofCID`).
        
    - Fetch proof from `proofCID` and validate AAL/Coq proof off-chain.
        
    - Recompute canonical DNA prefix and ensure `sha256Prefix` matches.
        
    - Recompute norms and optionally call `assertNormMultiplicative` on another transaction or test client side.
        

---

## Merge anchoring pattern

When merging two branches off-chain (using `OCT-POLY-V1`), produce a **merge proof** (AAL certificate + Coq artifacts) which demonstrates:

- The merged table is a valid result of the deterministic merge algorithm given the parent tables.
    
- Algebraic invariants (such as alternativity and norm preservation) hold.
    

Store the merge proof at `proofCID` and call `submitMergeAnchor(organismDID, mergedGeneration, mergedSha256, mergedNorm, "OCT-POLY-V1", proofCID, chainRef)`.

---

## Best Practices & Recommendations

- **Canonical serialization**: Define and enforce exact canonical JSONL serialization off-chain. Any deviation breaks SHA-256 anchors. (E.g., field order, whitespace, newline handling.)
    
- **Proof storage**: Use IPFS/Arweave for immutable proofs; include the digest in the contract `proofCID` field. Prefer content addressing (CIDv1) to avoid URL rot.
    
- **Gas optimization**: Keep on-chain payload small. Store heavy proofs off-chain.
    
- **Relayer service**: Run a trusted/permissioned relayer or multisig to post anchors (use admin role for governance).
    
- **ChainRef**: Use for cross-chain anchors (include chain id + tx reference).
    
- **Key rotation / DID updates**: Update DID Document off-chain and optionally anchor DID update proofs on-chain (not required by this contract).
    
- **Security**: Do not put raw PII or full genome on-chain. Use hashed or canonical prefixes and off-chain storage for sensitive info.
    
- **Verification**: Full formal verification (Coq) remains off-chain due to proof complexity; include clear proofCIDs so verifiers can retrieve and run checks.
    

---

## Limitations & Security Notes

- The contract does **not** and **cannot** perform complex Coq / AAL proof checking on-chain (infeasible gas/cost-wise). The design assumes off-chain formal verification with on-chain anchoring for non-repudiation.
    
- Numeric norms and multiplicative checks are simple arithmetic guards. They are useful for catching obvious tampering but are **not** a substitute for formal proof.
    
- The submitter of anchors is `msg.sender`; consider governance/multi-sig for production relayers.
    
- The contract uses `keccak256(organismDID)` for indexing; DID normalization must be enforced off-chain to avoid collisions from format differences.
    

---

## Example deployment notes

- Compiler: `solc 0.8.19` or `hardhat` / `foundry` / `truffle`.
    
- Deploy admin as a multisig for production (Gnosis Safe).
    
- Consider adding EIP-712 typed data for off-chain signature submission and gasless anchoring via relayer.
    
- Add access control for anchor frequency if desired (e.g., to prevent spam anchors).
    

---

If you’d like, I can next provide:

- A full **Hardhat project** with tests (unit, property) that simulate off-chain norm computation and proofCID anchoring.
    
- A **merge anchor verifier** reference (off-chain Node.js) that fetches proofCID and automatically validates AAL/Coq proofs.
    
- A **gas cost analysis** for typical anchor submissions.
    

Which of these would you like next?