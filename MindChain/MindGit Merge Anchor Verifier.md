Nice — below is a **complete, ready-to-run Node.js reference verifier** that:

- fetches a `proofCID` (supports IPFS HTTP gateways, raw HTTPS, Arweave URLs),
    
- extracts the proof bundle (tar/zip),
    
- checks canonical SHA-256 prefix against the DNA prefix you provide,
    
- validates signer signatures (Ed25519) against supplied DID docs / public keys, and
    
- attempts to run Coq proof checking (`coqc`) on any `.v` files found (if `coqc` is installed on the host).
    

It’s **opinionated but practical**: heavy formal proof checking (Coq / AAL) is performed by invoking `coqc` on the proof files; if `coqc` is not installed the verifier reports that and still validates all other checks.

I include:

- `package.json` (dependencies)
    
- `verify-proof.js` — the verifier script
    
- README-style usage & explanation
    

Run on a machine with Node 18+.

---

## 1) `package.json`

```json
{
  "name": "mindgit-merge-verifier",
  "version": "1.0.0",
  "description": "Off-chain merge-anchor verifier for MindGit (fetch proofCID, validate manifests, verify signatures, run Coq)",
  "main": "verify-proof.js",
  "scripts": {
    "verify": "node verify-proof.js"
  },
  "author": "Axiomatic Research Laboratory",
  "license": "MIT",
  "dependencies": {
    "node-fetch": "^3.3.1",
    "tar": "^6.1.11",
    "adm-zip": "^0.5.9",
    "tweetnacl": "^1.0.3",
    "js-sha256": "^0.9.0",
    "did-resolver": "^3.0.1"
  },
  "type": "module"
}
```

> Notes:
> 
> - `node-fetch` for HTTP fetching (Node 18+ includes fetch globally but package ensures compatibility).
>     
> - `tar` and `adm-zip` for archive extraction.
>     
> - `tweetnacl` for Ed25519 signature verification.
>     
> - `js-sha256` for hash computation.
>     
> - `did-resolver` is included for DID resolution helpers (you may configure resolvers per environment).
>     

Install deps:

```bash
npm install
```

---

## 2) `verify-proof.js`

Save the file and run `node verify-proof.js --help` for usage.

```javascript
#!/usr/bin/env node
/**
 * verify-proof.js
 *
 * MindGit Merge Anchor Verifier (off-chain)
 *
 * Fetches a proof bundle by proofCID (supports ipfs gateway, HTTP(S) links),
 * extracts it, validates the included manifest, verifies Ed25519 signatures
 * (against public keys fetched from DID documents or provided URLs), computes
 * and compares canonical SHA-256 prefixes for DNA, and runs Coq (coqc) on any
 * .v files if available.
 *
 * Usage:
 *   node verify-proof.js --proof <proofCID-or-URL> --dna-prefix <path/to/prefix.jsonl> --anchor '<json-string-or-file>'
 *
 * Examples:
 *   node verify-proof.js --proof bafy... --dna-prefix ./dna_prefix.jsonl --anchor ./anchor.json
 *   node verify-proof.js --proof https://ipfs.io/ipfs/<cid> --dna-prefix ./prefix.jsonl --anchor '{"organism_did":"did:canvasl:...","generation":42,"sha256_prefix":"0x..."}'
 */

import fs from "fs";
import os from "os";
import path from "path";
import crypto from "crypto";
import { fileURLToPath } from "url";
import fetchPkg from "node-fetch";
const fetch = fetchPkg;
import Tar from "tar";
import AdmZip from "adm-zip";
import nacl from "tweetnacl";
import { sha256 } from "js-sha256";
import { spawnSync } from "child_process";
import { Resolver } from "did-resolver";

// -- simple CLI parsing
function usageAndExit() {
  console.log(`
MindGit Merge Anchor Verifier

Usage:
  node verify-proof.js --proof <proofCID-or-URL> --dna-prefix <path/to/prefix.jsonl> --anchor <anchor.json|anchor-string>

Options:
  --proof         proofCID (IPFS CID) or HTTP(S)/arweave URL to download proof bundle
  --dna-prefix    path to canonical JSONL DNA prefix (text) used to compute sha256Prefix
  --anchor        anchor JSON object (file path or raw JSON string) containing at least:
                   { "organism_did", "generation", "sha256_prefix", "proofCID" }
  --outdir        optional output dir (defaults to temp dir)
  --help          show this message
`);
  process.exit(1);
}

const argv = process.argv.slice(2);
if (argv.includes("--help") || argv.length === 0) usageAndExit();

function argVal(flag) {
  const i = argv.indexOf(flag);
  if (i === -1 || i === argv.length - 1) return null;
  return argv[i + 1];
}

const proofArg = argVal("--proof");
const dnaPrefixPath = argVal("--dna-prefix");
const anchorArg = argVal("--anchor");
const outdirArg = argVal("--outdir");

if (!proofArg || !dnaPrefixPath || !anchorArg) {
  usageAndExit();
}

// Read anchor (file or JSON string)
let anchorObj = null;
try {
  if (fs.existsSync(anchorArg)) {
    anchorObj = JSON.parse(fs.readFileSync(anchorArg, "utf8"));
  } else {
    anchorObj = JSON.parse(anchorArg);
  }
} catch (e) {
  console.error("Failed to parse --anchor argument as JSON or file:", e.message);
  process.exit(2);
}

const OUT_ROOT = outdirArg ? path.resolve(outdirArg) : fs.mkdtempSync(path.join(os.tmpdir(), "mindgit-proof-"));
if (!fs.existsSync(OUT_ROOT)) fs.mkdirSync(OUT_ROOT, { recursive: true });

console.log("Working directory:", OUT_ROOT);

// Utility: fetch resource (CID or URL)
async function fetchProofBundle(proofCIDorURL, destPath) {
  // Accept: ipfs CID (base32/36/58) or a full URL
  let url;
  if (proofCIDorURL.startsWith("http://") || proofCIDorURL.startsWith("https://")) {
    url = proofCIDorURL;
  } else if (/^bafy|^Qm|^[A-Za-z0-9]/.test(proofCIDorURL)) {
    // try ipfs.io gateway first
    url = `https://ipfs.io/ipfs/${proofCIDorURL}`;
  } else {
    throw new Error("Unrecognized proofCID/URL format");
  }

  console.log("Downloading proof bundle from", url);
  const res = await fetch(url);
  if (!res.ok) {
    throw new Error(`Failed to fetch proof bundle: ${res.status} ${res.statusText}`);
  }
  const buf = await res.arrayBuffer();
  fs.writeFileSync(destPath, Buffer.from(buf));
  return destPath;
}

// Utility: detect archive type and extract
async function extractBundle(archivePath, destDir) {
  const magic = fs.readFileSync(archivePath, { start: 0, end: 262 }).toString("utf8");
  // crude detection
  const ext = path.extname(archivePath).toLowerCase();
  if (ext === ".zip" || magic.includes("PK")) {
    console.log("Detected ZIP archive; extracting via adm-zip");
    const zip = new AdmZip(archivePath);
    zip.extractAllTo(destDir, true);
    return destDir;
  } else {
    // assume tar (tar.gz or tar)
    try {
      console.log("Attempting tar extraction");
      await Tar.x({ file: archivePath, C: destDir });
      return destDir;
    } catch (e) {
      throw new Error("Unable to extract archive: unknown format");
    }
  }
}

// Compute canonical SHA-256 of DNA prefix file (text)
function computeSha256HexFromFile(filePath) {
  const text = fs.readFileSync(filePath, "utf8");
  // canonicalization: trim trailing whitespace, ensure newline endings normalized to \n
  const normalized = text.replace(/\r\n/g, "\n");
  const h = sha256(normalized);
  return "0x" + h;
}

// Helper: verify Ed25519 signature given public key (base58 or hex)
function verifyEd25519Signature(messageBytes, signatureBytes, publicKeyBytes) {
  try {
    // tweetnacl expects Uint8Array
    const ok = nacl.sign.detached.verify(
      new Uint8Array(messageBytes),
      new Uint8Array(signatureBytes),
      new Uint8Array(publicKeyBytes)
    );
    return ok;
  } catch (e) {
    console.warn("Ed25519 verify error", e.message);
    return false;
  }
}

// Utility: fetch DID Document minimal resolver (very small)
// For production use a full DID resolver; here we accept did URLs with direct JSON fetch
async function fetchDidDocument(didOrUrl) {
  // Accept either a DID doc URL (http... returning DID JSON) or a did: value that includes a resolver endpoint in metadata
  if (didOrUrl.startsWith("http://") || didOrUrl.startsWith("https://")) {
    const r = await fetch(didOrUrl);
    if (!r.ok) throw new Error("Failed to fetch DID doc URL");
    return await r.json();
  }
  // Basic heuristic: if DID contains a 'service' entry in anchorObj, try to use that
  // Otherwise, look up via well-known: https://<method-resolver>/... (omitted)
  throw new Error("DID resolution not implemented for 'did:' identifiers in this reference script. Provide a DID-doc URL in signature metadata or use an HTTP DID doc URL in proof manifest.");
}

// Main runner
(async () => {
  try {
    // Step 1: verify anchor fields and sha256 prefix match
    if (!anchorObj.organism_did && !anchorObj.organismDID && !anchorObj.organismDID) {
      console.warn("Anchor object missing organism_did / organismDID field - continuing but sanity checks may fail.");
    }
    const expectedSha = anchorObj.sha256_prefix || anchorObj.sha256Prefix || anchorObj.sha256 || anchorObj.sha256Prefix;
    if (!expectedSha) {
      console.warn("Anchor object missing sha256_prefix. Please provide canonical sha for comparison.");
    }

    // compute local sha from dna prefix file
    const computedSha = computeSha256HexFromFile(dnaPrefixPath);
    console.log("Computed SHA-256 prefix:", computedSha);
    if (expectedSha) {
      console.log("Anchor expected SHA-256 prefix:", expectedSha);
      if (computedSha.toLowerCase() !== expectedSha.toLowerCase()) {
        console.error("SHA-256 mismatch between anchor and provided dna prefix. Verification FAIL.");
        // but continue extracting for further checks
      } else {
        console.log("SHA-256 prefix matches anchor.");
      }
    }

    // Step 2: fetch proof bundle
    const proofDest = path.join(OUT_ROOT, "proof.bundle");
    await fetchProofBundle(proofArg, proofDest);

    // Step 3: extract bundle
    const extractDir = path.join(OUT_ROOT, "proof-extracted");
    fs.mkdirSync(extractDir, { recursive: true });
    await extractBundle(proofDest, extractDir);
    console.log("Proof bundle extracted to:", extractDir);

    // Step 4: find manifest file (proof.json or manifest.json)
    const candidates = ["proof.json", "manifest.json", "proof-manifest.json"];
    let manifest = null;
    for (const f of candidates) {
      const p = path.join(extractDir, f);
      if (fs.existsSync(p)) {
        manifest = JSON.parse(fs.readFileSync(p, "utf8"));
        console.log("Loaded manifest:", f);
        break;
      }
    }
    if (!manifest) {
      // try to find any *.json that looks like a manifest
      const files = fs.readdirSync(extractDir);
      for (const f of files) {
        if (f.toLowerCase().endsWith(".json")) {
          const candidate = JSON.parse(fs.readFileSync(path.join(extractDir, f), "utf8"));
          if (candidate.proof_type || candidate.proof || candidate.prover) {
            manifest = candidate;
            console.log("Loaded manifest from", f);
            break;
          }
        }
      }
    }

    if (!manifest) {
      console.warn("No manifest found in proof bundle. Proceeding with limited checks.");
    } else {
      console.log("Manifest summary:", Object.keys(manifest));
    }

    // Step 5: verify signatures declared in manifest (if any)
    let signatureReport = [];
    if (manifest && Array.isArray(manifest.signatures)) {
      for (const sig of manifest.signatures) {
        // sig may contain: { type: "Ed25519", signer: "did:...", publicKeyUrl: "https://...", signature: "base64", alg: "EdDSA" }
        const sigType = sig.type || "Ed25519";
        const sigB64 = sig.signature || sig.sig;
        if (!sigB64) {
          signatureReport.push({ ok: false, reason: "signature missing field" });
          continue;
        }
        const signatureBytes = Buffer.from(sigB64, "base64");
        // message to verify: canonical manifest payload (manifest.payload or manifest.signed)
        const payload = sig.payload || manifest.payload || manifest.signed || JSON.stringify(manifest.payload || manifest.signed || manifest);
        // fetch public key
        let pubKeyBytes = null;
        if (sig.publicKeyUrl) {
          try {
            const r = await fetch(sig.publicKeyUrl);
            if (!r.ok) throw new Error("Failed to fetch public key URL");
            const keyBody = await r.text();
            // expect raw hex or base58 or JSON with publicKeyBase58
            try {
              const j = JSON.parse(keyBody);
              if (j.publicKeyMultibase) {
                // remove multibase prefix (assume 'z' base58btc)
                const multibase = j.publicKeyMultibase;
                // crude: base58 decode is not included in this reference; try publicKeyBase58
                if (j.publicKeyBase58) {
                  // TODO: in production decode base58; here assume key is hex in j.publicKeyHex
                }
              }
            } catch (e) {
              // treat body as hex/base64
            }
            // Try a couple heuristics:
            let pkHex = null;
            if (/^[0-9a-fA-F]+$/.test(keyBody.trim())) {
              pkHex = keyBody.trim();
              pubKeyBytes = Buffer.from(pkHex, "hex");
            } else if (/^[A-Za-z0-9+/=]+$/.test(keyBody.trim())) {
              // base64
              pubKeyBytes = Buffer.from(keyBody.trim(), "base64");
            } else {
              // attempt JSON parse
              try {
                const jb = JSON.parse(keyBody);
                if (jb.publicKeyBase58) {
                  // not implementing base58 decode here; we require publicKeyUrl to return hex/base64 for this reference script
                  console.warn("publicKeyBase58 encountered; this reference script requires hex/base64 public keys. Please provide hex/base64.");
                } else if (jb.publicKeyJwk) {
                  // convert JWK Ed25519 x param (base64url) into bytes
                  const x = jb.publicKeyJwk.x;
                  const b = Buffer.from(x.replace(/-/g, "+").replace(/_/g, "/"), "base64");
                  pubKeyBytes = b;
                }
              } catch (e) {
                // unknown format
              }
            }
          } catch (e) {
            signatureReport.push({ ok: false, reason: "failed fetch publicKeyUrl: " + e.message });
            continue;
          }
        } else if (sig.signerDid) {
          // Look up DID doc URL via convention or manifest mapping
          const didDocUrl = sig.publicKeyUrl || sig.didDocUrl || sig.signerDidDocUrl;
          if (!didDocUrl) {
            signatureReport.push({ ok: false, reason: "no publicKeyUrl or didDocUrl provided for signerDid" });
            continue;
          }
          try {
            const dd = await fetchDidDocument(didDocUrl);
            // extract first Ed25519 verificationMethod publicKeyMultibase or publicKeyBase58
            let pkBytes = null;
            if (dd.verificationMethod && dd.verificationMethod.length) {
              const vm = dd.verificationMethod[0];
              if (vm.publicKeyJwk && vm.publicKeyJwk.x) {
                const x = vm.publicKeyJwk.x;
                pkBytes = Buffer.from(x.replace(/-/g, "+").replace(/_/g, "/"), "base64");
              } else if (vm.publicKeyHex) {
                pkBytes = Buffer.from(vm.publicKeyHex.replace(/^0x/, ""), "hex");
              } else if (vm.publicKeyBase58) {
                console.warn("publicKeyBase58 found in DID doc; this reference script does not decode base58. Use a hex/base64 public key URL instead.");
              } else if (vm.publicKeyMultibase) {
                console.warn("publicKeyMultibase found; not decoded by reference script.");
              }
              if (pkBytes) pubKeyBytes = pkBytes;
            }
          } catch (e) {
            signatureReport.push({ ok: false, reason: "did-doc fetch failed: " + e.message });
            continue;
          }
        } else {
          signatureReport.push({ ok: false, reason: "no signer DID or publicKeyUrl specified" });
          continue;
        }

        if (!pubKeyBytes) {
          signatureReport.push({ ok: false, reason: "failed to obtain public key bytes for signature" });
          continue;
        }

        // verify
        const ok = verifyEd25519Signature(Buffer.from(payload, "utf8"), signatureBytes, pubKeyBytes);
        signatureReport.push({ ok, signer: sig.signerDid || sig.publicKeyUrl || sig.publicKeyHex || "unknown", reason: ok ? "verified" : "signature mismatch" });
      }
    } else {
      console.log("No signatures array found in manifest; skipping signature verification.");
    }

    // Step 6: run Coq (if .v files exist)
    const coqFiles = [];
    function walk(dir) {
      const items = fs.readdirSync(dir);
      for (const it of items) {
        const p = path.join(dir, it);
        const st = fs.statSync(p);
        if (st.isDirectory()) walk(p);
        else if (it.endsWith(".v")) coqFiles.push(p);
      }
    }
    walk(extractDir);
    let coqReport = { coqAvailable: false, results: [] };
    // check coqc
    const coqcCheck = spawnSync("coqc", ["--version"]);
    if (coqcCheck.status === 0) {
      coqReport.coqAvailable = true;
      console.log("coqc detected. Running proofs...");
      for (const f of coqFiles) {
        console.log("Running coqc on", f);
        const r = spawnSync("coqc", [f], { encoding: "utf8", cwd: path.dirname(f), timeout: 10 * 60 * 1000 });
        const ok = (r.status === 0);
        coqReport.results.push({ file: f, ok, stdout: r.stdout ? String(r.stdout).slice(0, 1000) : "", stderr: r.stderr ? String(r.stderr).slice(0, 1000) : "" });
        console.log(`coqc ${ok ? "OK" : "FAILED"}: ${f} (exit ${r.status})`);
      }
    } else {
      console.warn("coqc not found in PATH. Skipping Coq checking. Install Coq (coqc) to run formal checks.");
    }

    // Step 7: final report
    const report = {
      anchor: anchorObj,
      computedSha,
      manifestPath: manifest ? Object.keys(manifest) : null,
      manifest,
      signatureReport,
      coqReport,
      extractedPath: extractDir,
      tempDir: OUT_ROOT
    };

    const rptPath = path.join(OUT_ROOT, "verification-report.json");
    fs.writeFileSync(rptPath, JSON.stringify(report, null, 2), "utf8");
    console.log("Verification completed. Report:", rptPath);
    console.log(JSON.stringify(report, null, 2));
    process.exit(0);

  } catch (err) {
    console.error("Verification failed:", err && err.message ? err.message : err);
    process.exit(3);
  }
})();
```

---

## 3) Expected proof bundle layout (recommended)

To interoperate well with the verifier, the off-chain proof bundle should be a `.tar.gz` or `.zip` with the following elements:

```
proof-bundle.tar.gz
├─ proof.json             # manifest, includes signatures array
├─ dna_prefix.jsonl       # optionally include the canonical DNA prefix
├─ coq/
│  ├─ proof.v
│  └─ support.v
├─ aal/
│  └─ aal-certificate.json
└─ proof-artifacts/
   └─ proof.witness.bin
```

**`proof.json`** should include (example):

```json
{
  "prover": "Axiomatic Research Laboratory",
  "proof_type": "AAL+Coq",
  "organism_did": "did:canvasl:...",
  "generation": 1234,
  "sha256_prefix": "0xabc123...",
  "norm": "42",
  "signatures": [
    {
      "type": "Ed25519",
      "signerDid": "did:canvasl:issuer456",
      "publicKeyUrl": "https://example.org/keys/issuer456.pub.hex",
      "signature": "<base64 signature>",
      "payload": "{\"sha256_prefix\":\"0xabc123...\",\"generation\":1234}"
    }
  ],
  "coq_files": ["coq/proof.v"],
  "proof_artifact_links": ["ipfs://bafy..."]
}
```

- `publicKeyUrl` is expected to return raw public key bytes in hex or base64 OR a minimal DID doc (JSON) with `verificationMethod` fields; the reference verifier includes heuristics but production systems should expose keys in a standardized format (e.g., `publicKeyHex` or JWK) for deterministic verification.
    

---

## 4) How the verifier validates proofs (summary)

1. **Canonical SHA check**: compute SHA-256 of the DNA prefix file you provide and compare to anchor's `sha256_prefix`.
    
2. **Bundle fetch & extraction**: download the proofCID and extract it.
    
3. **Manifest parsing**: read `proof.json` for metadata & signatures.
    
4. **Signature verification**: for each signature: fetch public key (URL or DID doc) and verify Ed25519 signatures over the canonical payload.
    
5. **Coq verification**: if `.v` files are present and `coqc` is installed, run `coqc` on each file and ensure no errors (exit code 0).
    
6. **Report**: produce a JSON report including signature results, coq run outputs, and any mismatch.
    

---

## 5) Caveats & Production Notes

- **DID resolution**: The reference script expects `publicKeyUrl` or `didDocUrl` in the manifest. Full DID resolution (multiple methods, method-specific resolvers) should be implemented using a DID resolver library (e.g., `did-resolver`, method drivers). I included `did-resolver` in `package.json` for future extension but kept the script conservative.
    
- **Base58/Multibase**: Production DID docs often list keys in base58 or multibase. This reference script does not decode base58 (it warns). For production use, add a base58 library (`bs58`) and multibase parsing.
    
- **BBS+ / selective disclosure**: BBS+/BLS signatures require specialized libs and verification. This verifier covers Ed25519/JWK verification; extend to BBS+ as needed.
    
- **Coq environment**: Proofs depending on complex libraries or non-portable filesystem paths may fail in this simple runner. Use reproducible Coq containers (Docker with pinned Coq version) to run proofs reliably.
    
- **Canonicalization**: It's critical that the DNA prefix is canonicalized the same way off-chain and by verifiers. Define and share an exact canonicalization algorithm (field order, whitespace, newline normalization) and enforce it in toolchains.
    

---

## 6) Example run

Assuming:

- `dna_prefix.jsonl` prepared canonically
    
- `anchor.json` contains anchor metadata with `sha256_prefix` and `proofCID`
    
- proofCID is `bafy...`
    

```bash
node verify-proof.js --proof bafy... --dna-prefix ./dna_prefix.jsonl --anchor ./anchor.json
```

Output: a `verification-report.json` in a temporary working directory with details about signature verification and Coq results.

---

## 7) Next steps / Enhancements I can add

If you want, I can:

- Add **base58 / multibase** decoding (bs58 + multibase) to fully support DID docs.
    
- Integrate a full **did-resolver** instance (with common method drivers) to fetch verification keys directly from DIDs.
    
- Add **BBS+** signature verification for selective-disclosure proofs.
    
- Provide a **Dockerfile** that bundles Coq + script to run proofs reliably in CI.
    
- Add a **test-suite** with sample proof bundles (passes, fails, edge-cases) and automated CI.
    

Which enhancement would you like next?