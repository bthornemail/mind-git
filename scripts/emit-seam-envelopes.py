#!/usr/bin/env python3
"""
mind-git -> ULP seam envelope emitter (Producer).

Goal: durable, deterministic provenance facts (claims/links/notes) without authority logic.
- Input: a small JSON file with {"claims":[...]}.
- Output: port-matroid seam envelopes (NDJSON).
- Claim ordering is canonicalized (sorted by claim digest), so input ordering doesn't matter.
- All values are strings.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def canonical_json(obj: object) -> str:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def emit_ndjson(obj: dict) -> None:
    print(json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True))

def component_prefix(namespace: str) -> str:
    parts = namespace.split(".")
    if len(parts) < 4 or parts[0:2] != ["ulp", "trace"]:
        raise SystemExit(f"namespace invalid (expected ulp.trace.<producer>.*.vN): {namespace!r}")
    return parts[2] + "__"


def main() -> int:
    ap = argparse.ArgumentParser(description="Emit ULP seam envelopes for mind-git claim fixtures.")
    ap.add_argument("--input", required=True, help="Path to claims JSON")
    ap.add_argument("--namespace", default="ulp.trace.mind_git.v0")
    ap.add_argument("--writer", default="mind-git")
    ap.add_argument("--epoch", type=int, default=1)
    ap.add_argument("--gen", type=int, default=1)
    ap.add_argument("--owner-mask", type=int, default=15)
    args = ap.parse_args()
    prefix = component_prefix(args.namespace)

    in_path = Path(args.input)
    root = json.loads(in_path.read_text())

    if set(root.keys()) != {"claims"} or not isinstance(root["claims"], list):
        raise SystemExit("input JSON must have exact shape: {\"claims\":[...]}")

    claims = root["claims"]
    for c in claims:
        if not isinstance(c, dict) or set(c.keys()) != {"type", "subject_hash", "payload", "actor", "policy"}:
            raise SystemExit("each claim must have exact keys: type, subject_hash, payload, actor, policy")
        if not isinstance(c["payload"], dict):
            raise SystemExit("claim payload must be an object")

    # Canonicalize claim identity and ordering.
    claim_rows: list[tuple[str, dict]] = []
    for c in claims:
        payload_digest = "sha256:" + sha256_hex(canonical_json(c["payload"]).encode("utf-8"))
        claim_id = "sha256:" + sha256_hex(
            (str(c["type"]) + "\n" + str(c["subject_hash"]) + "\n" + str(c["actor"]) + "\n" + str(c["policy"]) + "\n" + payload_digest + "\n").encode("utf-8")
        )
        row = {
            "type": str(c["type"]),
            "subject_hash": str(c["subject_hash"]),
            "actor": str(c["actor"]),
            "policy": str(c["policy"]),
            "payload_digest": payload_digest,
            "claim_id": claim_id,
        }
        claim_rows.append((claim_id, row))

    claim_rows.sort(key=lambda t: t[0])
    claim_list_digest = "sha256:" + sha256_hex(("".join([cid + "\n" for cid, _ in claim_rows])).encode("utf-8"))

    authority = {"kind": "direct", "basis": []}
    meta = {"writer": args.writer, "epoch": args.epoch, "gen": args.gen}

    def env(payload: dict) -> dict:
        return {"namespace": args.namespace, "authority": authority, "meta": meta, "payload": payload}

    trace_eid = 1
    run_eid = 2

    emit_ndjson(env({"op": "create_entity", "eid": trace_eid, "etype": "trace", "owner_mask": args.owner_mask}))
    emit_ndjson(env({"op": "set_component_string", "eid": trace_eid, "key": prefix + "trace_kind", "value": "claims_fixture"}))
    emit_ndjson(env({"op": "set_component_string", "eid": trace_eid, "key": prefix + "trace_source", "value": "claims"}))
    emit_ndjson(env({"op": "set_component_string", "eid": trace_eid, "key": prefix + "trace_claim_list_digest", "value": claim_list_digest}))

    emit_ndjson(env({"op": "create_entity", "eid": run_eid, "etype": "claims", "owner_mask": args.owner_mask}))
    emit_ndjson(env({"op": "set_component_string", "eid": run_eid, "key": prefix + "claim_list_digest", "value": claim_list_digest}))
    emit_ndjson(env({"op": "set_component_string", "eid": run_eid, "key": prefix + "claim_count", "value": str(len(claim_rows))}))

    for idx, (cid, row) in enumerate(claim_rows):
        eid = 100 + idx
        emit_ndjson(env({"op": "create_entity", "eid": eid, "etype": "claim", "owner_mask": args.owner_mask}))
        emit_ndjson(env({"op": "set_component_string", "eid": eid, "key": prefix + "claim_id", "value": row["claim_id"]}))
        emit_ndjson(env({"op": "set_component_string", "eid": eid, "key": prefix + "claim_type", "value": row["type"]}))
        emit_ndjson(env({"op": "set_component_string", "eid": eid, "key": prefix + "claim_subject_hash", "value": row["subject_hash"]}))
        emit_ndjson(env({"op": "set_component_string", "eid": eid, "key": prefix + "claim_actor", "value": row["actor"]}))
        emit_ndjson(env({"op": "set_component_string", "eid": eid, "key": prefix + "claim_policy", "value": row["policy"]}))
        emit_ndjson(env({"op": "set_component_string", "eid": eid, "key": prefix + "claim_payload_digest", "value": row["payload_digest"]}))
        emit_ndjson(env({"op": "set_component_string", "eid": eid, "key": prefix + "claim_list_digest", "value": claim_list_digest}))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
