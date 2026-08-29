#!/usr/bin/env python3
"""Independently validate one accepted H1 replay receipt and its artifacts."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from replay_common import (
    RECEIPT_SCHEMA, AwsCliObjectStore, LocalObjectStore, ObjectStore, ReplayError,
    canonical_json, load_json,
    load_manifest, require_sha, require_tag, sha256_bytes, sha256_file,
)


def validate(args: argparse.Namespace) -> None:
    manifest = load_manifest(args.manifest)
    manifest_sha = sha256_file(args.manifest)
    receipt = load_json(args.receipt)
    if receipt.get("schema") != RECEIPT_SCHEMA or receipt.get("accepted") is not True:
        raise ReplayError("receipt is not an accepted replay-v1 receipt")
    tag = require_tag(receipt.get("tag"))
    if receipt.get("manifest_sha256") != manifest_sha:
        raise ReplayError("receipt manifest SHA mismatch")
    require_sha(receipt.get("job_sha256"), "receipt.job_sha256")
    require_sha(receipt.get("replay_ready_sha256"), "receipt.replay_ready_sha256")
    audit = receipt.get("axiom_audit")
    if not isinstance(audit, dict) or audit.get("sorry_ax") is not False or audit.get("source_scan") != "PASS":
        raise ReplayError("receipt axiom/source audit is not accepted")
    axioms = audit.get("axioms")
    patterns = [re.compile(pattern) for pattern in manifest.get("allowed_axiom_patterns", [])]
    unexpected = (
        [] if not isinstance(axioms, list) else [
            axiom for axiom in axioms
            if axiom not in set(manifest["allowed_axioms"])
            and not any(pattern.fullmatch(axiom) for pattern in patterns)
        ]
    )
    if not isinstance(axioms, list) or unexpected:
        raise ReplayError("receipt contains malformed or undisclosed axioms")

    before = receipt.get("certificate_before_tagging")
    after = receipt.get("certificate_after_tagging")
    if not isinstance(before, dict) or not isinstance(after, dict):
        raise ReplayError("receipt lacks certificate before/after records")
    for field in ("key", "size", "sha256", "etag", "last_modified"):
        if before.get(field) != after.get(field):
            raise ReplayError(f"certificate identity changed at field {field}")
    if not isinstance(after.get("tags"), dict) or after["tags"].get("replay") != "consumed":
        raise ReplayError("receipt does not prove replay=consumed")

    store: ObjectStore = (
        LocalObjectStore(args.object_store_root)
        if args.object_store_root is not None
        else AwsCliObjectStore(args.s3_bucket, args.aws)
    )
    actual_certificate = store.head(before["key"])
    if (actual_certificate.sha256, actual_certificate.size, actual_certificate.etag,
        actual_certificate.last_modified) != (
        before["sha256"], before["size"], before["etag"], before["last_modified"]
    ):
        raise ReplayError("live certificate identity differs from receipt")
    if actual_certificate.tags.get("replay") != "consumed":
        raise ReplayError("live certificate has lost consumed tag")

    artifacts = receipt.get("artifacts")
    if not isinstance(artifacts, dict) or set(artifacts) != {"source", "log", "olean"}:
        raise ReplayError("receipt artifact set is malformed")
    for label, expected in artifacts.items():
        if not isinstance(expected, dict):
            raise ReplayError(f"receipt {label} artifact is malformed")
        actual = store.head(expected.get("key", ""))
        if actual.sha256 != expected.get("sha256") or actual.size != expected.get("size"):
            raise ReplayError(f"live {label} artifact differs from receipt")

    prefix = manifest["campaign_prefix"]
    ready_key = f"{prefix}replay-ready/{tag}.json"
    ready_path = args.receipt.parent / f".{tag}.ready.validation.json"
    try:
        store.download(ready_key, ready_path)
        ready = load_json(ready_path)
    finally:
        ready_path.unlink(missing_ok=True)
    if sha256_bytes(canonical_json(ready)) != receipt["replay_ready_sha256"]:
        raise ReplayError("replay-ready record hash mismatch")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    backend = parser.add_mutually_exclusive_group(required=True)
    backend.add_argument("--object-store-root", type=Path)
    backend.add_argument("--s3-bucket")
    parser.add_argument("--aws", default="aws")
    args = parser.parse_args()
    try:
        validate(args)
    except ReplayError as error:
        print(f"INVALID: {error}", file=sys.stderr)
        return 2
    print("VALID")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
