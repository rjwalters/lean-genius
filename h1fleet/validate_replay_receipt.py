#!/usr/bin/env python3
"""Independently validate one accepted H1 replay receipt and its artifacts."""

from __future__ import annotations

import argparse
import re
import sys
import tempfile
from pathlib import Path

from replay_common import (
    RECEIPT_SCHEMA, AwsCliObjectStore, LocalObjectStore, ObjectInfo, ObjectStore, ReplayError,
    canonical_json, load_json,
    load_manifest, require_sha, require_tag, sha256_bytes, sha256_file,
    validate_command_receipts,
)
from replay_worker import (
    artifact_key, ledger_key, ready_key, receipt_command_bindings, receipt_key,
    validate_aws_cli, validate_production_manifest,
)


STABLE_OBJECT_FIELDS = (
    "key", "size", "sha256", "etag", "last_modified", "version_id",
    "metadata", "tags",
)


def validate_downloaded_identity(
    label: str, expected: object, actual: ObjectInfo, downloaded: Path,
) -> None:
    """Compare recorded stable identity and independently rehash GET bytes."""
    if not isinstance(expected, dict):
        raise ReplayError(f"receipt {label} object identity is malformed")
    downloaded_sha = sha256_file(downloaded)
    if downloaded.stat().st_size != actual.size or downloaded_sha != actual.sha256:
        raise ReplayError(f"downloaded {label} bytes differ from returned object identity")
    for field in STABLE_OBJECT_FIELDS:
        if expected.get(field) != getattr(actual, field):
            raise ReplayError(f"live {label} differs from receipt at {field}")


def validate_production_backend_binding(
    manifest: dict[str, object], s3_bucket: str, aws: str,
) -> None:
    """Bind independent validation to the frozen production backend."""
    validate_production_manifest(manifest)
    if s3_bucket != manifest["s3_bucket"]:
        raise ReplayError("S3 bucket differs from frozen manifest")
    validate_aws_cli(aws, str(manifest["aws_cli_identity"]))


def validate(args: argparse.Namespace) -> None:
    manifest = load_manifest(args.manifest)
    manifest_sha = sha256_file(args.manifest)
    supplied_receipt_bytes = args.receipt.read_bytes()
    supplied_receipt_sha = sha256_bytes(supplied_receipt_bytes)
    receipt = load_json(args.receipt)
    if receipt.get("schema") != RECEIPT_SCHEMA or receipt.get("accepted") is not True:
        raise ReplayError("receipt is not an accepted replay-v1 receipt")
    tag = require_tag(receipt.get("tag"))
    if receipt.get("manifest_sha256") != manifest_sha:
        raise ReplayError("receipt manifest SHA mismatch")
    require_sha(receipt.get("job_sha256"), "receipt.job_sha256")
    require_sha(receipt.get("replay_ready_sha256"), "receipt.replay_ready_sha256")
    if not isinstance(receipt.get("tagging_request_id"), str) or not receipt["tagging_request_id"]:
        raise ReplayError("receipt lacks tagging request id")
    if receipt.get("tagging_operation") not in ("performed", "already_present"):
        raise ReplayError("receipt has invalid tagging operation")
    expected_request_kind = {
        "performed": "put-object-tagging",
        "already_present": "get-object-tagging-readback",
    }[receipt["tagging_operation"]]
    if receipt.get("tagging_request_kind") != expected_request_kind:
        raise ReplayError("receipt has invalid tagging request kind")
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
    if before.get("version_id") != after.get("version_id"):
        raise ReplayError("certificate identity changed at field version_id")
    if not isinstance(after.get("tags"), dict) or after["tags"].get("replay") != "consumed":
        raise ReplayError("receipt does not prove replay=consumed")

    if args.object_store_root is not None:
        store: ObjectStore = LocalObjectStore(args.object_store_root)
    else:
        validate_production_backend_binding(manifest, args.s3_bucket, args.aws)
        store = AwsCliObjectStore(args.s3_bucket, args.aws)
    prefix = manifest["campaign_prefix"]
    live_receipt_key = receipt_key(prefix, tag)
    with tempfile.TemporaryDirectory() as temporary:
        live_receipt_path = Path(temporary) / "receipt.json"
        live_receipt = store.download(live_receipt_key, live_receipt_path)
        live_receipt_bytes = live_receipt_path.read_bytes()
        live_receipt_sha = sha256_file(live_receipt_path)
    if live_receipt_bytes != supplied_receipt_bytes or (
        live_receipt.key != live_receipt_key
        or live_receipt.size != len(supplied_receipt_bytes)
        or live_receipt.sha256 != supplied_receipt_sha
        or live_receipt_sha != supplied_receipt_sha
    ):
        raise ReplayError("supplied receipt bytes differ from immutable live receipt")
    if (
        live_receipt.metadata.get("tag") != tag
        or live_receipt.metadata.get("manifest-sha256") != manifest_sha
        or ("sha256" in live_receipt.metadata
            and live_receipt.metadata["sha256"] != live_receipt_sha)
    ):
        raise ReplayError("live receipt metadata binding is malformed")
    with tempfile.TemporaryDirectory() as temporary:
        actual_certificate = store.download(before["key"], Path(temporary) / "certificate")
    if (actual_certificate.sha256, actual_certificate.size, actual_certificate.etag,
        actual_certificate.last_modified, actual_certificate.version_id) != (
        before["sha256"], before["size"], before["etag"], before["last_modified"],
        before.get("version_id")
    ):
        raise ReplayError("live certificate identity differs from receipt")
    if actual_certificate.tags.get("replay") != "consumed":
        raise ReplayError("live certificate has lost consumed tag")

    artifacts = receipt.get("artifacts")
    if not isinstance(artifacts, dict) or set(artifacts) != {"source", "log", "olean"}:
        raise ReplayError("receipt artifact set is malformed")
    artifact_locations = {
        "source": artifact_key(prefix, "sources", tag, "lean.zst"),
        "log": artifact_key(prefix, "logs", tag, "log.zst"),
        "olean": artifact_key(prefix, "oleans", tag, "olean.zst"),
    }
    with tempfile.TemporaryDirectory() as temporary:
        for label, expected in artifacts.items():
            if not isinstance(expected, dict) or expected.get("key") != artifact_locations[label]:
                raise ReplayError(f"receipt {label} artifact key is not canonical")
            destination = Path(temporary) / f"{label}.zst"
            actual = store.download(artifact_locations[label], destination)
            validate_downloaded_identity(label, expected, actual, destination)

    live_ready_key = ready_key(prefix, tag)
    replay_ready_info = receipt.get("replay_ready")
    if not isinstance(replay_ready_info, dict) or replay_ready_info.get("key") != live_ready_key:
        raise ReplayError("receipt lacks immutable replay-ready object identity")
    with tempfile.TemporaryDirectory() as temporary:
        ready_path = Path(temporary) / "replay-ready.json"
        ready_info = store.download(live_ready_key, ready_path)
        validate_downloaded_identity(
            "replay-ready", replay_ready_info, ready_info, ready_path)
        ready = load_json(ready_path)
    if sha256_bytes(canonical_json(ready)) != receipt["replay_ready_sha256"]:
        raise ReplayError("replay-ready record hash mismatch")
    if ready.get("artifacts") != receipt.get("artifacts"):
        raise ReplayError("receipt artifacts differ from replay-ready evidence")
    for field in (
        "job_identity", "build_identity", "module", "compact_lrat", "source_raw",
        "olean_raw", "commands", "work_root", "worker_runtime",
    ):
        if receipt.get(field) != ready.get(field):
            raise ReplayError(f"receipt {field} differs from replay-ready evidence")
    job_identity = ready.get("job_identity")
    if not isinstance(job_identity, dict):
        raise ReplayError("replay-ready job identity is malformed")
    serialization = job_identity.get("table_serialization")
    if not isinstance(serialization, str) or sha256_bytes(serialization.encode()) != job_identity.get("table_sha256"):
        raise ReplayError("replay-ready table serialization/hash mismatch")
    if (
        job_identity.get("inventory_sha256") != manifest["inventory_sha256"]
        or job_identity.get("coverage_sha256") != manifest["coverage_sha256"]
    ):
        raise ReplayError("replay-ready inventory/coverage identity mismatch")
    expected_build = {
        key: manifest[key] for key in (
            "repository_commit", "toolchain_identity", "overlay_sha256",
            "generator_sha256", "template_sha256", "cnf_emitter_sha256", "worker_sha256",
            "validator_sha256", "receipt_schema_sha256",
            "aggregate_generator_sha256", "axiom_auditor_sha256",
            "common_sha256", "dispatcher_sha256", "zstd_identity",
        )
    }
    if ready.get("build_identity") != expected_build:
        raise ReplayError("replay-ready build identity differs from manifest")
    worker_runtime = ready.get("worker_runtime")
    if not isinstance(worker_runtime, dict) or (
        worker_runtime.get("instance_type") != manifest["worker_instance_type"]
        or worker_runtime.get("ami_id") != manifest["worker_ami_id"]
        or worker_runtime.get("container_image_digest") != manifest["worker_image_digest"]
        or (worker_runtime.get("region") != manifest["aws_region"]
            and worker_runtime.get("identity_source") != "local-test-backend")
    ):
        raise ReplayError("replay-ready worker runtime differs from manifest")
    if args.object_store_root is not None:
        if (
            worker_runtime.get("identity_source") != "local-test-backend"
            or worker_runtime.get("container_image_digest_source") != "local-test-backend"
        ):
            raise ReplayError("local worker runtime source labels mismatch")
    elif (
        worker_runtime.get("identity_source") != "aws-imdsv2-instance-identity-document"
        or worker_runtime.get("container_image_digest_source")
        != "freight-manifest-assertion-bootstrap-verified"
        or not isinstance(worker_runtime.get("availability_zone"), str)
        or re.fullmatch(re.escape(worker_runtime.get("region", "")) + r"[a-z]",
                        worker_runtime["availability_zone"]) is None
    ):
        raise ReplayError("production worker runtime provenance is malformed")
    work_root = ready.get("work_root")
    if not isinstance(work_root, str) or work_root != str(Path(work_root).resolve()):
        raise ReplayError("replay-ready work root is not absolute and normalized")
    command_job = {
        "tag": tag, "profile": job_identity.get("profile"),
        "local_index": job_identity.get("local_index"),
    }
    if not isinstance(command_job["profile"], int) or not isinstance(command_job["local_index"], int):
        raise ReplayError("replay-ready profile/local index is malformed")
    validate_command_receipts(
        ready.get("commands"), manifest.get("environment_allowlist", []),
        manifest["commands"], receipt_command_bindings(Path(work_root), command_job),
    )
    if ready.get("certificate") != before:
        raise ReplayError("receipt pre-tag identity differs from replay-ready evidence")
    integrity = receipt.get("integrity")
    if args.object_store_root is not None:
        if integrity != {
            "scheme": "local-test-unkeyed", "key_id": "local-test", "value": None,
        }:
            raise ReplayError("local receipt has unexpected integrity declaration")
    elif (
        not isinstance(integrity, dict)
        or integrity.get("scheme") != manifest["receipt_integrity_scheme"]
        or integrity.get("key_id") != manifest["receipt_integrity_key_id"]
        or not isinstance(integrity.get("value"), str)
        or not integrity["value"]
    ):
        raise ReplayError("production receipt lacks selected keyed integrity evidence")
    native_prefix = ready.get("native_axiom_prefix")
    if not isinstance(native_prefix, str) or not native_prefix.startswith("Erdos85.h1V2P"):
        raise ReplayError("replay-ready lacks native axiom ownership prefix")
    foreign_native = [
        axiom for axiom in axioms if axiom not in set(manifest["allowed_axioms"])
        and not axiom.startswith(native_prefix)
    ]
    if foreign_native:
        raise ReplayError("receipt contains a native axiom owned by another leaf")

    if replay_ready_info.get("sha256") != receipt["replay_ready_sha256"]:
        raise ReplayError("receipt replay-ready object hash mismatch")
    live_ledger_key = ledger_key(prefix, tag)
    with tempfile.TemporaryDirectory() as temporary:
        ledger_path = Path(temporary) / "accepted-ledger.json"
        store.download(live_ledger_key, ledger_path)
        ledger = load_json(ledger_path)
    if (
        ledger.get("accepted") is not True
        or ledger.get("tag") != tag
        or ledger.get("receipt_key") != live_receipt_key
        or ledger.get("receipt_sha256") != live_receipt_sha
        or ledger.get("manifest_sha256") != manifest_sha
    ):
        raise ReplayError("terminal ledger does not bind the accepted receipt")


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
    except (OSError, ReplayError) as error:
        print(f"INVALID: {error}", file=sys.stderr)
        return 2
    print("VALID")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
