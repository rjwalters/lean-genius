#!/usr/bin/env python3
"""Publish a durable H1 coverage audit without writing the live campaign."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path


SCHEMA = "erdos85-h1-coverage-audit-snapshot-v2"
OUTPUTS = ("counts.json", "coverage.tsv", "inventory_universe_diff.tsv")
LIVE_RELATIVE = Path("h1fleet/coverage")
STATUS_KEYS = {"certificate-key-conflict", "certified-in-S3", "fleet-in-flight",
               "host-ledgered-UNSAT-not-uploaded", "pending"}
UNKNOWN_KEYS = {"certified_s3", "fleet_v2_claim", "fleet_v2_ledger",
                "fleet_v3_claim", "fleet_v3_ledger", "host_ledger"}
TAG_RE = re.compile(r"[0-9a-f]{16}")
SHA_RE = re.compile(r"[0-9a-f]{64}")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def canonical(value: object) -> bytes:
    return (json.dumps(value, ensure_ascii=True, allow_nan=False,
                       separators=(",", ":"), sort_keys=True) + "\n").encode("ascii")


def regular_absolute(path: Path, label: str) -> None:
    if not path.is_absolute() or path.is_symlink() or not path.is_file():
        raise ValueError(f"{label} must be an absolute regular non-symlink file")


def snapshot_files(root: Path) -> dict[str, dict[str, object]]:
    result = {}
    for name in OUTPUTS:
        path = root / name
        regular_absolute(path, f"snapshot {name}")
        result[name] = {"bytes": path.stat().st_size, "sha256": sha256(path)}
    return result


def is_within(path: Path, parent: Path) -> bool:
    try:
        path.relative_to(parent)
        return True
    except ValueError:
        return False


def validate_summary(counts: dict) -> dict:
    required = {
        "anomalies", "capacity_inventory_total", "capacity_only_error",
        "certificate_key_conflict_count", "certificate_key_conflict_tags",
        "certificate_key_present_tags", "certificate_ledger_valid_tags",
        "certificate_readback_valid_tags", "certificate_ledger_valid_present_tags",
        "certificate_readback_valid_present_tags",
        "certificate_ledger_readback_valid_present_overlap_tags", "conflict_audit_sha256",
        "certified_s3_tags", "cnf_sha_comparable_count",
        "cnf_sha_divergent_count", "cnf_sha_divergent_tags",
        "compact_inventory_total", "compact_only_pre_capacity",
        "fleet_claim_tags", "fleet_ledger_rows", "fleet_unknown_without_cert",
        "host_ledger_rows", "status_counts", "status_total", "unknown_tags",
    }
    if not isinstance(counts, dict) or not required <= set(counts):
        raise ValueError("reconciler counts schema is incomplete")
    statuses = counts["status_counts"]
    integer_fields = ("capacity_inventory_total", "capacity_only_error",
        "certificate_key_conflict_count", "certificate_key_present_tags",
        "certificate_ledger_valid_tags", "certificate_readback_valid_tags",
        "certificate_ledger_valid_present_tags", "certificate_readback_valid_present_tags",
        "certificate_ledger_readback_valid_present_overlap_tags",
        "certified_s3_tags", "cnf_sha_comparable_count",
        "cnf_sha_divergent_count", "compact_inventory_total",
        "compact_only_pre_capacity", "fleet_claim_tags", "fleet_ledger_rows",
        "fleet_unknown_without_cert", "host_ledger_rows", "status_total")
    if any(type(counts[field]) is not int or counts[field] < 0
           for field in integer_fields):
        raise ValueError("reconciler integer summary fields are malformed")
    if (not isinstance(statuses, dict) or set(statuses) != STATUS_KEYS
            or any(type(value) is not int or value < 0 for value in statuses.values())):
        raise ValueError("reconciler status partition is malformed")
    unknown = counts["unknown_tags"]
    if (not isinstance(unknown, dict) or set(unknown) != UNKNOWN_KEYS
            or any(value != [] for value in unknown.values())):
        raise ValueError("reconciler unknown-tag partition is malformed")
    conflicts = counts["certificate_key_conflict_tags"]
    expected_anomalies = ({"certificate-key-present-without-valid-upload-ledger":
                           counts["certificate_key_conflict_count"]}
                          if counts["certificate_key_conflict_count"] else {})
    if (not isinstance(conflicts, list)
            or len(conflicts) != counts["certificate_key_conflict_count"]
            or conflicts != sorted(set(conflicts))
            or any(not isinstance(tag, str) or not TAG_RE.fullmatch(tag) for tag in conflicts)
            or counts["certificate_key_present_tags"] != (
                counts["certified_s3_tags"] + counts["certificate_key_conflict_count"])
            or counts["certificate_ledger_valid_present_tags"]
                + counts["certificate_readback_valid_present_tags"]
                - counts["certificate_ledger_readback_valid_present_overlap_tags"]
                != counts["certified_s3_tags"]
            or counts["certificate_ledger_valid_present_tags"]
                > counts["certificate_ledger_valid_tags"]
            or counts["certificate_readback_valid_present_tags"]
                > counts["certificate_readback_valid_tags"]
            or counts["certificate_ledger_readback_valid_present_overlap_tags"]
                > min(counts["certificate_ledger_valid_present_tags"],
                      counts["certificate_readback_valid_present_tags"])
            or not isinstance(counts["conflict_audit_sha256"], str)
            or (counts["conflict_audit_sha256"] != ""
                and SHA_RE.fullmatch(counts["conflict_audit_sha256"]) is None)
            or statuses["certificate-key-conflict"] != counts["certificate_key_conflict_count"]
            or counts["anomalies"] != expected_anomalies
            or counts["capacity_inventory_total"] != 13_351
            or counts["status_total"] != 13_351
            or sum(statuses.values()) != 13_351
            or counts["compact_inventory_total"] != 13_541
            or counts["compact_only_pre_capacity"] != 190
            or counts["capacity_only_error"] != 0
            or counts["cnf_sha_divergent_count"] != 0
            or counts["cnf_sha_divergent_tags"] != []):
        raise ValueError("H1 reconciliation integrity gate failed")
    return {
        "anomalies": counts["anomalies"],
        "certificate_key_conflict_count": counts["certificate_key_conflict_count"],
        "certificate_key_conflict_tags": conflicts,
        "certificate_key_present": counts["certificate_key_present_tags"],
        "certificate_ledger_valid": counts["certificate_ledger_valid_tags"],
        "certificate_readback_valid": counts["certificate_readback_valid_tags"],
        "certificate_ledger_valid_present": counts["certificate_ledger_valid_present_tags"],
        "certificate_readback_valid_present": counts["certificate_readback_valid_present_tags"],
        "certificate_ledger_readback_valid_present_overlap":
            counts["certificate_ledger_readback_valid_present_overlap_tags"],
        "conflict_audit_sha256": counts["conflict_audit_sha256"],
        "certified": statuses.get("certified-in-S3", 0),
        "cnf_sha_comparable_count": counts["cnf_sha_comparable_count"],
        "cnf_sha_divergent_count": counts["cnf_sha_divergent_count"],
        "fleet_claim_tags": counts["fleet_claim_tags"],
        "fleet_in_flight": statuses.get("fleet-in-flight", 0),
        "fleet_ledger_rows": counts["fleet_ledger_rows"],
        "fleet_unknown_without_cert": counts["fleet_unknown_without_cert"],
        "host_ledger_rows": counts["host_ledger_rows"],
        "pending": statuses.get("pending", 0),
        "status_total": counts["status_total"],
        "unknown_tags": counts["unknown_tags"],
    }


def copy_host_inputs(campaign: Path, mirror: Path,
                     manifest_hashes: dict[str, str]) -> dict:
    source_grind = campaign / "h1grind"
    target_grind = mirror / "h1grind"
    (target_grind / "orbits").mkdir(parents=True)
    for name in ("all_even_manifest.tsv", "complement_manifest.tsv"):
        source = source_grind / name
        destination = target_grind / name
        destination.write_bytes(source.read_bytes())
        if sha256(destination) != manifest_hashes[name]:
            raise ValueError(f"campaign input changed while staging {name}")
    ledger_identity = []
    for source in sorted((source_grind / "orbits").glob("*/ledger.line")):
        relative = source.relative_to(source_grind)
        destination = target_grind / relative
        destination.parent.mkdir()
        before = source.read_bytes()
        destination.write_bytes(before)
        after = source.read_bytes()
        if before != after:
            raise ValueError(f"host ledger changed while staging: {relative}")
        ledger_identity.append({"bytes": len(before), "path": str(relative),
                                "sha256": hashlib.sha256(before).hexdigest()})
    return {"count": len(ledger_identity),
            "identity_sha256": hashlib.sha256(canonical(ledger_identity)).hexdigest()}


def publish_snapshot(*, campaign: Path, reconciler: Path,
                     reconciler_sha256: str, all_even_manifest: Path,
                     complement_manifest: Path, compact_inventory: Path,
                     aws_profile: str, bucket: str, s3_prefix: str,
                     output: Path, conflict_audit: Path | None = None,
                     conflict_audit_sha256: str | None = None,
                     timestamp: str | None = None) -> dict:
    if not campaign.is_absolute() or campaign.is_symlink() or not campaign.is_dir():
        raise ValueError("campaign must be an absolute non-symlink directory")
    for path, label in ((reconciler, "reconciler"),
                        (all_even_manifest, "all-even manifest"),
                        (complement_manifest, "complement manifest"),
                        (compact_inventory, "compact inventory")):
        regular_absolute(path, label)
    if sha256(reconciler) != reconciler_sha256:
        raise ValueError("reconciler hash mismatch")
    if not output.is_absolute() or output.exists() or output.is_symlink():
        raise ValueError("output must be an absent absolute path")
    if output.parent.is_symlink() or not output.parent.is_dir():
        raise ValueError("output parent must be an existing non-symlink directory")
    if is_within(output.resolve(strict=False), campaign.resolve()):
        raise ValueError("audit output must be outside the live campaign")
    if not aws_profile or not bucket or not s3_prefix:
        raise ValueError("AWS profile/bucket/prefix must be nonempty")
    if (conflict_audit is None) != (conflict_audit_sha256 is None):
        raise ValueError("conflict audit path and SHA-256 must be supplied together")
    if conflict_audit is not None:
        regular_absolute(conflict_audit, "conflict audit")
        if SHA_RE.fullmatch(conflict_audit_sha256) is None \
                or sha256(conflict_audit) != conflict_audit_sha256:
            raise ValueError("conflict audit hash mismatch")
    if all_even_manifest != campaign / "h1grind/all_even_manifest.tsv":
        raise ValueError("all-even manifest is not the canonical campaign input")
    if complement_manifest != campaign / "h1grind/complement_manifest.tsv":
        raise ValueError("complement manifest is not the canonical campaign input")

    live_root = campaign / LIVE_RELATIVE
    live_before = snapshot_files(live_root)
    publisher = Path(__file__).resolve()
    captured = {
        "all_even_manifest.tsv": sha256(all_even_manifest),
        "complement_manifest.tsv": sha256(complement_manifest),
        "compact_inventory": sha256(compact_inventory),
        "publisher": sha256(publisher),
        "reconciler": sha256(reconciler),
    }
    if conflict_audit is not None:
        captured["conflict_audit"] = sha256(conflict_audit)
    if captured["reconciler"] != reconciler_sha256:
        raise ValueError("reconciler changed before staging")
    staging = Path(tempfile.mkdtemp(prefix=".h1-audit-stage.", dir=output.parent))
    try:
        mirror = staging / "campaign"
        (mirror / "h1fleet").mkdir(parents=True)
        host_ledgers = copy_host_inputs(campaign, mirror, captured)
        staged_tools = staging / "tools"; staged_tools.mkdir()
        staged_reconciler = staged_tools / "reconcile_coverage.py"
        staged_compact = staged_tools / "h1_orbit_inventory.compact"
        staged_reconciler.write_bytes(reconciler.read_bytes())
        staged_compact.write_bytes(compact_inventory.read_bytes())
        staged_conflict = None
        if conflict_audit is not None:
            staged_conflict = staged_tools / "conflict-readback-audit.json"
            staged_conflict.write_bytes(conflict_audit.read_bytes())
        if (sha256(staged_reconciler) != captured["reconciler"]
                or sha256(staged_compact) != captured["compact_inventory"]):
            raise ValueError("pinned tool/input changed while staging")
        if staged_conflict is not None and sha256(staged_conflict) != captured["conflict_audit"]:
            raise ValueError("pinned conflict audit changed while staging")
        command = [sys.executable, str(staged_reconciler), "--campaign", str(mirror),
                   "--aws-profile", aws_profile, "--bucket", bucket,
                   "--s3-prefix", s3_prefix,
                   "--compact-inventory", str(staged_compact)]
        if staged_conflict is not None:
            command += ["--conflict-audit", str(staged_conflict),
                        "--conflict-audit-sha256", conflict_audit_sha256]
        result = subprocess.run(command, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True)
        if result.returncode:
            raise ValueError(f"reconciler failed rc={result.returncode}: {result.stdout[-2000:]}")
        staged_root = mirror / LIVE_RELATIVE
        staged_outputs = snapshot_files(staged_root)
        counts = json.loads((staged_root / "counts.json").read_text())
        summary = validate_summary(counts)
        live_after = snapshot_files(live_root)
        if live_after != live_before:
            raise ValueError("live campaign coverage changed during read-only audit")
        originals_after = {
            "all_even_manifest.tsv": sha256(all_even_manifest),
            "complement_manifest.tsv": sha256(complement_manifest),
            "compact_inventory": sha256(compact_inventory),
            "publisher": sha256(publisher),
            "reconciler": sha256(reconciler),
        }
        if conflict_audit is not None:
            originals_after["conflict_audit"] = sha256(conflict_audit)
        if originals_after != captured:
            raise ValueError("a pinned original changed during reconciliation")

        output.mkdir(parents=False, exist_ok=False)
        for name in OUTPUTS:
            destination = output / name
            destination.write_bytes((staged_root / name).read_bytes())
            with destination.open("rb") as stream:
                os.fsync(stream.fileno())
        retained = snapshot_files(output)
        if retained != staged_outputs:
            raise ValueError("retained audit output differs from reconciler output")
        receipt = {
            "aws": {"bucket": bucket, "profile": aws_profile,
                    "s3_prefix": s3_prefix},
            "inputs": {
                "all_even_manifest": str(all_even_manifest),
                "all_even_manifest_sha256": captured["all_even_manifest.tsv"],
                "compact_inventory": str(compact_inventory),
                "compact_inventory_sha256": captured["compact_inventory"],
                "complement_manifest": str(complement_manifest),
                "complement_manifest_sha256": captured["complement_manifest.tsv"],
                "publisher": str(publisher),
                "publisher_sha256": captured["publisher"],
                "reconciler": str(reconciler),
                "reconciler_sha256": reconciler_sha256,
                "conflict_audit": str(conflict_audit) if conflict_audit is not None else None,
                "conflict_audit_sha256": conflict_audit_sha256,
            },
            "live_campaign": str(campaign),
            "host_ledger_snapshot": host_ledgers,
            "live_named_output_paths": {
                name: str(live_root / name) for name in OUTPUTS},
            "live_named_outputs_mutated": False,
            "live_outputs_before": live_before,
            "live_outputs_after": live_after,
            "outputs": retained,
            "schema": SCHEMA,
            "summary": summary,
            "timestamp_utc": timestamp or datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        }
        receipt_path = output / "receipt.json"
        receipt_path.write_bytes(canonical(receipt))
        with receipt_path.open("rb") as stream:
            os.fsync(stream.fileno())
        descriptor = os.open(output, os.O_RDONLY)
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
        return receipt
    finally:
        shutil.rmtree(staging)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--campaign", type=Path, required=True)
    parser.add_argument("--reconciler", type=Path, required=True)
    parser.add_argument("--reconciler-sha256", required=True)
    parser.add_argument("--all-even-manifest", type=Path, required=True)
    parser.add_argument("--complement-manifest", type=Path, required=True)
    parser.add_argument("--compact-inventory", type=Path, required=True)
    parser.add_argument("--conflict-audit", type=Path)
    parser.add_argument("--conflict-audit-sha256")
    parser.add_argument("--aws-profile", required=True)
    parser.add_argument("--bucket", required=True)
    parser.add_argument("--s3-prefix", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    receipt = publish_snapshot(
        campaign=args.campaign, reconciler=args.reconciler,
        reconciler_sha256=args.reconciler_sha256,
        all_even_manifest=args.all_even_manifest,
        complement_manifest=args.complement_manifest,
        compact_inventory=args.compact_inventory,
        conflict_audit=args.conflict_audit,
        conflict_audit_sha256=args.conflict_audit_sha256,
        aws_profile=args.aws_profile, bucket=args.bucket,
        s3_prefix=args.s3_prefix, output=args.output)
    print(f"WROTE {args.output} receipt_sha256={sha256(args.output / 'receipt.json')} "
          f"certified={receipt['summary']['certified']} pending={receipt['summary']['pending']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
