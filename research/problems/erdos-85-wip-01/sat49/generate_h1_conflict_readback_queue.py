#!/usr/bin/env python3
"""Build a pinned audit queue for H1 canonical certificate-key conflicts.

This queue is readback-only.  It neither selects repair work nor treats object
presence as certificate validity.  Every job is derived from a conflict row in
an immutable coverage-audit-v2 snapshot and names the exact canonical object
whose bytes must be independently validated.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
import os
import re
import stat
from collections import Counter
from pathlib import Path


AUDIT_SCHEMA = "erdos85-h1-coverage-audit-snapshot-v2"
QUEUE_SCHEMA = "erdos85-h1-conflict-readback-queue-v1"
TAG_RE = re.compile(r"[0-9a-f]{16}")
PROFILE_NAMES = ("BBBB", "ABBB", "AABB", "AAAB", "AAAA")
CERTIFICATE_PREFIX = "sat49/campaign-20260825/h1/"
CERTIFICATE_SUFFIX = ".compact.lrat.gz"
COVERAGE_COLUMNS = (
    "tag", "profile", "family", "local_index", "inventory_source", "status",
    "certificate_key_present", "certificate_ledger_valid", "certificate_key_conflict",
    "certified_s3", "host_unsat", "host_cnf_sha256", "host_verdict",
    "fleet_claim", "fleet_cnf_sha256", "fleet_verdict", "cnf_sha_divergent",
    "fleet_v2_claim", "fleet_v2_cnf_sha256", "fleet_v2_verdict",
    "fleet_v3_claim", "fleet_v3_cnf_sha256", "fleet_v3_verdict",
)
AUDIT_RECEIPT_KEYS = {
    "aws", "inputs", "live_campaign", "host_ledger_snapshot",
    "live_named_output_paths", "live_named_outputs_mutated", "live_outputs_before",
    "live_outputs_after", "outputs", "schema", "summary", "timestamp_utc",
}
AUDIT_SUMMARY_KEYS = {
    "anomalies", "certificate_key_conflict_count", "certificate_key_conflict_tags",
    "certificate_key_present", "certificate_ledger_valid", "certified",
    "cnf_sha_comparable_count", "cnf_sha_divergent_count", "fleet_claim_tags",
    "fleet_in_flight", "fleet_ledger_rows", "fleet_unknown_without_cert",
    "host_ledger_rows", "pending", "status_total", "unknown_tags",
}
STATUSES = {
    "certificate-key-conflict", "certified-in-S3", "fleet-in-flight",
    "host-ledgered-UNSAT-not-uploaded", "pending",
}


def canonical(value: object) -> bytes:
    return (json.dumps(value, ensure_ascii=True, allow_nan=False,
                       separators=(",", ":"), sort_keys=True) + "\n").encode("ascii")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def stable_snapshot(path: Path) -> tuple[bytes, tuple[int, int, int, int]]:
    before = path.stat()
    with path.open("rb") as stream:
        opened_before = os.fstat(stream.fileno())
        data = stream.read()
        opened_after = os.fstat(stream.fileno())
    after = path.stat()
    identify = lambda value: (
        value.st_dev, value.st_ino, value.st_size, value.st_mtime_ns
    )
    if not stat.S_ISREG(opened_before.st_mode) or not (
        identify(before) == identify(opened_before)
        == identify(opened_after) == identify(after)
    ):
        raise ValueError(f"{path}: input changed while being read")
    return data, identify(after)


def stable_read(path: Path) -> bytes:
    return stable_snapshot(path)[0]


def revalidate(path: Path, expected: tuple[int, int, int, int]) -> None:
    current = path.stat()
    identity = (current.st_dev, current.st_ino, current.st_size, current.st_mtime_ns)
    if not stat.S_ISREG(current.st_mode) or identity != expected:
        raise ValueError(f"{path}: input changed before output publication")


def create_only(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp.{os.getpid()}")
    try:
        temporary.write_bytes(data)
        os.link(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def certificate_key(tag: str) -> str:
    if not TAG_RE.fullmatch(tag):
        raise ValueError(f"invalid H1 tag: {tag!r}")
    return f"{CERTIFICATE_PREFIX}{tag}{CERTIFICATE_SUFFIX}"


def validate_certificate_key(tag: str, key: str) -> None:
    if key != certificate_key(tag):
        raise ValueError(f"{tag}: certificate key is not exact canonical key")


def parse_audit_receipt(path: Path, data: bytes, expected_sha256: str,
                        coverage_data: bytes) -> tuple[list[str], dict]:
    if not re.fullmatch(r"[0-9a-f]{64}", expected_sha256):
        raise ValueError("invalid expected audit receipt SHA-256")
    if sha256_bytes(data) != expected_sha256:
        raise ValueError(f"{path}: audit receipt SHA-256 mismatch")
    try:
        receipt = json.loads(data)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValueError(f"{path}: malformed audit receipt") from error
    if (not isinstance(receipt, dict) or set(receipt) != AUDIT_RECEIPT_KEYS
            or receipt.get("schema") != AUDIT_SCHEMA or canonical(receipt) != data):
        raise ValueError(f"{path}: unsupported audit receipt schema")
    if (receipt["live_named_outputs_mutated"] is not False
            or not isinstance(receipt["live_campaign"], str)
            or not isinstance(receipt["timestamp_utc"], str)
            or any(not isinstance(receipt[name], dict) for name in (
                "aws", "inputs", "host_ledger_snapshot", "live_named_output_paths",
                "live_outputs_before", "live_outputs_after"))):
        raise ValueError(f"{path}: malformed audit receipt top-level fields")
    outputs = receipt.get("outputs")
    if not isinstance(outputs, dict) or set(outputs) != {
            "counts.json", "coverage.tsv", "inventory_universe_diff.tsv"}:
        raise ValueError(f"{path}: malformed audit output identities")
    for name, identity in outputs.items():
        if (not isinstance(identity, dict) or set(identity) != {"bytes", "sha256"}
                or type(identity["bytes"]) is not int or identity["bytes"] < 0
                or not isinstance(identity["sha256"], str)
                or not re.fullmatch(r"[0-9a-f]{64}", identity["sha256"])):
            raise ValueError(f"{path}: malformed identity for {name}")
    coverage = outputs.get("coverage.tsv") if isinstance(outputs, dict) else None
    if (not isinstance(coverage, dict)
            or coverage.get("sha256") != sha256_bytes(coverage_data)
            or coverage.get("bytes") != len(coverage_data)):
        raise ValueError(f"{path}: coverage identity mismatch")
    summary = receipt.get("summary")
    if not isinstance(summary, dict) or set(summary) != AUDIT_SUMMARY_KEYS:
        raise ValueError(f"{path}: malformed audit summary")
    integer_summary = AUDIT_SUMMARY_KEYS - {
        "anomalies", "certificate_key_conflict_tags", "unknown_tags"}
    if any(type(summary[name]) is not int or summary[name] < 0
           for name in integer_summary):
        raise ValueError(f"{path}: malformed audit summary counts")
    tags = summary.get("certificate_key_conflict_tags")
    count = summary.get("certificate_key_conflict_count")
    total = summary.get("status_total")
    if (not isinstance(tags, list) or tags != sorted(set(tags))
            or any(not isinstance(tag, str) or not TAG_RE.fullmatch(tag) for tag in tags)
            or type(count) is not int or count != len(tags)
            or type(total) is not int or total < count):
        raise ValueError(f"{path}: malformed conflict summary")
    if (summary.get("anomalies") != (
            {"certificate-key-present-without-valid-upload-ledger": count}
            if count else {})
            or summary.get("unknown_tags") != {
                "certified_s3": [], "fleet_v2_claim": [], "fleet_v2_ledger": [],
                "fleet_v3_claim": [], "fleet_v3_ledger": [], "host_ledger": []}):
        raise ValueError(f"{path}: audit anomaly/unknown summary mismatch")
    return tags, summary


def parse_coverage(path: Path, data: bytes, expected_tags: list[str],
                   summary: dict) -> list[dict[str, object]]:
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ValueError(f"{path}: coverage is not UTF-8") from error
    selected = []
    seen = set()
    with io.StringIO(text, newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        if reader.fieldnames != list(COVERAGE_COLUMNS):
            raise ValueError(f"{path}: coverage header is not exact v2 schema")
        for line_number, row in enumerate(reader, 2):
            tag = row["tag"]
            if not TAG_RE.fullmatch(tag) or tag in seen:
                raise ValueError(f"{path}:{line_number}: invalid or duplicate tag")
            seen.add(tag)
            try:
                profile = int(row["profile"])
                local_index = int(row["local_index"])
            except ValueError as error:
                raise ValueError(f"{path}:{line_number}: nonnumeric coordinates") from error
            if (profile not in range(5) or row["family"] != PROFILE_NAMES[profile]
                    or local_index < 0):
                raise ValueError(f"{path}:{line_number}: invalid profile coordinates")
            if (row["status"] not in STATUSES
                    or any(row[name] not in {"0", "1"} for name in (
                        "certificate_key_present", "certificate_ledger_valid",
                        "certificate_key_conflict", "certified_s3"))):
                raise ValueError(f"{path}:{line_number}: invalid status or certificate flags")
            if row["status"] == "certificate-key-conflict":
                if (row["certificate_key_present"] != "1"
                        or row["certificate_ledger_valid"] != "0"
                        or row["certificate_key_conflict"] != "1"
                        or row["certified_s3"] != "0"):
                    raise ValueError(f"{path}:{line_number}: inconsistent conflict flags")
                key = certificate_key(tag)
                validate_certificate_key(tag, key)
                selected.append({
                    "certificate_key": key,
                    "family": row["family"],
                    "local_index": local_index,
                    "profile": profile,
                    "tag": tag,
                })
            elif row["certificate_key_conflict"] == "1":
                raise ValueError(f"{path}:{line_number}: conflict flag/status mismatch")
    if len(seen) != summary["status_total"]:
        raise ValueError(f"{path}: coverage row count differs from audit receipt")
    selected.sort(key=lambda job: job["tag"])
    actual_tags = [job["tag"] for job in selected]
    if actual_tags != expected_tags:
        raise ValueError(f"{path}: conflict rows differ from audit receipt")
    if not selected:
        raise ValueError(f"{path}: audit contains no certificate-key conflicts")
    rows = list(csv.DictReader(io.StringIO(text, newline=""), delimiter="\t"))
    statuses = Counter(row["status"] for row in rows)
    effective_verdicts = [row["fleet_v3_verdict"] or row["fleet_v2_verdict"] for row in rows]
    shas = [tuple(value for value in (
        row["host_cnf_sha256"], row["fleet_v2_cnf_sha256"], row["fleet_v3_cnf_sha256"]
    ) if value) for row in rows]
    computed = {
        "certificate_key_conflict_count": statuses["certificate-key-conflict"],
        "certificate_key_present": sum(row["certificate_key_present"] == "1" for row in rows),
        "certificate_ledger_valid": sum(row["certificate_ledger_valid"] == "1" for row in rows),
        "certified": statuses["certified-in-S3"],
        "cnf_sha_comparable_count": sum(len(values) >= 2 for values in shas),
        "cnf_sha_divergent_count": sum(len(set(values)) > 1 for values in shas),
        "fleet_claim_tags": sum(row["fleet_claim"] == "1" for row in rows),
        "fleet_in_flight": statuses["fleet-in-flight"],
        "fleet_ledger_rows": sum(bool(row["fleet_v2_verdict"] or row["fleet_v3_verdict"])
                                 for row in rows),
        "fleet_unknown_without_cert": sum(
            verdict == "UNKNOWN" and row["certificate_key_present"] == "0"
            for row, verdict in zip(rows, effective_verdicts, strict=True)),
        "host_ledger_rows": sum(bool(row["host_verdict"]) for row in rows),
        "pending": statuses["pending"],
        "status_total": len(rows),
    }
    if any(summary.get(key) != value for key, value in computed.items()):
        raise ValueError(f"{path}: coverage counts differ from audit summary")
    return selected


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit-receipt", type=Path, required=True)
    parser.add_argument("--audit-receipt-sha256", required=True)
    parser.add_argument("--coverage", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--receipt-output", type=Path, required=True)
    args = parser.parse_args()
    if args.output == args.receipt_output:
        raise ValueError("output and receipt output must be distinct")
    for output in (args.output, args.receipt_output):
        if output.exists():
            raise FileExistsError(f"refusing to replace existing output: {output}")
    coverage_data, coverage_identity = stable_snapshot(args.coverage)
    audit_data, audit_identity = stable_snapshot(args.audit_receipt)
    expected_tags, summary = parse_audit_receipt(
        args.audit_receipt, audit_data, args.audit_receipt_sha256, coverage_data)
    jobs = parse_coverage(args.coverage, coverage_data, expected_tags, summary)
    output_data = b"".join(canonical(job) for job in jobs)
    revalidate(args.coverage, coverage_identity)
    revalidate(args.audit_receipt, audit_identity)
    create_only(args.output, output_data)
    counts = Counter(job["profile"] for job in jobs)
    receipt = {
        "audit_receipt_sha256": sha256_bytes(audit_data),
        "certificate_prefix": CERTIFICATE_PREFIX,
        "conflict_tags": expected_tags,
        "coverage_sha256": sha256_bytes(coverage_data),
        "output_sha256": sha256_bytes(output_data),
        "profile_counts": [counts[index] for index in range(5)],
        "rows": len(jobs),
        "schema": QUEUE_SCHEMA,
        "selection_status": "certificate-key-conflict",
    }
    revalidate(args.coverage, coverage_identity)
    revalidate(args.audit_receipt, audit_identity)
    create_only(args.receipt_output, canonical(receipt))
    print(canonical(receipt).decode("ascii"), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
