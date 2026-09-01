#!/usr/bin/env python3
"""Emit a fail-closed H1 queue for bounded UNKNOWN retry in a new namespace.

The v2 workers intentionally never revisit a tag once its ledger or claim
exists.  This tool preserves that immutable evidence and derives a separate
queue containing exactly pending, uncertified, claimed rows whose fleet verdict
is UNKNOWN.  A canonical key classified as present is outside this ordinary
retry lane even if later audit finds it corrupt; preserving and superseding
such an object requires the separately reviewed repair namespace.
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


TAG_RE = re.compile(r"[0-9a-f]{16}")
PROFILE_NAMES = ("BBBB", "ABBB", "AABB", "AAAB", "AAAA")
V2_CLAIM_PREFIX = "sat49/campaign-20260825/h1-fleet-v2/claims/"


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def stable_read(path: Path) -> bytes:
    """Read one regular-file snapshot and reject path replacement during the read."""
    before = path.stat()
    with path.open("rb") as stream:
        opened_before = os.fstat(stream.fileno())
        data = stream.read()
        opened_after = os.fstat(stream.fileno())
    after = path.stat()
    identity = lambda value: (
        value.st_dev, value.st_ino, value.st_size, value.st_mtime_ns
    )
    if not stat.S_ISREG(opened_before.st_mode) or not (
        identity(before) == identity(opened_before)
        == identity(opened_after) == identity(after)
    ):
        raise ValueError(f"{path}: input changed while being read")
    return data


def atomic_write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp.{os.getpid()}")
    try:
        temporary.write_bytes(data)
        # link(2) is an atomic create-only publication: it fails if the final
        # name already exists and therefore cannot silently replace evidence.
        os.link(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def read_jobs_bytes(path: Path, data: bytes) -> dict[str, tuple[int, str, int, str]]:
    jobs = {}
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ValueError(f"{path}: jobs are not UTF-8") from error
    for line_number, raw in enumerate(text.splitlines(), 1):
        fields = raw.split("\t")
        if len(fields) != 4 or not TAG_RE.fullmatch(fields[0]):
            raise ValueError(f"{path}:{line_number}: malformed four-field job")
        tag, profile_text, family, index_text = fields
        try:
            profile, local_index = int(profile_text), int(index_text)
        except ValueError as error:
            raise ValueError(f"{path}:{line_number}: nonnumeric job key") from error
        if (
            profile not in range(5) or family != PROFILE_NAMES[profile]
            or local_index < 0 or tag in jobs
        ):
            raise ValueError(f"{path}:{line_number}: invalid or duplicate job")
        jobs[tag] = (profile, family, local_index, raw)
    if not jobs:
        raise ValueError("jobs file is empty")
    return jobs


def read_jobs(path: Path) -> dict[str, tuple[int, str, int, str]]:
    return read_jobs_bytes(path, stable_read(path))


def read_orphan_tags_bytes(path: Path, data: bytes) -> set[str]:
    try:
        lines = data.decode("ascii").splitlines()
    except UnicodeDecodeError as error:
        raise ValueError(f"{path}: orphan claim evidence is not ASCII") from error
    tags = []
    for line_number, raw in enumerate(lines, 1):
        if not raw.startswith(V2_CLAIM_PREFIX):
            raise ValueError(f"{path}:{line_number}: wrong orphan claim prefix")
        tag = raw[len(V2_CLAIM_PREFIX):]
        if not TAG_RE.fullmatch(tag):
            raise ValueError(f"{path}:{line_number}: malformed orphan claim key")
        tags.append(tag)
    if not tags or tags != sorted(set(tags)):
        raise ValueError(f"{path}: orphan claim keys must be nonempty, unique, and sorted")
    return set(tags)


def select_unknowns_bytes(
    coverage: Path, data: bytes, jobs: dict[str, tuple[int, str, int, str]],
    orphan_tags: set[str] | None = None,
) -> list[str]:
    orphan_tags = orphan_tags or set()
    selected: list[str] = []
    seen: set[str] = set()
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ValueError(f"{coverage}: coverage is not UTF-8") from error
    with io.StringIO(text, newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        required = {
            "tag", "profile", "family", "local_index", "status",
            "certified_s3", "fleet_v2_claim", "fleet_v2_verdict",
            "fleet_v3_claim", "fleet_v3_verdict",
        }
        if not reader.fieldnames or not required.issubset(reader.fieldnames):
            raise ValueError(f"{coverage}: missing required coverage columns")
        for line_number, row in enumerate(reader, 2):
            tag = row["tag"]
            if not TAG_RE.fullmatch(tag) or tag in seen:
                raise ValueError(f"{coverage}:{line_number}: invalid or duplicate tag")
            seen.add(tag)
            is_retry = (
                row["status"] == "pending" and row["certified_s3"] == "0"
                and row["fleet_v2_claim"] == "1"
                and row["fleet_v2_verdict"] == "UNKNOWN"
                and row["fleet_v3_claim"] == "0"
                and row["fleet_v3_verdict"] == ""
            )
            is_orphan = tag in orphan_tags
            if is_orphan and not (
                row["status"] == "pending" and row["certified_s3"] == "0"
                and row["fleet_v2_claim"] == "0" and row["fleet_v2_verdict"] == ""
                and row["fleet_v3_claim"] == "0" and row["fleet_v3_verdict"] == ""
            ):
                raise ValueError(
                    f"{coverage}:{line_number}: orphan tag has acquired terminal or claim evidence"
                )
            if is_retry or is_orphan:
                if tag not in jobs:
                    raise ValueError(f"{coverage}:{line_number}: retry tag absent from jobs")
                profile, family, local_index, raw_job = jobs[tag]
                if (
                    row["profile"] != str(profile) or row["family"] != family
                    or row["local_index"] != str(local_index)
                ):
                    raise ValueError(
                        f"{coverage}:{line_number}: coverage/job identity mismatch"
                    )
                selected.append(raw_job)
    unknown_jobs = jobs.keys() - seen
    if unknown_jobs:
        raise ValueError(f"jobs contain {len(unknown_jobs)} tag(s) absent from coverage")
    missing_orphans = orphan_tags - seen
    if missing_orphans:
        raise ValueError(f"orphan evidence has {len(missing_orphans)} tag(s) absent from coverage")
    return sorted(selected)


def select_unknowns(
    coverage: Path, jobs: dict[str, tuple[int, str, int, str]]
) -> list[str]:
    return select_unknowns_bytes(coverage, stable_read(coverage), jobs)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--coverage", type=Path, required=True)
    parser.add_argument("--jobs", type=Path, required=True)
    parser.add_argument("--orphan-claims", type=Path, required=True)
    parser.add_argument("--orphan-claims-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--receipt-output", type=Path, required=True)
    args = parser.parse_args()
    if args.output == args.receipt_output:
        raise ValueError("output and receipt output must be distinct")
    for output in (args.output, args.receipt_output):
        if output.exists():
            raise FileExistsError(f"refusing to replace existing output: {output}")
    jobs_data = stable_read(args.jobs)
    coverage_data = stable_read(args.coverage)
    orphan_data = stable_read(args.orphan_claims)
    if (not re.fullmatch(r"[0-9a-f]{64}", args.orphan_claims_sha256)
            or sha256_bytes(orphan_data) != args.orphan_claims_sha256):
        raise ValueError(f"{args.orphan_claims}: orphan claim evidence SHA-256 mismatch")
    jobs = read_jobs_bytes(args.jobs, jobs_data)
    orphan_tags = read_orphan_tags_bytes(args.orphan_claims, orphan_data)
    rows = select_unknowns_bytes(args.coverage, coverage_data, jobs, orphan_tags)
    output_data = ("\n".join(rows) + "\n").encode()
    atomic_write(args.output, output_data)
    counts = Counter(int(row.split("\t", 2)[1]) for row in rows)
    orphan_counts = Counter(jobs[tag][0] for tag in orphan_tags)
    receipt = {
        "schema": "erdos85-h1-v3-final-retry-queue-v2",
        "coverage_sha256": sha256_bytes(coverage_data),
        "jobs_sha256": sha256_bytes(jobs_data),
        "orphan_claims_sha256": sha256_bytes(orphan_data),
        "output_sha256": sha256_bytes(output_data),
        "rows": len(rows),
        "unknown_rows": len(rows) - len(orphan_tags),
        "orphan_rows": len(orphan_tags),
        "profile_counts": [counts[index] for index in range(5)],
        "orphan_profile_counts": [orphan_counts[index] for index in range(5)],
        "unknown_selection": {
            "status": "pending", "certified_s3": "0",
            "fleet_v2_claim": "1", "fleet_v2_verdict": "UNKNOWN",
            "fleet_v3_claim": "0", "fleet_v3_verdict": "",
        },
        "orphan_selection": {
            "status": "pending", "certified_s3": "0",
            "fleet_v2_claim": "0", "fleet_v2_verdict": "",
            "fleet_v3_claim": "0", "fleet_v3_verdict": "",
            "evidence_key_prefix": V2_CLAIM_PREFIX,
        },
    }
    atomic_write(
        args.receipt_output,
        (json.dumps(receipt, indent=2, sort_keys=True) + "\n").encode(),
    )
    print(json.dumps(receipt, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
