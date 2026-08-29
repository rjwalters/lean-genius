#!/usr/bin/env python3
"""Emit a fail-closed H1 queue for bounded UNKNOWN retry in a new namespace.

The v2 workers intentionally never revisit a tag once its ledger or claim
exists.  This tool preserves that immutable evidence and derives a separate
queue containing exactly pending, uncertified, claimed rows whose fleet verdict
is UNKNOWN.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import re
from collections import Counter
from pathlib import Path


TAG_RE = re.compile(r"[0-9a-f]{16}")
PROFILE_NAMES = ("BBBB", "ABBB", "AABB", "AAAB", "AAAA")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def atomic_write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp.{os.getpid()}")
    try:
        temporary.write_bytes(data)
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


def read_jobs(path: Path) -> dict[str, tuple[int, str, int, str]]:
    jobs = {}
    for line_number, raw in enumerate(path.read_text().splitlines(), 1):
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


def select_unknowns(coverage: Path, jobs: dict[str, tuple[int, str, int, str]]) -> list[str]:
    selected: list[str] = []
    seen: set[str] = set()
    with coverage.open(newline="") as stream:
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
            if is_retry:
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
    return sorted(selected)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--coverage", type=Path, required=True)
    parser.add_argument("--jobs", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--receipt-output", type=Path, required=True)
    args = parser.parse_args()
    jobs = read_jobs(args.jobs)
    rows = select_unknowns(args.coverage, jobs)
    atomic_write(args.output, ("\n".join(rows) + "\n").encode())
    counts = Counter(int(row.split("\t", 2)[1]) for row in rows)
    receipt = {
        "schema": "erdos85-h1-unknown-retry-queue-v1",
        "coverage_sha256": sha256(args.coverage),
        "jobs_sha256": sha256(args.jobs),
        "output_sha256": sha256(args.output),
        "rows": len(rows),
        "profile_counts": [counts[index] for index in range(5)],
        "selection": {
            "status": "pending", "certified_s3": "0",
            "fleet_v2_claim": "1", "fleet_v2_verdict": "UNKNOWN",
            "fleet_v3_claim": "0", "fleet_v3_verdict": "",
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
