#!/usr/bin/env python3
"""Build an exact H1 replay JSONL queue from three frozen offline indexes.

No AWS calls are made.  The terminal index must already bind each immutable S3
certificate key to a gzip-object SHA-256 verified by full object readback.
The resulting receipt is not yet consumed by ``build_replay_manifest.py``;
that provenance integration remains a required freeze gate.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import json
from pathlib import Path

from replay_common import ReplayError, atomic_write, canonical_json, require_sha
from capacity_queue import CAPACITY_PROFILE_COUNTS, PROFILE_NAMES, TABLE_PAIRS, table_serialization_tag
from replay_worker import validate_job


SCHEMA = "erdos85-h1-replay-queue-build-v1"
TERMINAL_COLUMNS = (
    "orbit", "certificate_key", "certificate_gzip_sha256",
    "certificate_readback_sha256",
)


def sha_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def require_fresh_distinct_paths(inputs: list[Path], outputs: list[Path]) -> None:
    resolved = [path.resolve() for path in [*inputs, *outputs]]
    if len(resolved) != len(set(resolved)):
        raise ReplayError("replay queue input/output paths must be distinct")
    existing = [str(path) for path in outputs if path.exists() or path.is_symlink()]
    if existing:
        raise ReplayError(f"replay queue outputs must be fresh: {existing}")


def read_tsv(value: bytes, label: str) -> tuple[list[str], list[dict[str, str]]]:
    try:
        text = value.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ReplayError(f"{label} is not UTF-8") from error
    reader = csv.DictReader(io.StringIO(text), delimiter="\t")
    if reader.fieldnames is None or len(reader.fieldnames) != len(set(reader.fieldnames)):
        raise ReplayError(f"{label} has a missing or duplicate header")
    rows = list(reader)
    if any(None in row for row in rows):
        raise ReplayError(f"{label} has rows wider than its header")
    return reader.fieldnames, rows


def inventory_rows(value: bytes) -> list[dict[str, object]]:
    try:
        lines = value.decode("ascii").splitlines()
    except UnicodeDecodeError as error:
        raise ReplayError("capacity inventory is not ASCII") from error
    result: list[dict[str, object]] = []
    counts = [0] * len(PROFILE_NAMES)
    seen: set[str] = set()
    for number, line in enumerate(lines, 1):
        if not line:
            continue
        try:
            profile, *values = map(int, line.split())
        except ValueError as error:
            raise ReplayError(f"capacity inventory line {number} is non-integer") from error
        if profile not in range(5) or len(values) != len(TABLE_PAIRS) or any(x < 0 for x in values):
            raise ReplayError(f"capacity inventory line {number} is malformed")
        table = {pair: count for pair, count in zip(TABLE_PAIRS, values, strict=True) if count}
        serialization = json.dumps(sorted(table.items()))
        tag = table_serialization_tag(serialization)
        if tag in seen:
            raise ReplayError(f"duplicate capacity orbit {tag}")
        seen.add(tag)
        result.append({"tag": tag, "profile": profile, "local_index": counts[profile],
                       "table_serialization": serialization})
        counts[profile] += 1
    if tuple(counts) != CAPACITY_PROFILE_COUNTS:
        raise ReplayError(f"capacity profile counts differ: {tuple(counts)}")
    return result


def keyed(rows: list[dict[str, str]], label: str) -> dict[str, dict[str, str]]:
    result: dict[str, dict[str, str]] = {}
    for number, row in enumerate(rows, 2):
        tag = row.get("orbit", "")
        if tag in result:
            raise ReplayError(f"{label}:{number}: duplicate orbit {tag}")
        result[tag] = row
    return result


def build(inventory: bytes, certificate_index: bytes, terminal_index: bytes,
          require_complete: bool = True) -> tuple[bytes, dict[str, object]]:
    capacity = inventory_rows(inventory)
    cert_fields, cert_rows = read_tsv(certificate_index, "certificate index")
    required_cert = {"orbit", "profile", "localIndex", "compact_lrat_sha256", "cnf_sha256"}
    if not required_cert.issubset(cert_fields):
        raise ReplayError("certificate index lacks required columns")
    terminal_fields, terminal_rows = read_tsv(terminal_index, "terminal index")
    if tuple(terminal_fields) != TERMINAL_COLUMNS:
        raise ReplayError("terminal index header differs from exact schema")
    certs = keyed(cert_rows, "certificate index")
    terminals = keyed(terminal_rows, "terminal index")
    expected = {row["tag"] for row in capacity}
    if set(certs) - expected or set(terminals) - expected:
        raise ReplayError("input index contains orbit outside capacity inventory")
    if set(certs) != set(terminals):
        raise ReplayError("certificate and terminal indexes cover different orbits")
    if require_complete and (set(certs) != expected or set(terminals) != expected):
        raise ReplayError("complete queue inputs do not exactly cover capacity inventory")
    jobs: list[dict[str, object]] = []
    for item in capacity:
        tag = str(item["tag"])
        if tag not in certs or tag not in terminals:
            continue
        cert, terminal = certs[tag], terminals[tag]
        profile = int(item["profile"])
        local_index = int(item["local_index"])
        if cert["profile"] != PROFILE_NAMES[profile] or cert["localIndex"] != str(local_index):
            raise ReplayError(f"{tag}: certificate capacity ordinal mismatch")
        compact = require_sha(cert["compact_lrat_sha256"], f"{tag}.compact_lrat_sha256")
        cnf = require_sha(cert["cnf_sha256"], f"{tag}.cnf_sha256")
        gzip_sha = require_sha(terminal["certificate_gzip_sha256"], f"{tag}.gzip_sha256")
        readback = require_sha(terminal["certificate_readback_sha256"], f"{tag}.readback_sha256")
        if gzip_sha != readback:
            raise ReplayError(f"{tag}: gzip and readback SHA-256 differ")
        key = f"sat49/campaign-20260825/h1/{tag}.compact.lrat.gz"
        if terminal["certificate_key"] != key:
            raise ReplayError(f"{tag}: certificate key differs from canonical key")
        serialization = str(item["table_serialization"])
        job = {"tag": tag, "profile": profile, "local_index": local_index,
                     "certificate_key": key, "certificate_gzip_sha256": gzip_sha,
                     "compact_lrat_sha256": compact, "cnf_sha256": cnf,
                     "table_serialization": serialization,
                     "table_sha256": sha_bytes(serialization.encode())}
        jobs.append(validate_job(job, tag))
    jobs.sort(key=lambda row: str(row["tag"]))
    if not jobs:
        raise ReplayError("replay queue is empty")
    output = b"".join(canonical_json(job) for job in jobs)
    receipt: dict[str, object] = {
        "schema": SCHEMA, "inventory_sha256": sha_bytes(inventory),
        "certificate_index_sha256": sha_bytes(certificate_index),
        "terminal_index_sha256": sha_bytes(terminal_index),
        "output_sha256": sha_bytes(output), "emitted_jobs": len(jobs),
        "require_complete": require_complete,
    }
    return output, receipt


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", type=Path, required=True)
    parser.add_argument("--certificate-index", type=Path, required=True)
    parser.add_argument("--terminal-index", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--receipt-output", type=Path, required=True)
    parser.add_argument("--allow-partial", action="store_true")
    args = parser.parse_args()
    inputs = [args.inventory, args.certificate_index, args.terminal_index]
    outputs = [args.output, args.receipt_output]
    require_fresh_distinct_paths(inputs, outputs)
    values = [path.read_bytes() for path in inputs]
    output, receipt = build(*values, require_complete=not args.allow_partial)
    atomic_write(args.output, output)
    atomic_write(args.receipt_output, canonical_json(receipt))
    print(f"jobs={receipt['emitted_jobs']} queue_sha256={receipt['output_sha256']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
