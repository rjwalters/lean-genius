#!/usr/bin/env python3
"""Validate the final order-49 certificate-leaf-to-Lean socket table.

There is exactly one TSV row per certificate leaf, never one row per aggregate
stratum.  Thus H1 contributes 13,351 rows and each row binds one CNF, compact
LRAT, replay receipt, and Lean theorem.  The frozen expected JSON manifest
binds each leaf hypothesis to its campaign-row identity or identities.  This
validator checks those identities and bijections; it never treats a solver
verdict as a proof or invents missing campaign provenance.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
from pathlib import Path


FIELDS = (
    "hypothesis",
    "theorem",
    "source_module",
    "commit",
    "campaign_manifest_rows",
    "cnf_sha256",
    "compact_lrat_sha256",
    "replay_receipt",
    "review_id",
)
LEAN_NAME = re.compile(
    r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
)
SHA256 = re.compile(r"[0-9a-f]{64}")
COMMIT = re.compile(r"[0-9a-f]{40}")
REVIEW = re.compile(r"#?[1-9][0-9]*")
FORBIDDEN = re.compile(r"(?:^|[^A-Za-z])(TBD|UNKNOWN|TODO|NONE|N/A)(?:$|[^A-Za-z])", re.I)


class SocketTableError(ValueError):
    pass


def _read_expected(path: Path) -> dict[str, list[str]]:
    try:
        document = json.loads(path.read_text())
    except json.JSONDecodeError as exc:
        raise SocketTableError(f"{path}: invalid expected JSON: {exc.msg}") from exc
    if not isinstance(document, dict) or set(document) != {"version", "sockets"}:
        raise SocketTableError(
            f"{path}: expected exactly version and sockets at top level")
    if document["version"] != 1 or not isinstance(document["sockets"], list):
        raise SocketTableError(f"{path}: expected version 1 and a sockets array")
    expected: dict[str, list[str]] = {}
    for number, item in enumerate(document["sockets"]):
        context = f"{path}:sockets[{number}]"
        if not isinstance(item, dict) or set(item) != {
                "hypothesis", "campaign_manifest_rows"}:
            raise SocketTableError(f"{context}: invalid expected socket schema")
        hypothesis = item["hypothesis"]
        if not isinstance(hypothesis, str) or not LEAN_NAME.fullmatch(hypothesis):
            raise SocketTableError(f"{context}: invalid hypothesis identifier")
        if hypothesis in expected:
            raise SocketTableError(f"duplicate expected hypothesis: {hypothesis}")
        rows = item["campaign_manifest_rows"]
        if (not isinstance(rows, list) or not rows or
                any(not isinstance(row, str) or not row for row in rows) or
                len(rows) != len(set(rows))):
            raise SocketTableError(f"{context}: invalid campaign manifest rows")
        expected[hypothesis] = rows
    if not expected:
        raise SocketTableError(f"{path}: expected socket set is empty")
    return expected


def _manifest_rows(value: str, context: str) -> list[str]:
    try:
        parsed = json.loads(value)
    except json.JSONDecodeError as exc:
        raise SocketTableError(
            f"{context}: campaign_manifest_rows is not JSON: {exc.msg}") from exc
    if not isinstance(parsed, list) or not parsed:
        raise SocketTableError(
            f"{context}: campaign_manifest_rows must be a nonempty JSON array")
    if any(not isinstance(item, str) or not item for item in parsed):
        raise SocketTableError(
            f"{context}: campaign manifest row identities must be nonempty strings")
    if len(parsed) != len(set(parsed)):
        raise SocketTableError(f"{context}: duplicate campaign manifest row identity")
    return parsed


def validate(table_path: Path, expected_path: Path) -> int:
    expected = _read_expected(expected_path)
    with table_path.open(newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t", strict=True)
        if tuple(reader.fieldnames or ()) != FIELDS:
            raise SocketTableError(
                f"{table_path}: header must be exactly {list(FIELDS)}")
        rows = list(reader)

    hypotheses: list[str] = []
    theorems: list[str] = []
    receipts: list[str] = []
    all_manifest_rows: list[str] = []
    for number, row in enumerate(rows, 2):
        context = f"{table_path}:{number}"
        if None in row or any(value is None for value in row.values()):
            raise SocketTableError(f"{context}: wrong number of TSV fields")
        if any(FORBIDDEN.search(value) for value in row.values()):
            raise SocketTableError(f"{context}: placeholder value is forbidden")
        if not LEAN_NAME.fullmatch(row["hypothesis"]):
            raise SocketTableError(f"{context}: invalid hypothesis identifier")
        if not LEAN_NAME.fullmatch(row["theorem"]):
            raise SocketTableError(f"{context}: invalid theorem identifier")
        if not LEAN_NAME.fullmatch(row["source_module"]):
            raise SocketTableError(f"{context}: invalid source_module identifier")
        if not COMMIT.fullmatch(row["commit"]):
            raise SocketTableError(f"{context}: commit must be 40 lowercase hex digits")
        for field in ("cnf_sha256", "compact_lrat_sha256", "replay_receipt"):
            if not SHA256.fullmatch(row[field]):
                raise SocketTableError(f"{context}: {field} must be a lowercase SHA-256")
        if not REVIEW.fullmatch(row["review_id"]):
            raise SocketTableError(f"{context}: invalid review_id")
        hypotheses.append(row["hypothesis"])
        theorems.append(row["theorem"])
        receipts.append(row["replay_receipt"])
        manifest_rows = _manifest_rows(row["campaign_manifest_rows"], context)
        if set(manifest_rows) != set(expected.get(row["hypothesis"], [])):
            raise SocketTableError(
                f"{context}: campaign manifest rows differ from frozen expectation")
        all_manifest_rows.extend(manifest_rows)

    duplicates = sorted({name for name in hypotheses if hypotheses.count(name) > 1})
    if duplicates:
        raise SocketTableError(f"duplicate socket hypotheses: {duplicates}")
    expected_set = set(expected)
    actual_set = set(hypotheses)
    if actual_set != expected_set:
        missing = sorted(expected_set - actual_set)
        unknown = sorted(actual_set - expected_set)
        raise SocketTableError(
            f"hypothesis bijection failed: missing={missing}, unknown={unknown}")
    duplicate_manifest_rows = sorted({
        item for item in all_manifest_rows if all_manifest_rows.count(item) > 1
    })
    if duplicate_manifest_rows:
        raise SocketTableError(
            f"campaign manifest rows reused by multiple sockets: {duplicate_manifest_rows}")
    for label, values in (("theorems", theorems), ("replay receipts", receipts)):
        duplicates = sorted({value for value in values if values.count(value) > 1})
        if duplicates:
            raise SocketTableError(f"duplicate {label}: {duplicates}")
    return len(rows)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--table", type=Path, required=True)
    parser.add_argument(
        "--expected-hypotheses", type=Path, required=True,
        help="frozen v1 JSON leaf manifest (name retained for checklist terminology)")
    args = parser.parse_args()
    try:
        count = validate(args.table, args.expected_hypotheses)
    except (OSError, SocketTableError) as exc:
        parser.error(str(exc))
    print(f"PASS sockets={count} table={args.table.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
