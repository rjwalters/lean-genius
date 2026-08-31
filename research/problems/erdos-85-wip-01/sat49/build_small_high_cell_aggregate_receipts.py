#!/usr/bin/env python3
"""Build canonical seven-cell receipts from the validated 406-leaf socket bank."""

from __future__ import annotations

import argparse
import csv
import hashlib
import importlib.util
import json
import os
import re
from pathlib import Path


HERE = Path(__file__).resolve().parent
VALIDATOR_PATH = HERE / "validate_socket_table.py"
SPEC = importlib.util.spec_from_file_location("socket_table", VALIDATOR_PATH)
SOCKETS = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(SOCKETS)

SCHEMA = "erdos85-small-high-cell-aggregate-v1"
INDEX_SCHEMA = "erdos85-small-high-cell-aggregate-index-v1"
CELLS = (
    ("hb1", "h3_b1", "Erdos85.smallHighH3B1Base_unsat"),
    ("hc1", "h3_c1", "Erdos85.smallHighH3C1Base_unsat"),
    ("hc2", "h3_c2", "Erdos85.smallHighH3C2Base_unsat"),
    ("hdist2", "h3_dist2", "Erdos85.smallHighH3Dist2Base_unsat"),
    ("h50", "h5_t0", "Erdos85.smallHighH5T0Base_unsat"),
    ("h51", "h5_t1", "Erdos85.smallHighH5T1Base_unsat"),
    ("h52", "h5_t2", "Erdos85.smallHighH5T2Base_unsat"),
)
SHA256 = re.compile(r"[0-9a-f]{64}")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def canonical(value: object) -> bytes:
    return (json.dumps(value, ensure_ascii=True, allow_nan=False,
                       separators=(",", ":"), sort_keys=True) + "\n").encode("ascii")


def identity_sha(value: object) -> str:
    return hashlib.sha256(canonical(value)).hexdigest()


def expected_job_ids(cell: str) -> list[str]:
    return [f"{cell}.cover-left", f"{cell}.cover-right", *(
        f"{cell}.cube-{left}-{right}"
        for left in range(7) for right in range(8))]


def require_file_pin(path: Path, expected: str, label: str) -> None:
    if not path.is_absolute() or path.is_symlink() or not path.is_file():
        raise ValueError(f"{label} must be an absolute regular non-symlink file")
    if not SHA256.fullmatch(expected) or sha256(path) != expected:
        raise ValueError(f"{label} hash mismatch")


def read_socket_rows(table: Path) -> list[dict[str, str]]:
    with table.open(newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t", strict=True)
        if tuple(reader.fieldnames or ()) != SOCKETS.FIELDS:
            raise ValueError("socket table header drift")
        return list(reader)


def validate_inputs(root_manifest: Path, root_manifest_sha256: str,
                    table: Path, expected: Path, validation_receipt: Path,
                    module: Path, source_module: str,
                    module_sha256: str) -> tuple[dict, list[dict[str, str]], dict]:
    for path, pin, label in (
        (root_manifest, root_manifest_sha256, "root manifest"),
        (module, module_sha256, "generated module"),
    ):
        require_file_pin(path, pin, label)
    for path, label in ((table, "socket table"), (expected, "expected sockets"),
                        (validation_receipt, "socket validation receipt")):
        if not path.is_absolute() or path.is_symlink() or not path.is_file():
            raise ValueError(f"{label} must be an absolute regular non-symlink file")
    if module.name != source_module.split(".")[-1] + ".lean":
        raise ValueError("generated module path/name mismatch")

    socket_count = SOCKETS.validate(table, expected)
    if socket_count != 406:
        raise ValueError(f"expected exactly 406 validated leaf sockets, got {socket_count}")
    expected_receipt = SOCKETS.evidence_receipt(table, expected, socket_count) + "\n"
    if validation_receipt.read_text() != expected_receipt:
        raise ValueError("socket validation receipt is not byte-exact")

    manifest = json.loads(root_manifest.read_text())
    if manifest.get("schema") != "erdos85-small-high-cube-jobs-v1":
        raise ValueError("unsupported root manifest schema")
    cells = manifest.get("cells")
    if not isinstance(cells, dict) or list(cells) != [cell for _, cell, _ in CELLS]:
        raise ValueError("root manifest cell order/set mismatch")
    manifest_ids: list[str] = []
    for _, cell, _ in CELLS:
        ids = [row.get("id") for row in cells[cell].get("jobs", [])]
        if ids != expected_job_ids(cell):
            raise ValueError(f"{cell}: manifest is not the exact ordered 58-job grid")
        manifest_ids.extend(ids)
    if len(manifest_ids) != 406 or len(set(manifest_ids)) != 406:
        raise ValueError("root manifest job bijection failure")

    rows = read_socket_rows(table)
    by_job: dict[str, dict[str, str]] = {}
    for row in rows:
        identities = json.loads(row["campaign_manifest_rows"])
        if not isinstance(identities, list) or len(identities) != 1:
            raise ValueError("each small-high leaf socket must bind exactly one job id")
        job = identities[0]
        if job in by_job:
            raise ValueError(f"duplicate leaf socket job: {job}")
        by_job[job] = row
    if list(by_job) != manifest_ids:
        raise ValueError("socket rows are not the exact ordered manifest projection")

    module_text = module.read_text()
    for row in rows:
        theorem = row["theorem"].split(".")[-1]
        if f"theorem {theorem} " not in module_text and f"theorem {theorem} :" not in module_text:
            raise ValueError(f"generated module lacks leaf theorem {row['theorem']}")
        if row["source_module"] != source_module:
            raise ValueError("leaf socket source module mismatch")
    for _, _, theorem in CELLS:
        short = theorem.split(".")[-1]
        if f"theorem {short} " not in module_text and f"theorem {short} :" not in module_text:
            raise ValueError(f"generated module lacks base theorem {theorem}")
    return manifest, rows, by_job


def build_receipts(root_manifest: Path, root_manifest_sha256: str,
                   table: Path, expected: Path, validation_receipt: Path,
                   module: Path, source_module: str,
                   module_sha256: str) -> tuple[list[tuple[str, dict]], dict]:
    _, _, by_job = validate_inputs(
        root_manifest, root_manifest_sha256, table, expected, validation_receipt,
        module, source_module, module_sha256)
    validator_line = validation_receipt.read_text().rstrip("\n")
    identity_match = re.fullmatch(
        r"PASS schema=erdos85-sat49-socket-table-v1 sockets=406 "
        r"table_sha256=[0-9a-f]{64} expected_manifest_sha256=[0-9a-f]{64} "
        r"identity_sha256=([0-9a-f]{64})", validator_line)
    if identity_match is None:
        raise ValueError("socket validation receipt identity is malformed")
    validator_identity = identity_match.group(1)
    table_sha, expected_sha = sha256(table), sha256(expected)
    receipts: list[tuple[str, dict]] = []
    for ordinal, (argument, cell, theorem) in enumerate(CELLS):
        jobs = expected_job_ids(cell)
        projection = [{field: by_job[job][field] for field in SOCKETS.FIELDS}
                      for job in jobs]
        receipt = {
            "base_unsat_theorem": theorem,
            "cell": cell,
            "consumer_argument": argument,
            "expected_manifest_sha256": expected_sha,
            "leaf_count": 58,
            "leaf_evidence_identity_sha256": identity_sha(projection),
            "leaf_job_ids": jobs,
            "ordinal": ordinal,
            "root_manifest_sha256": root_manifest_sha256,
            "schema": SCHEMA,
            "socket_table_sha256": table_sha,
            "socket_validator_identity_sha256": validator_identity,
            "source_module": source_module,
            "source_sha256": module_sha256,
        }
        receipts.append((cell, receipt))
    index = {
        "cells": [{"cell": cell, "receipt": f"{cell}.receipt.json",
                   "receipt_sha256": hashlib.sha256(canonical(receipt)).hexdigest()}
                  for cell, receipt in receipts],
        "expected_manifest_sha256": expected_sha,
        "root_manifest_sha256": root_manifest_sha256,
        "schema": INDEX_SCHEMA,
        "socket_table_sha256": table_sha,
        "socket_validator_identity_sha256": validator_identity,
        "source_module": source_module,
        "source_sha256": module_sha256,
    }
    return receipts, index


def publish(output: Path, receipts: list[tuple[str, dict]], index: dict) -> None:
    output.mkdir(parents=False, exist_ok=False)
    for cell, receipt in receipts:
        path = output / f"{cell}.receipt.json"
        path.write_bytes(canonical(receipt))
        with path.open("rb") as stream:
            os.fsync(stream.fileno())
    index_path = output / "index.receipt.json"
    index_path.write_bytes(canonical(index))
    with index_path.open("rb") as stream:
        os.fsync(stream.fileno())
    descriptor = os.open(output, os.O_RDONLY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root-manifest", type=Path, required=True)
    parser.add_argument("--root-manifest-sha256", required=True)
    parser.add_argument("--socket-table", type=Path, required=True)
    parser.add_argument("--expected-sockets", type=Path, required=True)
    parser.add_argument("--socket-validation-receipt", type=Path, required=True)
    parser.add_argument("--module", type=Path, required=True)
    parser.add_argument("--source-module", required=True)
    parser.add_argument("--module-sha256", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    receipts, index = build_receipts(
        args.root_manifest, args.root_manifest_sha256,
        args.socket_table, args.expected_sockets,
        args.socket_validation_receipt, args.module,
        args.source_module, args.module_sha256)
    publish(args.output, receipts, index)
    print(f"WROTE {args.output.resolve()} cells=7 leaves=406")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
