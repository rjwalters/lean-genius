#!/usr/bin/env python3
"""Build and materialize the checked h3/h5 cube-job manifest.

The Lean module ``Erdos85OrderFortyNineSmallHighCubeCover`` proves that each
listed cell is covered by two negative cover formulas and a 7-by-8 grid of
positive two-unit cubes.  This script stores only the tiny unit manifest;
workers materialize one derived CNF at a time, avoiding hundreds of copies of
the 1.3-million-clause base files.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path


# One-based DIMACS identifiers, shifted from the checked zero-based Lean arrays
# at this explicit format boundary and independently covered by the live
# selector-contract preflight.
SELECTORS: dict[str, tuple[tuple[int, ...], tuple[int, ...]]] = {
    "h3_b1": ((142, 144, 145, 146, 147, 148, 149),
              (142, 187, 194, 195, 196, 197, 198, 199)),
    "h3_c1": ((142, 144, 145, 146, 147, 148, 149),
              (142, 187, 194, 195, 196, 197, 198, 199)),
    "h3_c2": ((142, 143, 144, 145, 146, 147, 148),
              (142, 194, 195, 196, 197, 198, 199, 207)),
    "h3_dist2": ((142, 143, 144, 145, 146, 147, 148),
                 (142, 193, 196, 197, 198, 199, 200, 201)),
    "h5_t0": ((231, 232, 233, 240, 241, 242, 243),
              (231, 276, 277, 278, 286, 287, 288, 289)),
    "h5_t1": ((231, 232, 238, 239, 240, 241, 242),
              (231, 275, 276, 285, 286, 287, 288, 289)),
    "h5_t2": ((231, 236, 237, 238, 239, 240, 241),
              (231, 274, 275, 284, 285, 286, 287, 288)),
}

DEFAULT_FILENAMES = {
    cell: f"{cell}.cnf" for cell in SELECTORS
}
FREIGHT_SCHEMA = "erdos85-small-high-base-freight-v1"
SHA_RE = re.compile(r"[0-9a-f]{64}")
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
FREIGHT_BUILDER_SOURCE = (
    "research/problems/erdos-85-wip-01/sat49/build_small_high_base_freight.py")
EMITTER_SOURCE = "proofs/Proofs/Erdos85OrderFortyNineSmallHighCnfEmit.lean"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_json(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def load_freight_receipt(base_dir: Path, receipt_path: Path,
                         expected_sha256: str,
                         repo: Path = REPO) -> dict[str, object]:
    if not SHA_RE.fullmatch(expected_sha256):
        raise ValueError("expected freight receipt SHA-256 is not canonical")
    if receipt_path.resolve() != (base_dir / "receipt.json").resolve():
        raise ValueError("freight receipt must be base-dir/receipt.json")
    raw = receipt_path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != expected_sha256:
        raise ValueError("freight receipt SHA-256 differs from external pin")
    try:
        receipt = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ValueError("cannot parse freight receipt") from error
    if not isinstance(receipt, dict) or canonical_json(receipt) != raw:
        raise ValueError("freight receipt is not canonical JSON")
    expected_fields = {
        "schema", "git_commit", "freight_builder_source",
        "freight_builder_sha256", "emitter_source", "emitter_sha256",
        "emitter_build_command", "emitter_command", "lean_version", "cells",
    }
    if set(receipt) != expected_fields or receipt.get("schema") != FREIGHT_SCHEMA:
        raise ValueError("freight receipt differs from exact schema")
    for key in ("freight_builder_sha256", "emitter_sha256"):
        if not isinstance(receipt.get(key), str) or not SHA_RE.fullmatch(receipt[key]):
            raise ValueError(f"freight receipt has invalid {key}")
    commit = receipt.get("git_commit")
    if not isinstance(commit, str) or not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("freight receipt has invalid git_commit")
    if receipt.get("freight_builder_source") != FREIGHT_BUILDER_SOURCE:
        raise ValueError("freight receipt has wrong builder source")
    if receipt.get("emitter_source") != EMITTER_SOURCE:
        raise ValueError("freight receipt has wrong emitter source")
    if not isinstance(receipt.get("lean_version"), str) or not receipt["lean_version"]:
        raise ValueError("freight receipt has invalid lean_version")
    for source_key, hash_key in (
        ("freight_builder_source", "freight_builder_sha256"),
        ("emitter_source", "emitter_sha256"),
    ):
        historical = subprocess.run(
            ["git", "show", f"{commit}:{receipt[source_key]}"], cwd=repo,
            capture_output=True, check=False)
        if historical.returncode != 0:
            raise ValueError("freight receipt commit/source is unavailable")
        if hashlib.sha256(historical.stdout).hexdigest() != receipt[hash_key]:
            raise ValueError(f"freight receipt {hash_key} differs from commit bytes")
    if receipt.get("emitter_build_command") != [
        "lake", "build", "Proofs.Erdos85OrderFortyNineSmallHighCnfEmit"
    ]:
        raise ValueError("freight receipt has invalid emitter build command")
    command = receipt.get("emitter_command")
    if (not isinstance(command, list) or len(command) != 6 or
            command[:4] != ["lake", "env", "lean", "--run"] or
            command[-1] != "<cell>" or
            not str(command[4]).endswith("/" + receipt["emitter_source"])):
        raise ValueError("freight receipt has invalid emitter command")
    rows = receipt.get("cells")
    if not isinstance(rows, list) or [row.get("cell") if isinstance(row, dict) else None
                                     for row in rows] != list(SELECTORS):
        raise ValueError("freight receipt cells differ from exact order")
    for row, cell in zip(rows, SELECTORS, strict=True):
        expected_row = {"cell", "path", "sha256", "bytes", "variables",
                        "clauses", "max_literal"}
        if set(row) != expected_row or row.get("path") != DEFAULT_FILENAMES[cell]:
            raise ValueError(f"freight receipt row differs for {cell}")
        path = base_dir / DEFAULT_FILENAMES[cell]
        variables, clauses = inspect_dimacs(path)
        maximum = 0
        with path.open("rb") as stream:
            for raw in stream:
                line = raw.strip()
                if not line or line.startswith((b"c", b"p")):
                    continue
                maximum = max(maximum, *(abs(int(value)) for value in line.split()[:-1]))
        dimensions = {"variables": variables, "clauses": clauses,
                      "max_literal": maximum}
        if (row.get("sha256") != sha256(path) or
                row.get("bytes") != path.stat().st_size or
                any(row.get(key) != value for key, value in dimensions.items())):
            raise ValueError(f"freight receipt does not bind actual base {cell}")
    return receipt


def inspect_dimacs(path: Path) -> tuple[int, int]:
    header: tuple[int, int] | None = None
    actual = 0
    with path.open("rb") as stream:
        for line_number, raw in enumerate(stream, 1):
            line = raw.strip()
            if not line or line.startswith(b"c"):
                continue
            if line.startswith(b"p"):
                fields = line.split()
                if (header is not None or len(fields) != 4 or
                        fields[:2] != [b"p", b"cnf"]):
                    raise ValueError(f"{path}:{line_number}: malformed header")
                header = (int(fields[2]), int(fields[3]))
                if header[0] < 0 or header[1] < 0:
                    raise ValueError(f"{path}:{line_number}: negative header value")
                continue
            if header is None:
                raise ValueError(f"{path}:{line_number}: clause precedes header")
            try:
                literals = [int(field) for field in line.split()]
            except ValueError as error:
                raise ValueError(
                    f"{path}:{line_number}: non-integer clause field"
                ) from error
            if not literals or literals[-1] != 0 or 0 in literals[:-1]:
                raise ValueError(f"{path}:{line_number}: unterminated clause")
            if any(abs(literal) > header[0] for literal in literals[:-1]):
                raise ValueError(
                    f"{path}:{line_number}: literal exceeds variable header"
                )
            actual += 1
    if header is None:
        raise ValueError(f"{path}: missing DIMACS header")
    if actual != header[1]:
        raise ValueError(
            f"{path}: header declares {header[1]} clauses, found {actual}"
        )
    return header


def jobs_for(cell: str) -> list[dict[str, object]]:
    left, right = SELECTORS[cell]
    jobs: list[dict[str, object]] = [
        {"id": f"{cell}.cover-left", "kind": "cover-left",
         "units": [-literal for literal in left]},
        {"id": f"{cell}.cover-right", "kind": "cover-right",
         "units": [-literal for literal in right]},
    ]
    for li, left_literal in enumerate(left):
        for ri, right_literal in enumerate(right):
            jobs.append({
                "id": f"{cell}.cube-{li}-{ri}",
                "kind": "cube",
                "left_index": li,
                "right_index": ri,
                "units": [left_literal, right_literal],
            })
    return jobs


def publish_create_only(temporary: Path, output: Path) -> None:
    """Atomically publish a staged file without replacing existing evidence."""
    try:
        os.link(temporary, output)
    except FileExistsError as error:
        raise FileExistsError(f"refusing to replace existing output: {output}") from error


def write_manifest(base_dir: Path, freight_receipt: Path,
                   expected_freight_receipt_sha256: str, output: Path) -> None:
    freight = load_freight_receipt(
        base_dir, freight_receipt, expected_freight_receipt_sha256)
    cells: dict[str, object] = {}
    positive_cube_jobs = 0
    negative_cover_jobs = 0
    for cell in SELECTORS:
        base = (base_dir / DEFAULT_FILENAMES[cell]).resolve()
        if not base.is_file():
            raise ValueError(f"missing base CNF for {cell}: {base}")
        variables, clauses = inspect_dimacs(base)
        left, right = SELECTORS[cell]
        if max(left + right) > variables:
            raise ValueError(f"selector exceeds variable header for {cell}")
        jobs = jobs_for(cell)
        positive_cube_jobs += sum(job["kind"] == "cube" for job in jobs)
        negative_cover_jobs += sum(job["kind"].startswith("cover-") for job in jobs)
        cells[cell] = {
            "base": str(base),
            "base_sha256": sha256(base),
            "variables": variables,
            "base_clauses": clauses,
            "left": list(left),
            "right": list(right),
            "jobs": jobs,
        }
    manifest = {
        "schema": "erdos85-small-high-cube-jobs-v1",
        "lean_commit": freight["git_commit"],
        "freight_schema": FREIGHT_SCHEMA,
        "freight_receipt_sha256": sha256(freight_receipt),
        "freight_builder_sha256": freight["freight_builder_sha256"],
        "emitter_sha256": freight["emitter_sha256"],
        "identifier_convention": "one-based DIMACS",
        "positive_cube_jobs": positive_cube_jobs,
        "negative_cover_jobs": negative_cover_jobs,
        "cells": cells,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary_name = tempfile.mkstemp(
        prefix=f".{output.name}.", suffix=".tmp", dir=output.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(fd, "w") as target:
            target.write(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
        publish_create_only(temporary, output)
    finally:
        temporary.unlink(missing_ok=True)


def find_job(manifest: dict[str, object], job_id: str) -> tuple[dict, dict]:
    cells = manifest.get("cells")
    if not isinstance(cells, dict):
        raise ValueError("manifest has no cell mapping")
    matches = []
    for cell in cells.values():
        for job in cell["jobs"]:
            if job["id"] == job_id:
                matches.append((cell, job))
    if len(matches) != 1:
        raise ValueError(f"unknown or duplicated job id: {job_id}")
    return matches[0]


def materialize(manifest_path: Path, job_id: str, output: Path) -> None:
    manifest = json.loads(manifest_path.read_text())
    if manifest.get("schema") != "erdos85-small-high-cube-jobs-v1":
        raise ValueError(f"unsupported manifest schema: {manifest_path}")
    cell, job = find_job(manifest, job_id)
    base = Path(cell["base"])
    if sha256(base) != cell["base_sha256"]:
        raise ValueError(f"base CNF hash mismatch: {base}")
    units = job["units"]
    output.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary_name = tempfile.mkstemp(
        prefix=f".{output.name}.", suffix=".tmp", dir=output.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(fd, "wb") as target, base.open("rb") as source:
            replaced = False
            for raw in source:
                if raw.lstrip().startswith(b"p cnf"):
                    if replaced:
                        raise ValueError(f"duplicate DIMACS header: {base}")
                    target.write(
                        f"p cnf {cell['variables']} "
                        f"{cell['base_clauses'] + len(units)}\n".encode()
                    )
                    replaced = True
                else:
                    target.write(raw)
            if not replaced:
                raise ValueError(f"missing DIMACS header: {base}")
            for literal in units:
                target.write(f"{literal} 0\n".encode())
        variables, clauses = inspect_dimacs(temporary)
        if (variables, clauses) != (
            cell["variables"], cell["base_clauses"] + len(units)
        ):
            raise AssertionError("materialized DIMACS metadata mismatch")
        publish_create_only(temporary, output)
    finally:
        temporary.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    manifest_parser = subparsers.add_parser("manifest")
    manifest_parser.add_argument("--base-dir", type=Path, required=True)
    manifest_parser.add_argument("--freight-receipt", type=Path, required=True)
    manifest_parser.add_argument(
        "--expected-freight-receipt-sha256", required=True)
    manifest_parser.add_argument("--output", type=Path, required=True)
    materialize_parser = subparsers.add_parser("materialize")
    materialize_parser.add_argument("--manifest", type=Path, required=True)
    materialize_parser.add_argument("--job", required=True)
    materialize_parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "manifest":
        write_manifest(
            args.base_dir.resolve(), args.freight_receipt.resolve(),
            args.expected_freight_receipt_sha256, args.output.resolve())
        print(f"WROTE {args.output.resolve()}")
    else:
        materialize(args.manifest.resolve(), args.job, args.output.resolve())
        print(f"WROTE {args.output.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
