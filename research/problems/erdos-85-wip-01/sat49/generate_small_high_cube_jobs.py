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
import tempfile
from pathlib import Path


# One-based DIMACS identifiers.  These are the checked zero-based Lean arrays
# from commit b2d4f135f3, shifted by one at this explicit format boundary.
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
    "h3_b1": "b1.lean-emitted.cnf",
    "h3_c1": "c1.lean-emitted.cnf",
    "h3_c2": "c2.lean-emitted.cnf",
    "h3_dist2": "dist2.lean-emitted.cnf",
    "h5_t0": "h5_t0.lean-emitted.cnf",
    "h5_t1": "h5_t1.lean-emitted.cnf",
    "h5_t2": "h5_t2.lean-emitted.cnf",
}


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


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
                continue
            if not line.endswith(b" 0") and line != b"0":
                raise ValueError(f"{path}:{line_number}: unterminated clause")
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


def write_manifest(base_dir: Path, output: Path) -> None:
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
        "lean_commit": "b2d4f135f3",
        "identifier_convention": "one-based DIMACS",
        "positive_cube_jobs": positive_cube_jobs,
        "negative_cover_jobs": negative_cover_jobs,
        "cells": cells,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name(f".{output.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, output)


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
        os.replace(temporary, output)
    finally:
        temporary.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    manifest_parser = subparsers.add_parser("manifest")
    manifest_parser.add_argument("--base-dir", type=Path, required=True)
    manifest_parser.add_argument("--output", type=Path, required=True)
    materialize_parser = subparsers.add_parser("materialize")
    materialize_parser.add_argument("--manifest", type=Path, required=True)
    materialize_parser.add_argument("--job", required=True)
    materialize_parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "manifest":
        write_manifest(args.base_dir.resolve(), args.output.resolve())
        print(f"WROTE {args.output.resolve()}")
    else:
        materialize(args.manifest.resolve(), args.job, args.output.resolve())
        print(f"WROTE {args.output.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
