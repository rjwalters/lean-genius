#!/usr/bin/env python3
"""Generate second-level checked-grid jobs for hard h3/h5 parent cubes."""

from __future__ import annotations

import argparse
import json
import os
import tempfile
from pathlib import Path

from generate_small_high_cube_jobs import inspect_dimacs, sha256


# One-based DIMACS identifiers matching
# Erdos85OrderFortyNineSmallHighNestedCubeSelectors.lean.
SELECTORS: dict[str, tuple[tuple[int, ...], tuple[int, ...]]] = {
    "h3_b1": ((187, 243, 244, 245, 246, 247, 248),
               (144, 188, 274, 275, 276, 277, 278)),
    "h3_c1": ((187, 243, 244, 245, 246, 247, 248),
               (144, 188, 274, 275, 276, 277, 278)),
    "h3_c2": ((243, 244, 245, 246, 247, 248, 250),
               (144, 188, 231, 274, 275, 276, 277)),
    "h3_dist2": ((143, 237, 245, 246, 247, 248, 249, 250),
                  (144, 188, 231, 274, 275, 276, 277)),
    "h5_t0": ((274, 317, 320, 321, 331, 332, 333, 334),
               (316, 358, 360, 362, 375, 376, 377, 378)),
    "h5_t1": ((232, 318, 319, 331, 332, 333, 334, 335),
               (275, 358, 360, 376, 377, 378, 379)),
    "h5_t2": ((232, 317, 318, 330, 331, 332, 333, 334),
               (275, 316, 357, 375, 376, 377, 378, 379)),
}


def read_hard_jobs(path: Path) -> list[str]:
    text = path.read_text()
    try:
        parsed = json.loads(text)
    except json.JSONDecodeError:
        parsed = [line.strip() for line in text.splitlines()
                  if line.strip() and not line.lstrip().startswith("#")]
    if not isinstance(parsed, list) or any(not isinstance(item, str)
                                           for item in parsed):
        raise ValueError("hard-job file must be a JSON string list or one id per line")
    if len(set(parsed)) != len(parsed):
        raise ValueError("hard-job file contains duplicate ids")
    return parsed


def parent_jobs(parent: dict) -> dict[str, tuple[str, dict, dict]]:
    cells = parent.get("cells")
    if not isinstance(cells, dict):
        raise ValueError("parent manifest has no cell mapping")
    result = {}
    for cell_name, cell in cells.items():
        if cell_name not in SELECTORS:
            raise ValueError(f"unexpected parent cell: {cell_name}")
        for job in cell.get("jobs", []):
            job_id = job.get("id")
            if not isinstance(job_id, str) or job_id in result:
                raise ValueError(f"invalid or duplicate parent job id: {job_id}")
            result[job_id] = (cell_name, cell, job)
    return result


def nested_jobs(parent_id: str, left: tuple[int, ...],
                right: tuple[int, ...]) -> list[dict[str, object]]:
    result: list[dict[str, object]] = [
        {"id": f"{parent_id}.nested.cover-left", "kind": "cover-left",
         "units": [-literal for literal in left]},
        {"id": f"{parent_id}.nested.cover-right", "kind": "cover-right",
         "units": [-literal for literal in right]},
    ]
    for li, left_literal in enumerate(left):
        for ri, right_literal in enumerate(right):
            result.append({
                "id": f"{parent_id}.nested.cube-{li}-{ri}",
                "kind": "cube", "left_index": li, "right_index": ri,
                "units": [left_literal, right_literal],
            })
    return result


def write_manifest(parent_path: Path, hard_path: Path, output: Path) -> None:
    parent = json.loads(parent_path.read_text())
    if parent.get("schema") != "erdos85-small-high-cube-jobs-v1":
        raise ValueError(f"unsupported parent schema: {parent_path}")
    lookup = parent_jobs(parent)
    hard_ids = read_hard_jobs(hard_path)
    leaves = {}
    total_positive = 0
    total_covers = 0
    for parent_id in hard_ids:
        if parent_id not in lookup:
            raise ValueError(f"unknown parent job: {parent_id}")
        cell_name, cell, parent_job = lookup[parent_id]
        if parent_job.get("kind") != "cube":
            raise ValueError(f"nested split requires a positive parent cube: {parent_id}")
        base = Path(cell["base"])
        if sha256(base) != cell["base_sha256"]:
            raise ValueError(f"base CNF hash mismatch: {base}")
        variables, clauses = inspect_dimacs(base)
        if (variables, clauses) != (cell["variables"], cell["base_clauses"]):
            raise ValueError(f"base CNF metadata mismatch: {base}")
        left, right = SELECTORS[cell_name]
        if max(left + right) > variables:
            raise ValueError(f"nested selector exceeds variable header: {cell_name}")
        jobs = nested_jobs(parent_id, left, right)
        total_positive += len(left) * len(right)
        total_covers += 2
        leaves[parent_id] = {
            "cell": cell_name,
            "base": str(base.resolve()),
            "base_sha256": cell["base_sha256"],
            "variables": variables,
            "base_clauses": clauses,
            "parent_units": parent_job["units"],
            "left": list(left),
            "right": list(right),
            "jobs": jobs,
        }
    manifest = {
        "schema": "erdos85-small-high-nested-cube-jobs-v1",
        "identifier_convention": "one-based DIMACS",
        "parent_manifest": str(parent_path.resolve()),
        "parent_manifest_sha256": sha256(parent_path),
        "hard_parent_jobs": len(leaves),
        "positive_cube_jobs": total_positive,
        "negative_cover_jobs": total_covers,
        "leaves": leaves,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name(f".{output.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, output)


def find_nested_job(manifest: dict, job_id: str) -> tuple[dict, dict]:
    matches = []
    for leaf in manifest.get("leaves", {}).values():
        for job in leaf.get("jobs", []):
            if job.get("id") == job_id:
                matches.append((leaf, job))
    if len(matches) != 1:
        raise ValueError(f"unknown or duplicated nested job id: {job_id}")
    return matches[0]


def materialize(manifest_path: Path, job_id: str, output: Path) -> None:
    manifest = json.loads(manifest_path.read_text())
    if manifest.get("schema") != "erdos85-small-high-nested-cube-jobs-v1":
        raise ValueError(f"unsupported manifest schema: {manifest_path}")
    parent_path = Path(manifest["parent_manifest"])
    if sha256(parent_path) != manifest["parent_manifest_sha256"]:
        raise ValueError(f"parent manifest hash mismatch: {parent_path}")
    leaf, job = find_nested_job(manifest, job_id)
    base = Path(leaf["base"])
    if sha256(base) != leaf["base_sha256"]:
        raise ValueError(f"base CNF hash mismatch: {base}")
    units = [*leaf["parent_units"], *job["units"]]
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
                        f"p cnf {leaf['variables']} "
                        f"{leaf['base_clauses'] + len(units)}\n".encode()
                    )
                    replaced = True
                else:
                    target.write(raw)
            if not replaced:
                raise ValueError(f"missing DIMACS header: {base}")
            for literal in units:
                target.write(f"{literal} 0\n".encode())
        expected = (leaf["variables"], leaf["base_clauses"] + len(units))
        if inspect_dimacs(temporary) != expected:
            raise AssertionError("materialized nested DIMACS metadata mismatch")
        os.replace(temporary, output)
    finally:
        temporary.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    manifest_parser = subparsers.add_parser("manifest")
    manifest_parser.add_argument("--parent-manifest", type=Path, required=True)
    manifest_parser.add_argument("--hard-jobs", type=Path, required=True)
    manifest_parser.add_argument("--output", type=Path, required=True)
    materialize_parser = subparsers.add_parser("materialize")
    materialize_parser.add_argument("--manifest", type=Path, required=True)
    materialize_parser.add_argument("--job", required=True)
    materialize_parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "manifest":
        write_manifest(args.parent_manifest.resolve(), args.hard_jobs.resolve(),
                       args.output.resolve())
    else:
        materialize(args.manifest.resolve(), args.job, args.output.resolve())
    print(f"WROTE {args.output.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
