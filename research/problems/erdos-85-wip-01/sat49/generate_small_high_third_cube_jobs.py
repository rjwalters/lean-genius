#!/usr/bin/env python3
"""Generate third-level checked-grid jobs for hard h3 b1/c1 nested cubes."""

from __future__ import annotations

import argparse
import json
import os
import tempfile
from pathlib import Path

from generate_small_high_cube_jobs import inspect_dimacs, sha256


# One-based DIMACS identifiers pinned by
# Erdos85OrderFortyNineSmallHighThirdCubeSelectors.lean.
LEFT = (164, 208, 293, 334, 374, 413, 451, 488)
RIGHT = (165, 209, 294, 335, 375, 414, 452, 489)
SUPPORTED_CELLS = {"h3_b1", "h3_c1"}


def third_jobs(parent_id: str) -> list[dict[str, object]]:
    result: list[dict[str, object]] = [
        {"id": f"{parent_id}.third.cover-left", "kind": "cover-left",
         "units": [-literal for literal in LEFT]},
        {"id": f"{parent_id}.third.cover-right", "kind": "cover-right",
         "units": [-literal for literal in RIGHT]},
    ]
    for li, left_literal in enumerate(LEFT):
        for ri, right_literal in enumerate(RIGHT):
            result.append({
                "id": f"{parent_id}.third.cube-{li}-{ri}", "kind": "cube",
                "left_index": li, "right_index": ri,
                "units": [left_literal, right_literal],
            })
    return result


def selected_nested_cubes(parent: dict) -> list[tuple[dict, dict]]:
    selected = []
    for leaf in parent.get("leaves", {}).values():
        if leaf.get("cell") not in SUPPORTED_CELLS:
            continue
        for job in leaf.get("jobs", []):
            if job.get("kind") == "cube":
                selected.append((leaf, job))
    return selected


def write_manifest(parent_path: Path, output: Path) -> None:
    parent = json.loads(parent_path.read_text())
    if parent.get("schema") != "erdos85-small-high-nested-cube-jobs-v1":
        raise ValueError(f"unsupported parent schema: {parent_path}")
    leaves = {}
    for parent_leaf, parent_job in selected_nested_cubes(parent):
        base = Path(parent_leaf["base"])
        if sha256(base) != parent_leaf["base_sha256"]:
            raise ValueError(f"base CNF hash mismatch: {base}")
        variables, clauses = inspect_dimacs(base)
        if (variables, clauses) != (parent_leaf["variables"],
                                    parent_leaf["base_clauses"]):
            raise ValueError(f"base CNF metadata mismatch: {base}")
        if max(LEFT + RIGHT) > variables:
            raise ValueError("third-level selector exceeds variable header")
        parent_id = parent_job["id"]
        leaves[parent_id] = {
            "cell": parent_leaf["cell"],
            "base": str(base.resolve()),
            "base_sha256": parent_leaf["base_sha256"],
            "variables": variables,
            "base_clauses": clauses,
            "parent_units": [*parent_leaf["parent_units"],
                             *parent_job["units"]],
            "left": list(LEFT),
            "right": list(RIGHT),
            "jobs": third_jobs(parent_id),
        }
    manifest = {
        "schema": "erdos85-small-high-third-cube-jobs-v1",
        "identifier_convention": "one-based DIMACS",
        "parent_manifest": str(parent_path.resolve()),
        "parent_manifest_sha256": sha256(parent_path),
        "hard_nested_cube_jobs": len(leaves),
        "positive_cube_jobs": len(leaves) * len(LEFT) * len(RIGHT),
        "negative_cover_jobs": len(leaves) * 2,
        "leaves": leaves,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name(f".{output.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, output)


def find_job(manifest: dict, job_id: str) -> tuple[dict, dict]:
    matches = [(leaf, job) for leaf in manifest.get("leaves", {}).values()
               for job in leaf.get("jobs", []) if job.get("id") == job_id]
    if len(matches) != 1:
        raise ValueError(f"unknown or duplicated third-level job id: {job_id}")
    return matches[0]


def materialize(manifest_path: Path, job_id: str, output: Path) -> None:
    manifest = json.loads(manifest_path.read_text())
    if manifest.get("schema") != "erdos85-small-high-third-cube-jobs-v1":
        raise ValueError(f"unsupported manifest schema: {manifest_path}")
    parent_path = Path(manifest["parent_manifest"])
    if sha256(parent_path) != manifest["parent_manifest_sha256"]:
        raise ValueError(f"parent manifest hash mismatch: {parent_path}")
    leaf, job = find_job(manifest, job_id)
    base = Path(leaf["base"])
    if sha256(base) != leaf["base_sha256"]:
        raise ValueError(f"base CNF hash mismatch: {base}")
    units = [*leaf["parent_units"], *job["units"]]
    output.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary_name = tempfile.mkstemp(
        prefix=f".{output.name}.", suffix=".tmp", dir=output.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(fd, "wb") as target, base.open("rb") as source:
            replaced = False
            for raw in source:
                if raw.lstrip().startswith(b"p cnf"):
                    if replaced:
                        raise ValueError(f"duplicate DIMACS header: {base}")
                    target.write(f"p cnf {leaf['variables']} "
                                 f"{leaf['base_clauses'] + len(units)}\n".encode())
                    replaced = True
                else:
                    target.write(raw)
            if not replaced:
                raise ValueError(f"missing DIMACS header: {base}")
            for literal in units:
                target.write(f"{literal} 0\n".encode())
        expected = (leaf["variables"], leaf["base_clauses"] + len(units))
        if inspect_dimacs(temporary) != expected:
            raise AssertionError("materialized third-level metadata mismatch")
        os.replace(temporary, output)
    finally:
        temporary.unlink(missing_ok=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    manifest_parser = subparsers.add_parser("manifest")
    manifest_parser.add_argument("--parent-manifest", type=Path, required=True)
    manifest_parser.add_argument("--output", type=Path, required=True)
    materialize_parser = subparsers.add_parser("materialize")
    materialize_parser.add_argument("--manifest", type=Path, required=True)
    materialize_parser.add_argument("--job", required=True)
    materialize_parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "manifest":
        write_manifest(args.parent_manifest.resolve(), args.output.resolve())
    else:
        materialize(args.manifest.resolve(), args.job, args.output.resolve())
    print(f"WROTE {args.output.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
