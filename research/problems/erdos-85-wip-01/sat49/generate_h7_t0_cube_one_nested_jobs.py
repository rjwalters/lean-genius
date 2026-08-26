#!/usr/bin/env python3
"""Materialize second-level checked grids for hard h7/t0 cube-one leaves."""

from __future__ import annotations

import argparse
import json
import os
import tempfile
from pathlib import Path

from generate_h7_t0_cube_one_cover_jobs import inspect_dimacs, sha256


LEFT = (1255, 1289, 1323, 1357, 1391, 1425, 1459, 1493)
RIGHT = (1255, 1520, 1547, 1574, 1601, 1628, 1655, 1682)


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


def parent_jobs(parent: dict) -> dict[str, dict]:
    jobs = parent.get("jobs")
    if not isinstance(jobs, list) or len(jobs) != 66:
        raise ValueError("parent manifest must contain exactly 66 jobs")
    result = {}
    for job in jobs:
        job_id = job.get("id")
        if not isinstance(job_id, str) or job_id in result:
            raise ValueError(f"invalid or duplicate parent job id: {job_id}")
        result[job_id] = job
    return result


def nested_jobs(parent_id: str) -> list[dict[str, object]]:
    result: list[dict[str, object]] = [
        {"id": f"{parent_id}.nested.cover-left", "kind": "cover-left",
         "units": [-literal for literal in LEFT]},
        {"id": f"{parent_id}.nested.cover-right", "kind": "cover-right",
         "units": [-literal for literal in RIGHT]},
    ]
    for left_index, left in enumerate(LEFT):
        for right_index, right in enumerate(RIGHT):
            result.append({
                "id": (f"{parent_id}.nested.cube-"
                       f"{left_index}-{right_index}"),
                "kind": "cube",
                "left_index": left_index,
                "right_index": right_index,
                "units": [left, right],
            })
    return result


def write_manifest(parent_path: Path, hard_path: Path, output: Path) -> None:
    parent = json.loads(parent_path.read_text())
    if parent.get("schema") != "erdos85-h7-t0-cube1-cover-v1":
        raise ValueError(f"unsupported parent schema: {parent_path}")
    if parent.get("left") != [1254, 1288, 1322, 1356, 1390, 1424, 1458, 1492]:
        raise ValueError("unexpected parent left selectors")
    if parent.get("right") != [1254, 1519, 1546, 1573, 1600, 1627, 1654, 1681]:
        raise ValueError("unexpected parent right selectors")
    lookup = parent_jobs(parent)
    hard_ids = read_hard_jobs(hard_path)
    base = Path(parent["base"])
    if sha256(base) != parent["base_sha256"]:
        raise ValueError(f"base CNF hash mismatch: {base}")
    variables, clauses = inspect_dimacs(base)
    if (variables, clauses) != (parent["variables"], parent["base_clauses"]):
        raise ValueError("base CNF shape disagrees with parent manifest")
    if max(LEFT + RIGHT) > variables:
        raise ValueError("nested selector exceeds the base variable header")

    leaves = {}
    for parent_id in hard_ids:
        if parent_id not in lookup:
            raise ValueError(f"unknown parent job: {parent_id}")
        parent_job = lookup[parent_id]
        if parent_job.get("kind") != "cube":
            raise ValueError(f"nested split requires a positive parent cube: {parent_id}")
        if set(parent_job["units"]) & set(LEFT + RIGHT):
            raise ValueError(f"nested selectors overlap parent units: {parent_id}")
        leaves[parent_id] = {
            "parent_left_index": parent_job["left_index"],
            "parent_right_index": parent_job["right_index"],
            "parent_units": parent_job["units"],
            "left": list(LEFT),
            "right": list(RIGHT),
            "jobs": nested_jobs(parent_id),
        }
    manifest = {
        "schema": "erdos85-h7-t0-cube1-nested-jobs-v1",
        "identifier_convention": "one-based DIMACS",
        "parent_manifest": str(parent_path.resolve()),
        "parent_manifest_sha256": sha256(parent_path),
        "base": str(base.resolve()),
        "base_sha256": parent["base_sha256"],
        "variables": variables,
        "base_clauses": clauses,
        "hard_parent_jobs": len(leaves),
        "positive_cube_jobs": 64 * len(leaves),
        "negative_cover_jobs": 2 * len(leaves),
        "leaves": leaves,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name(f".{output.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, output)


def find_job(manifest: dict, job_id: str) -> tuple[dict, dict]:
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
    if manifest.get("schema") != "erdos85-h7-t0-cube1-nested-jobs-v1":
        raise ValueError(f"unsupported nested manifest schema: {manifest_path}")
    parent = Path(manifest["parent_manifest"])
    base = Path(manifest["base"])
    if sha256(parent) != manifest["parent_manifest_sha256"]:
        raise ValueError(f"parent manifest hash mismatch: {parent}")
    if sha256(base) != manifest["base_sha256"]:
        raise ValueError(f"base CNF hash mismatch: {base}")
    leaf, job = find_job(manifest, job_id)
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
                    raw = (f"p cnf {manifest['variables']} "
                           f"{manifest['base_clauses'] + len(units)}\n").encode()
                    replaced = True
                target.write(raw)
            if not replaced:
                raise ValueError(f"missing DIMACS header: {base}")
            for literal in units:
                target.write(f"{literal} 0\n".encode())
        expected = (manifest["variables"], manifest["base_clauses"] + len(units))
        if inspect_dimacs(temporary) != expected:
            raise AssertionError("materialized nested DIMACS shape mismatch")
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
