#!/usr/bin/env python3
"""Generate third-level checked-grid jobs for hard h3 b1/c1 nested cubes."""

from __future__ import annotations

import argparse
import json
import os
import re
import tempfile
from pathlib import Path

from generate_small_high_cube_jobs import inspect_dimacs, sha256


# One-based DIMACS identifiers pinned by
# Erdos85OrderFortyNineSmallHighThirdCubeSelectors.lean.
LEFT = (164, 208, 293, 334, 374, 413, 451, 488)
RIGHT = (165, 209, 294, 335, 375, 414, 452, 489)
SUPPORTED_CELLS = {"h3_b1", "h3_c1"}
JOB_ID = re.compile(
    r"h3_(?:b1|c1)\.cube-[0-7]-[0-7]\.nested\.cube-[0-7]-[0-7]"
    r"\.third\.(?:cover-(?:left|right)|cube-[0-7]-[0-7])"
)


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


def selected_nested_cubes(parent: dict, hard_ids: list[str] | None
                          ) -> list[tuple[dict, dict]]:
    lookup = {}
    for leaf in parent.get("leaves", {}).values():
        if leaf.get("cell") not in SUPPORTED_CELLS:
            continue
        for job in leaf.get("jobs", []):
            if job.get("kind") == "cube":
                job_id = job.get("id")
                if not isinstance(job_id, str) or job_id in lookup:
                    raise ValueError(f"invalid or duplicate nested job id: {job_id}")
                lookup[job_id] = (leaf, job)
    if hard_ids is None:
        return list(lookup.values())
    unknown = [job_id for job_id in hard_ids if job_id not in lookup]
    if unknown:
        raise ValueError(f"unknown, non-cube, or unsupported hard jobs: {unknown}")
    return [lookup[job_id] for job_id in hard_ids]


def write_manifest(parent_path: Path, hard_path: Path | None,
                   output: Path) -> None:
    parent = json.loads(parent_path.read_text())
    if parent.get("schema") != "erdos85-small-high-nested-cube-jobs-v1":
        raise ValueError(f"unsupported parent schema: {parent_path}")
    hard_ids = read_hard_jobs(hard_path) if hard_path is not None else None
    leaves = {}
    validated_bases = set()
    for parent_leaf, parent_job in selected_nested_cubes(parent, hard_ids):
        base = Path(parent_leaf["base"])
        if base not in validated_bases:
            if sha256(base) != parent_leaf["base_sha256"]:
                raise ValueError(f"base CNF hash mismatch: {base}")
            variables, clauses = inspect_dimacs(base)
            if (variables, clauses) != (parent_leaf["variables"],
                                        parent_leaf["base_clauses"]):
                raise ValueError(f"base CNF metadata mismatch: {base}")
            validated_bases.add(base)
        variables = parent_leaf["variables"]
        clauses = parent_leaf["base_clauses"]
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
        "hard_jobs": str(hard_path.resolve()) if hard_path is not None else None,
        "hard_jobs_sha256": sha256(hard_path) if hard_path is not None else None,
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
    if manifest.get("hard_jobs") is not None:
        hard_path = Path(manifest["hard_jobs"])
        if sha256(hard_path) != manifest["hard_jobs_sha256"]:
            raise ValueError(f"hard-job file hash mismatch: {hard_path}")
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


def write_queue(manifest_path: Path, output: Path, receipt: Path) -> None:
    """Export the manifest's exact child order with a deterministic receipt."""
    manifest = json.loads(manifest_path.read_text())
    if manifest.get("schema") != "erdos85-small-high-third-cube-jobs-v1":
        raise ValueError(f"unsupported manifest schema: {manifest_path}")
    parent_path = Path(manifest["parent_manifest"])
    if sha256(parent_path) != manifest["parent_manifest_sha256"]:
        raise ValueError(f"parent manifest hash mismatch: {parent_path}")
    hard_path_text = manifest.get("hard_jobs")
    if hard_path_text is not None:
        hard_path = Path(hard_path_text)
        if sha256(hard_path) != manifest.get("hard_jobs_sha256"):
            raise ValueError(f"hard-job file hash mismatch: {hard_path}")

    ids: list[str] = []
    kinds: dict[str, int] = {"cube": 0, "cover-left": 0, "cover-right": 0}
    leaves = manifest.get("leaves")
    if not isinstance(leaves, dict):
        raise ValueError("third-level manifest leaves must be an object")
    for parent_id, leaf in leaves.items():
        if not isinstance(parent_id, str) or not isinstance(leaf, dict):
            raise ValueError("invalid third-level leaf entry")
        jobs = leaf.get("jobs")
        if not isinstance(jobs, list):
            raise ValueError(f"invalid jobs for third-level leaf: {parent_id}")
        for job in jobs:
            if not isinstance(job, dict):
                raise ValueError(f"invalid job for third-level leaf: {parent_id}")
            job_id, kind = job.get("id"), job.get("kind")
            if (not isinstance(job_id, str) or
                    not job_id.startswith(parent_id + ".third.") or
                    JOB_ID.fullmatch(job_id) is None):
                raise ValueError(f"invalid third-level job id: {job_id}")
            if kind not in kinds:
                raise ValueError(f"invalid third-level job kind: {kind}")
            ids.append(job_id)
            kinds[kind] += 1
    if len(ids) != len(set(ids)):
        raise ValueError("third-level manifest contains duplicate job ids")
    expected_leaves = manifest.get("hard_nested_cube_jobs")
    expected_cubes = manifest.get("positive_cube_jobs")
    expected_covers = manifest.get("negative_cover_jobs")
    if (expected_leaves != len(leaves) or expected_cubes != kinds["cube"] or
            expected_covers != kinds["cover-left"] + kinds["cover-right"] or
            kinds["cover-left"] != len(leaves) or
            kinds["cover-right"] != len(leaves)):
        raise ValueError("third-level manifest count metadata mismatch")

    output.parent.mkdir(parents=True, exist_ok=True)
    queue_text = "".join(f"{job_id}\n" for job_id in ids)
    queue_tmp = output.with_name(f".{output.name}.{os.getpid()}.tmp")
    queue_tmp.write_text(queue_text)
    os.replace(queue_tmp, output)
    receipt_data = {
        "schema": "erdos85-small-high-third-queue-receipt-v1",
        "manifest": str(manifest_path.resolve()),
        "manifest_sha256": sha256(manifest_path),
        "parent_manifest_sha256": manifest["parent_manifest_sha256"],
        "hard_jobs_sha256": manifest.get("hard_jobs_sha256"),
        "queue": str(output.resolve()),
        "queue_sha256": sha256(output),
        "jobs": len(ids),
        "positive_cube_jobs": kinds["cube"],
        "negative_cover_jobs": kinds["cover-left"] + kinds["cover-right"],
    }
    receipt.parent.mkdir(parents=True, exist_ok=True)
    receipt_tmp = receipt.with_name(f".{receipt.name}.{os.getpid()}.tmp")
    receipt_tmp.write_text(json.dumps(receipt_data, indent=2, sort_keys=True) + "\n")
    os.replace(receipt_tmp, receipt)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)
    manifest_parser = subparsers.add_parser("manifest")
    manifest_parser.add_argument("--parent-manifest", type=Path, required=True)
    manifest_parser.add_argument("--hard-jobs", type=Path)
    manifest_parser.add_argument("--output", type=Path, required=True)
    materialize_parser = subparsers.add_parser("materialize")
    materialize_parser.add_argument("--manifest", type=Path, required=True)
    materialize_parser.add_argument("--job", required=True)
    materialize_parser.add_argument("--output", type=Path, required=True)
    queue_parser = subparsers.add_parser("queue")
    queue_parser.add_argument("--manifest", type=Path, required=True)
    queue_parser.add_argument("--output", type=Path, required=True)
    queue_parser.add_argument("--receipt", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "manifest":
        write_manifest(args.parent_manifest.resolve(),
                       args.hard_jobs.resolve() if args.hard_jobs else None,
                       args.output.resolve())
    elif args.command == "materialize":
        materialize(args.manifest.resolve(), args.job, args.output.resolve())
    else:
        write_queue(args.manifest.resolve(), args.output.resolve(),
                    args.receipt.resolve())
    print(f"WROTE {args.output.resolve()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
