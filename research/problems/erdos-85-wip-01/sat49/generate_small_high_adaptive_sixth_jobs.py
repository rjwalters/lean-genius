#!/usr/bin/env python3
"""Generate the exact 768-cell adaptive sixth frontier for the hard B1 leaf."""

from __future__ import annotations

import argparse
import json
import os
import tempfile
from hashlib import sha256 as hashlib_sha256
from pathlib import Path


SIXTH_LEFT = (206, 249, 717, 746, 774, 801, 827, 852)
SIXTH_RIGHT = (207, 250, 718, 747, 775, 802, 828, 853)
SIXTH_POOL = frozenset((3, 4, 5, 6, 7))
STRUCTURAL_THEOREMS = (
    "Erdos85.orderFortyNineThreeHighB1AdaptiveFifthResidual_exists_of_aligned",
    "Erdos85.orderFortyNineThreeHighB1AdaptiveSixthResidual_exists_of_aligned",
    "Erdos85.orderFortyNineThreeHighB1AdaptiveSixthFastResidual_of_graph",
    "Erdos85.orderFortyNineThreeHighB1AdaptiveSixthResidual_card_twelve",
)


def sha256(path: Path) -> str:
    digest = hashlib_sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def inspect_dimacs(path: Path) -> tuple[int, int]:
    header = None
    clauses = 0
    with path.open("rb") as source:
        for raw in source:
            line = raw.lstrip()
            if not line or line.startswith(b"c"):
                continue
            if line.startswith(b"p"):
                fields = line.split()
                if len(fields) != 4 or fields[:2] != [b"p", b"cnf"]:
                    raise ValueError(f"malformed DIMACS header: {path}")
                if header is not None:
                    raise ValueError(f"duplicate DIMACS header: {path}")
                header = (int(fields[2]), int(fields[3]))
            else:
                clauses += 1
    if header is None:
        raise ValueError(f"missing DIMACS header: {path}")
    if clauses != header[1]:
        raise ValueError(
            f"DIMACS clause mismatch: header={header[1]} actual={clauses}"
        )
    return header


def forbidden_index(ri: int, ai: int, bi: int, ci: int) -> int:
    """Excluded high-2 index, determined by the position of fifth index 2."""
    if ri == 2:
        return 4
    if ai == 2:
        return 5
    if bi == 2:
        return 6
    if ci == 2:
        return 7
    raise ValueError("fifth residual has no distinguished index 2")


def sixth_residual(
    ri: int, ai: int, bi: int, ci: int, di: int, ei: int
) -> bool:
    """Ordered distinct pairs from the state-dependent four-index set."""
    forbidden = forbidden_index(ri, ai, bi, ci)
    return (
        di in SIXTH_POOL
        and ei in SIXTH_POOL
        and di != forbidden
        and ei != forbidden
        and di != ei
    )


def sixth_jobs(
    parent_id: str, ri: int, ai: int, bi: int, ci: int
) -> list[dict[str, object]]:
    # Alignment supplies one selector at each of vertices 24 and 25.  The
    # graph consumer forces their ordered pair into this exact residue, so no
    # negative cover job is needed.
    return [
        {
            "id": f"{parent_id}.sixth.cube-{di}-{ei}",
            "kind": "cube",
            "left_selector_index": di,
            "right_selector_index": ei,
            "units": [SIXTH_LEFT[di], SIXTH_RIGHT[ei]],
        }
        for di in range(8)
        for ei in range(8)
        if sixth_residual(ri, ai, bi, ci, di, ei)
    ]


def fifth_cube_leaves(parent: dict) -> list[tuple[str, dict, dict]]:
    result = []
    for parent_id, leaf in parent.get("leaves", {}).items():
        if leaf.get("cell") != "h3_b1":
            raise ValueError(f"non-B1 fifth parent leaf: {parent_id}")
        for job in leaf.get("jobs", []):
            if job.get("kind") != "cube":
                raise ValueError(f"unexpected fifth job kind: {job.get('id')}")
            result.append((parent_id, leaf, job))
    return result


def write_manifest(parent_path: Path, output: Path) -> None:
    parent = json.loads(parent_path.read_text())
    if parent.get("schema") != "erdos85-small-high-adaptive-fifth-jobs-v1":
        raise ValueError(f"unsupported parent schema: {parent_path}")
    if parent.get("positive_residual_jobs") != 64:
        raise ValueError("adaptive fifth parent does not certify 64 residual jobs")
    if parent.get("negative_cover_jobs") != 0:
        raise ValueError("adaptive fifth parent unexpectedly contains cover jobs")

    leaves = {}
    seen_units: set[tuple[int, ...]] = set()
    for fifth_parent_id, parent_leaf, fifth_job in fifth_cube_leaves(parent):
        base = Path(parent_leaf["base"])
        if sha256(base) != parent_leaf["base_sha256"]:
            raise ValueError(f"base CNF hash mismatch: {base}")
        variables, clauses = inspect_dimacs(base)
        if (variables, clauses) != (
            parent_leaf["variables"],
            parent_leaf["base_clauses"],
        ):
            raise ValueError(f"base CNF metadata mismatch: {base}")
        if max(SIXTH_LEFT + SIXTH_RIGHT) > variables:
            raise ValueError("sixth selector exceeds variable header")

        parent_units = [*parent_leaf["parent_units"], *fifth_job["units"]]
        units_key = tuple(parent_units)
        if units_key in seen_units:
            raise ValueError(f"duplicate fifth residual units: {fifth_job['id']}")
        seen_units.add(units_key)
        fifth_id = str(fifth_job["id"])
        if not fifth_id.startswith(f"{fifth_parent_id}.fifth.cube-"):
            raise ValueError(f"malformed fifth job id: {fifth_id}")
        ri = parent_leaf["third_right_index"]
        ai = parent_leaf["fourth_left_index"]
        bi = parent_leaf["fourth_right_index"]
        ci = fifth_job["selector_index"]
        forbidden = forbidden_index(ri, ai, bi, ci)
        leaves[fifth_id] = {
            "cell": "h3_b1",
            "base": str(base.resolve()),
            "base_sha256": parent_leaf["base_sha256"],
            "variables": variables,
            "base_clauses": clauses,
            "third_left_index": parent_leaf["third_left_index"],
            "third_right_index": parent_leaf["third_right_index"],
            "fourth_left_index": parent_leaf["fourth_left_index"],
            "fourth_right_index": parent_leaf["fourth_right_index"],
            "fifth_selector_index": fifth_job["selector_index"],
            "sixth_forbidden_index": forbidden,
            "parent_units": parent_units,
            "sixth_left_selectors": list(SIXTH_LEFT),
            "sixth_right_selectors": list(SIXTH_RIGHT),
            "jobs": sixth_jobs(fifth_id, ri, ai, bi, ci),
        }

    positive = sum(len(leaf["jobs"]) for leaf in leaves.values())
    job_ids = [job["id"] for leaf in leaves.values() for job in leaf["jobs"]]
    unit_sets = [
        tuple([*leaf["parent_units"], *job["units"]])
        for leaf in leaves.values()
        for job in leaf["jobs"]
    ]
    if (len(leaves), positive) != (64, 768):
        raise AssertionError(
            f"adaptive sixth census mismatch: {(len(leaves), positive)}"
        )
    if len(job_ids) != len(set(job_ids)):
        raise AssertionError("duplicate adaptive sixth job id")
    if len(unit_sets) != len(set(unit_sets)):
        raise AssertionError("duplicate adaptive sixth unit assignment")
    forbidden_counts = {
        i: sum(leaf["sixth_forbidden_index"] == i for leaf in leaves.values())
        for i in (4, 5, 6, 7)
    }
    if forbidden_counts != {4: 16, 5: 16, 6: 16, 7: 16}:
        raise AssertionError(
            f"adaptive sixth forbidden-index mismatch: {forbidden_counts}"
        )

    manifest = {
        "schema": "erdos85-small-high-adaptive-sixth-jobs-v1",
        "identifier_convention": "one-based DIMACS",
        "parent_manifest": str(parent_path.resolve()),
        "parent_manifest_sha256": sha256(parent_path),
        "structural_theorems": list(STRUCTURAL_THEOREMS),
        "sixth_left_selectors": list(SIXTH_LEFT),
        "sixth_right_selectors": list(SIXTH_RIGHT),
        "sixth_selector_pool": sorted(SIXTH_POOL),
        "forbidden_index_counts": {
            str(i): forbidden_counts[i] for i in (4, 5, 6, 7)
        },
        "live_fifth_cells": len(leaves),
        "children_per_fifth_cell": 12,
        "positive_residual_jobs": positive,
        "negative_cover_jobs": 0,
        "structurally_pruned_positive_jobs": 64 * 64 - positive,
        "leaves": leaves,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name(f".{output.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, output)


def find_job(manifest: dict, job_id: str) -> tuple[dict, dict]:
    matches = [
        (leaf, job)
        for leaf in manifest.get("leaves", {}).values()
        for job in leaf.get("jobs", [])
        if job.get("id") == job_id
    ]
    if len(matches) != 1:
        raise ValueError(f"unknown or duplicated sixth-level job id: {job_id}")
    return matches[0]


def materialize(manifest_path: Path, job_id: str, output: Path) -> None:
    manifest = json.loads(manifest_path.read_text())
    if manifest.get("schema") != "erdos85-small-high-adaptive-sixth-jobs-v1":
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
            raise AssertionError("materialized adaptive sixth metadata mismatch")
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
