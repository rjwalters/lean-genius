#!/usr/bin/env python3
"""Generate the exact 64-cell adaptive fifth frontier for the hard B1 leaf."""

from __future__ import annotations

import argparse
import json
import os
import tempfile
from hashlib import sha256 as hashlib_sha256
from pathlib import Path


ADAPTIVE_THIRD_LEFT = (156, 243, 516, 551, 585, 618, 650, 681)
ADAPTIVE_THIRD_RIGHT = (158, 245, 518, 553, 587, 620, 652, 683)
FOURTH_LEFT = (159, 246, 519, 554, 588, 621, 653, 684)
FOURTH_RIGHT = (160, 247, 520, 555, 589, 622, 654, 685)
FIFTH = (161, 248, 521, 556, 590, 623, 655, 686)
STRUCTURAL_THEOREMS = (
    "Erdos85.orderFortyNineThreeHighB1AdaptiveFourthResidual_of_aligned",
    "Erdos85.orderFortyNineThreeHighB1AdaptiveFifthResidual_of_graph",
    "Erdos85.orderFortyNineThreeHighB1AdaptiveFifthResidual_count",
    "Erdos85.orderFortyNineThreeHighB1AdaptiveFifthDeadParent_count",
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


def third_residual(li: int, ri: int) -> bool:
    return li >= 4 and ri >= 2 and ri != 3 and li != ri


def live_index(i: int) -> bool:
    return i == 2 or i >= 4


def live_mate(i: int) -> int:
    return {4: 5, 5: 4, 6: 7, 7: 6}.get(i, i)


def fourth_residual(li: int, ri: int, ai: int, bi: int) -> bool:
    return (
        third_residual(li, ri)
        and live_index(ai)
        and live_index(bi)
        and ai != bi
        and ai not in (li, ri)
        and bi not in (li, ri)
        and ai != live_mate(ri)
    )


def fifth_dead_parent(li: int, ri: int, ai: int, bi: int) -> bool:
    """The sixteen fourth parents whose eight fifth children all contain C4."""
    return (
        fourth_residual(li, ri, ai, bi)
        and {ri, ai} == {2, live_mate(li)}
        and bi not in {2, li, live_mate(li)}
    )


def fifth_residual(li: int, ri: int, ai: int, bi: int, ci: int) -> bool:
    """The unique complement selector in each of the 64 nondead parents."""
    return (
        fourth_residual(li, ri, ai, bi)
        and not fifth_dead_parent(li, ri, ai, bi)
        and live_index(ci)
        and ci not in {li, ri, ai, bi}
    )


def third_residual_parents() -> list[tuple[int, int]]:
    return [
        (li, ri)
        for li in range(8)
        for ri in range(8)
        if third_residual(li, ri)
    ]


def fourth_residual_parents() -> list[tuple[int, int, int, int]]:
    return [
        (li, ri, ai, bi)
        for li in range(8)
        for ri in range(8)
        for ai in range(8)
        for bi in range(8)
        if fourth_residual(li, ri, ai, bi)
    ]


def fifth_jobs(
    parent_id: str, li: int, ri: int, ai: int, bi: int
) -> list[dict[str, object]]:
    jobs: list[dict[str, object]] = [
        {
            "id": f"{parent_id}.fifth.cover",
            "kind": "cover",
            "units": [-literal for literal in FIFTH],
        },
    ]
    for ci, literal in enumerate(FIFTH):
        if not fifth_residual(li, ri, ai, bi, ci):
            continue
        jobs.append(
            {
                "id": f"{parent_id}.fifth.cube-{ci}",
                "kind": "cube",
                "selector_index": ci,
                "units": [literal],
            }
        )
    return jobs


def canonical_leaf(parent: dict) -> tuple[str, dict]:
    leaves = parent.get("leaves", {})
    if not isinstance(leaves, dict) or len(leaves) != 1:
        raise ValueError("adaptive fourth parent must contain exactly one leaf")
    parent_id, leaf = next(iter(leaves.items()))
    if parent_id != "h3_b1.cube-0-0.nested.cube-0-0":
        raise ValueError(f"unexpected adaptive fourth parent: {parent_id}")
    if leaf.get("cell") != "h3_b1":
        raise ValueError("adaptive fourth parent is not the B1 cell")
    return parent_id, leaf


def write_manifest(parent_path: Path, output: Path) -> None:
    parent = json.loads(parent_path.read_text())
    if parent.get("schema") != "erdos85-small-high-third-cube-jobs-v1":
        raise ValueError(f"unsupported parent schema: {parent_path}")
    root_id, root = canonical_leaf(parent)
    base = Path(root["base"])
    if sha256(base) != root["base_sha256"]:
        raise ValueError(f"base CNF hash mismatch: {base}")
    variables, clauses = inspect_dimacs(base)
    if (variables, clauses) != (root["variables"], root["base_clauses"]):
        raise ValueError(f"base CNF metadata mismatch: {base}")
    if max(
        ADAPTIVE_THIRD_LEFT
        + ADAPTIVE_THIRD_RIGHT
        + FOURTH_LEFT
        + FOURTH_RIGHT
        + FIFTH
    ) > variables:
        raise ValueError("adaptive selector exceeds variable header")

    leaves = {}
    for li, ri, ai, bi in fourth_residual_parents():
        parent_id = (
            f"{root_id}.adaptive-third.cube-{li}-{ri}"
            f".fourth.cube-{ai}-{bi}"
        )
        parent_units = [
            *root["parent_units"],
            ADAPTIVE_THIRD_LEFT[li],
            ADAPTIVE_THIRD_RIGHT[ri],
            FOURTH_LEFT[ai],
            FOURTH_RIGHT[bi],
        ]
        leaves[parent_id] = {
            "cell": "h3_b1",
            "base": str(base.resolve()),
            "base_sha256": root["base_sha256"],
            "variables": variables,
            "base_clauses": clauses,
            "third_left_index": li,
            "third_right_index": ri,
            "fourth_left_index": ai,
            "fourth_right_index": bi,
            "parent_units": parent_units,
            "selectors": list(FIFTH),
            "jobs": fifth_jobs(parent_id, li, ri, ai, bi),
        }

    positive = sum(
        job["kind"] == "cube"
        for leaf in leaves.values()
        for job in leaf["jobs"]
    )
    covers = sum(
        job["kind"] == "cover"
        for leaf in leaves.values()
        for job in leaf["jobs"]
    )
    dead_parents = sum(
        fifth_dead_parent(li, ri, ai, bi)
        for li, ri, ai, bi in fourth_residual_parents()
    )
    if (len(leaves), positive, covers, dead_parents) != (80, 64, 80, 16):
        raise AssertionError(
            "adaptive fifth census mismatch: "
            f"{(len(leaves), positive, covers, dead_parents)}"
        )
    manifest = {
        "schema": "erdos85-small-high-adaptive-fifth-jobs-v1",
        "identifier_convention": "one-based DIMACS",
        "parent_manifest": str(parent_path.resolve()),
        "parent_manifest_sha256": sha256(parent_path),
        "structural_theorems": list(STRUCTURAL_THEOREMS),
        "adaptive_third_left": list(ADAPTIVE_THIRD_LEFT),
        "adaptive_third_right": list(ADAPTIVE_THIRD_RIGHT),
        "fourth_left": list(FOURTH_LEFT),
        "fourth_right": list(FOURTH_RIGHT),
        "fifth_selectors": list(FIFTH),
        "live_third_cells": len(third_residual_parents()),
        "live_fourth_cells": len(leaves),
        "structurally_dead_fourth_parents": dead_parents,
        "positive_residual_jobs": positive,
        "negative_cover_jobs": covers,
        "structurally_pruned_positive_jobs": 576,
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
        raise ValueError(f"unknown or duplicated fifth-level job id: {job_id}")
    return matches[0]


def materialize(manifest_path: Path, job_id: str, output: Path) -> None:
    manifest = json.loads(manifest_path.read_text())
    if manifest.get("schema") != "erdos85-small-high-adaptive-fifth-jobs-v1":
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
            raise AssertionError("materialized adaptive fifth metadata mismatch")
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
