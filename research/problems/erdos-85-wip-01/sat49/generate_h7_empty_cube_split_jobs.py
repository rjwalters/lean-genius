#!/usr/bin/env python3
"""Create deterministic one-level binary jobs for missing canonical H7 cubes."""

from __future__ import annotations

import argparse
import json
import os
import tempfile
from collections import defaultdict
from pathlib import Path

import generate_h7_empty_cube_manifest as inventory
import probe_h7_binary_lookahead as lookahead


SCHEMA = "erdos85-h7-canonical-empty-cube-splits-v1"


def choose_split(clauses: list[tuple[int, ...]],
                 occurrence: dict[int, list[int]],
                 parent_units: list[int], candidate_max: int = 861) -> dict:
    consistent, baseline = lookahead.propagate(
        clauses, occurrence, tuple(parent_units))
    if not consistent:
        raise ValueError("parent cube is already unit-inconsistent")
    ranked = []
    baseline_literals = tuple(
        variable if value else -variable for variable, value in baseline.items())
    for variable in range(1, candidate_max + 1):
        if variable in baseline:
            continue
        branches = []
        for literal in (-variable, variable):
            branch_consistent, assignment = lookahead.propagate(
                clauses, occurrence, (*baseline_literals, literal))
            branches.append({
                "consistent": branch_consistent,
                "forced": len(assignment) - len(baseline),
            })
        gains = [branch["forced"] for branch in branches]
        ranked.append(((-min(gains), -(gains[0] * gains[1]),
                        -sum(gains), variable), variable, branches))
    if not ranked:
        raise ValueError("no unfixed split variable remains")
    _, variable, branches = min(ranked)
    return {
        "variable": variable,
        "baseline_assigned": len(baseline),
        "false": branches[0],
        "true": branches[1],
    }


def build_split_manifest(parent: dict, base: Path,
                         only: set[str] | None = None) -> dict:
    if parent.get("schema") != inventory.SCHEMA:
        raise ValueError("unsupported canonical H7 parent manifest schema")
    if inventory.sha256(base) != parent.get("base_sha256"):
        raise ValueError("bound compact base hash mismatch")
    variables, clauses = lookahead.read_dimacs(base)
    if (variables, len(clauses)) != (parent.get("variables"),
                                     parent.get("base_clauses")):
        raise ValueError("bound compact base shape mismatch")
    occurrence: dict[int, list[int]] = defaultdict(list)
    for clause_index, clause in enumerate(clauses):
        for literal in clause:
            occurrence[literal].append(clause_index)
    missing = [job for job in parent.get("jobs", [])
               if job.get("status") == "missing" and
               (only is None or job.get("id") in only)]
    if only is not None and {job["id"] for job in missing} != only:
        raise ValueError("requested parent ID is absent or already certified")
    splits = []
    for job in missing:
        choice = choose_split(clauses, occurrence, job["units"])
        variable = choice["variable"]
        splits.append({
            "parent_id": job["id"],
            "edge_count": job["edge_count"],
            "type_index": job["type_index"],
            "parent_units": job["units"],
            "split_variable": variable,
            "ranking": choice,
            "leaves": [
                {"id": f"{job['id']}.split-{bit}", "value": bool(bit),
                 "units": [*job["units"], variable if bit else -variable]}
                for bit in (0, 1)
            ],
        })
    return {
        "schema": SCHEMA,
        "identifier_convention": "one-based signed DIMACS",
        "parent_schema": parent["schema"],
        "parent_manifest_sha256": None,
        "base_sha256": parent["base_sha256"],
        "variables": variables,
        "base_clauses": len(clauses),
        "parent_count": len(splits),
        "leaf_count": 2 * len(splits),
        "splits": splits,
    }


def materialize(base: Path, manifest: dict, leaf_id: str, output: Path) -> None:
    if manifest.get("schema") != SCHEMA:
        raise ValueError("unsupported split manifest schema")
    if inventory.sha256(base) != manifest.get("base_sha256"):
        raise ValueError("split base hash mismatch")
    matches = [leaf for split in manifest.get("splits", [])
               for leaf in split["leaves"] if leaf["id"] == leaf_id]
    if len(matches) != 1:
        raise ValueError(f"unknown or duplicate split leaf: {leaf_id}")
    units = matches[0]["units"]
    output.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{output.name}.", suffix=".tmp", dir=output.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "wb") as target, base.open("rb") as source:
            replaced = False
            for raw in source:
                if raw.lstrip().startswith(b"p cnf"):
                    if replaced:
                        raise ValueError("duplicate DIMACS header")
                    raw = (f"p cnf {manifest['variables']} "
                           f"{manifest['base_clauses'] + len(units)}\n").encode()
                    replaced = True
                target.write(raw)
            if not replaced:
                raise ValueError("missing DIMACS header")
            for unit in units:
                target.write(f"{unit} 0\n".encode())
        os.replace(temporary, output)
    finally:
        temporary.unlink(missing_ok=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    create = commands.add_parser("manifest")
    create.add_argument("--parent-manifest", type=Path, required=True)
    create.add_argument("--base", type=Path, required=True)
    create.add_argument("--only", nargs="*")
    create.add_argument("--output", type=Path, required=True)
    emit = commands.add_parser("materialize")
    emit.add_argument("--manifest", type=Path, required=True)
    emit.add_argument("--base", type=Path, required=True)
    emit.add_argument("--leaf", required=True)
    emit.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "manifest":
        parent = json.loads(args.parent_manifest.read_text())
        result = build_split_manifest(parent, args.base, set(args.only) if args.only else None)
        result["parent_manifest_sha256"] = inventory.sha256(args.parent_manifest)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    else:
        result = json.loads(args.manifest.read_text())
        materialize(args.base, result, args.leaf, args.output)
    print(f"WROTE {args.output}")


if __name__ == "__main__":
    main()
