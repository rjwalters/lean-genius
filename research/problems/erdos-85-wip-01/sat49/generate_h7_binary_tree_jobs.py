#!/usr/bin/env python3
"""Build and materialize a complete uniform binary tree below one H7 leaf."""

from __future__ import annotations

import argparse
import itertools
import json
import os
import tempfile
from pathlib import Path

from generate_h7_t0_cube_one_cover_jobs import inspect_dimacs, sha256


def expected_leaves(parent_id: str, split_variables: list[int]) -> list[dict]:
    leaves = []
    for bits in itertools.product((False, True), repeat=len(split_variables)):
        suffix = "".join("1" if bit else "0" for bit in bits)
        path_units = [variable if bit else -variable
                      for variable, bit in zip(split_variables, bits)]
        leaves.append({"id": f"{parent_id}.binary.leaf-{suffix}",
                       "bits": list(bits), "path_units": path_units})
    return leaves


def validate_bound_manifest(manifest: dict) -> tuple[Path, list[dict]]:
    if manifest.get("schema") != "erdos85-h7-binary-tree-jobs-v1":
        raise ValueError("unsupported binary-tree manifest schema")
    parent_path = Path(manifest["parent_manifest"])
    base = Path(manifest["base"])
    if (sha256(parent_path) != manifest["parent_manifest_sha256"] or
            sha256(base) != manifest["base_sha256"]):
        raise ValueError("bound parent/base hash mismatch")
    parent = json.loads(parent_path.read_text())
    if parent.get("schema") != "erdos85-h7-t0-cube1-cover-v1":
        raise ValueError("unsupported bound parent manifest schema")
    matches = [job for job in parent.get("jobs", [])
               if job.get("id") == manifest.get("parent_id")]
    if len(matches) != 1 or matches[0].get("kind") != "cube":
        raise ValueError("bound parent must be one unique positive cube job")
    parent_units = matches[0].get("units")
    split_variables = manifest.get("split_variables")
    if (parent_units != manifest.get("parent_units") or
            not isinstance(split_variables, list) or not split_variables or
            any(not isinstance(variable, int) for variable in split_variables) or
            len(set(split_variables)) != len(split_variables)):
        raise ValueError("binary-tree manifest binding mismatch")
    variables, clauses = inspect_dimacs(base)
    if (parent.get("base") != manifest.get("base") or
            parent.get("base_sha256") != manifest.get("base_sha256") or
            (variables, clauses) !=
            (manifest.get("variables"), manifest.get("base_clauses")) or
            (variables, clauses) !=
            (parent.get("variables"), parent.get("base_clauses"))):
        raise ValueError("bound base CNF metadata mismatch")
    if (any(not 1 <= variable <= variables for variable in split_variables) or
            set(map(abs, parent_units)) & set(split_variables)):
        raise ValueError("split variable outside header or fixed by parent")
    leaves = expected_leaves(manifest["parent_id"], split_variables)
    if manifest.get("leaf_count") != len(leaves) or manifest.get("leaves") != leaves:
        raise ValueError("binary-tree leaf enumeration mismatch")
    return base, leaves


def write_manifest(parent_path: Path, parent_id: str,
                   split_variables: tuple[int, ...], output: Path) -> None:
    parent = json.loads(parent_path.read_text())
    if parent.get("schema") != "erdos85-h7-t0-cube1-cover-v1":
        raise ValueError("unsupported parent manifest schema")
    jobs = [job for job in parent.get("jobs", []) if job.get("id") == parent_id]
    if len(jobs) != 1 or jobs[0].get("kind") != "cube":
        raise ValueError("binary parent must be one unique positive cube job")
    if not split_variables or len(set(split_variables)) != len(split_variables):
        raise ValueError("split variables must be nonempty and distinct")
    base = Path(parent["base"])
    if sha256(base) != parent["base_sha256"]:
        raise ValueError("base CNF hash mismatch")
    variables, clauses = inspect_dimacs(base)
    if (variables, clauses) != (parent["variables"], parent["base_clauses"]):
        raise ValueError("base CNF shape mismatch")
    parent_units = jobs[0].get("units")
    if (not isinstance(parent_units, list) or
            any(not isinstance(unit, int) or unit == 0 for unit in parent_units)):
        raise ValueError("malformed parent units")
    if (any(not 1 <= variable <= variables for variable in split_variables) or
            set(map(abs, parent_units)) & set(split_variables)):
        raise ValueError("split variable outside header or fixed by parent")
    leaves = expected_leaves(parent_id, list(split_variables))
    manifest = {
        "schema": "erdos85-h7-binary-tree-jobs-v1",
        "identifier_convention": "one-based DIMACS",
        "parent_manifest": str(parent_path.resolve()),
        "parent_manifest_sha256": sha256(parent_path),
        "parent_id": parent_id,
        "parent_units": parent_units,
        "split_variables": list(split_variables),
        "base": str(base.resolve()), "base_sha256": parent["base_sha256"],
        "variables": variables, "base_clauses": clauses,
        "leaf_count": len(leaves), "leaves": leaves,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name(f".{output.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, output)


def materialize(manifest_path: Path, leaf_id: str, output: Path) -> None:
    manifest = json.loads(manifest_path.read_text())
    base, leaves = validate_bound_manifest(manifest)
    matches = [leaf for leaf in leaves
               if leaf.get("id") == leaf_id]
    if len(matches) != 1:
        raise ValueError(f"unknown or duplicate leaf id: {leaf_id}")
    units = [*manifest["parent_units"], *matches[0]["path_units"]]
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
                        raise ValueError("duplicate DIMACS header")
                    raw = (f"p cnf {manifest['variables']} "
                           f"{manifest['base_clauses'] + len(units)}\n").encode()
                    replaced = True
                target.write(raw)
            if not replaced:
                raise ValueError("missing DIMACS header")
            for unit in units:
                target.write(f"{unit} 0\n".encode())
        expected = (manifest["variables"], manifest["base_clauses"] + len(units))
        if inspect_dimacs(temporary) != expected:
            raise AssertionError("materialized DIMACS shape mismatch")
        os.replace(temporary, output)
    finally:
        temporary.unlink(missing_ok=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    create = commands.add_parser("manifest")
    create.add_argument("--parent-manifest", type=Path, required=True)
    create.add_argument("--parent-id", required=True)
    create.add_argument("--split-variables", type=int, nargs="+", required=True)
    create.add_argument("--output", type=Path, required=True)
    emit = commands.add_parser("materialize")
    emit.add_argument("--manifest", type=Path, required=True)
    emit.add_argument("--leaf", required=True)
    emit.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "manifest":
        write_manifest(args.parent_manifest.resolve(), args.parent_id,
                       tuple(args.split_variables), args.output.resolve())
    else:
        materialize(args.manifest.resolve(), args.leaf, args.output.resolve())
    print(f"WROTE {args.output.resolve()}")


if __name__ == "__main__":
    main()
