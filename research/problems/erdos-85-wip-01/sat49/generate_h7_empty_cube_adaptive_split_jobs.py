#!/usr/bin/env python3
"""Build an adaptive binary proof tree below one canonical H7 empty cube."""

from __future__ import annotations

import argparse
import json
import os
import tempfile
from pathlib import Path

import generate_h7_adaptive_binary_tree_jobs as trees
import generate_h7_empty_cube_manifest as parents
import probe_h7_binary_lookahead as dimacs


SPEC_SCHEMA = "erdos85-h7-canonical-empty-cube-adaptive-spec-v1"
MANIFEST_SCHEMA = "erdos85-h7-canonical-empty-cube-adaptive-jobs-v1"


def build_manifest(parent: dict, parent_sha256: str, spec: dict,
                   spec_sha256: str, base: Path) -> dict:
    if parent.get("schema") != parents.SCHEMA:
        raise ValueError("unsupported canonical empty-cube parent schema")
    if spec.get("schema") != SPEC_SCHEMA:
        raise ValueError("unsupported adaptive tree spec schema")
    if parents.sha256(base) != parent.get("base_sha256"):
        raise ValueError("adaptive base hash mismatch")
    variables, clauses = dimacs.read_dimacs(base)
    if (variables, len(clauses)) != (parents.VARIABLES, parents.BASE_CLAUSES):
        raise ValueError("unexpected canonical compact base shape")
    if (variables, len(clauses)) != (parent.get("variables"),
                                     parent.get("base_clauses")):
        raise ValueError("adaptive base shape mismatch")
    parent_id = spec.get("parent_id")
    matches = [job for job in parent.get("jobs", [])
               if job.get("id") == parent_id]
    if len(matches) != 1 or matches[0].get("status") != "missing":
        raise ValueError("adaptive root must be exactly one missing parent")
    parent_job = matches[0]
    parent_units = parent_job.get("units")
    if (not isinstance(parent_units, list) or len(parent_units) != 21 or
            any(type(unit) is not int or unit == 0 for unit in parent_units)):
        raise ValueError("malformed canonical parent units")
    nodes = trees.validate_nodes(spec.get("nodes"), variables, parent_units)
    leaves = trees.expected_leaves(parent_id, nodes, parent_units)
    return {
        "schema": MANIFEST_SCHEMA,
        "identifier_convention": "one-based signed DIMACS",
        "parent_schema": parents.SCHEMA,
        "parent_manifest_sha256": parent_sha256,
        "tree_spec_sha256": spec_sha256,
        "base_sha256": parent["base_sha256"],
        "variables": variables, "base_clauses": len(clauses),
        "parent_id": parent_id,
        "edge_count": parent_job["edge_count"],
        "type_index": parent_job["type_index"],
        "parent_units": parent_units, "nodes": nodes,
        "internal_node_count": len(nodes),
        "leaf_count": len(leaves), "leaves": leaves,
    }


def validate_bound_manifest(manifest: dict, parent: dict, parent_sha256: str,
                            spec: dict, spec_sha256: str,
                            base: Path) -> list[dict]:
    if manifest.get("schema") != MANIFEST_SCHEMA:
        raise ValueError("unsupported adaptive manifest schema")
    expected = build_manifest(parent, parent_sha256, spec, spec_sha256, base)
    if manifest != expected:
        raise ValueError("adaptive manifest differs from bound inputs")
    return expected["leaves"]


def materialize(manifest: dict, leaves: list[dict], base: Path,
                leaf_id: str, output: Path) -> None:
    matches = [leaf for leaf in leaves if leaf["id"] == leaf_id]
    if len(matches) != 1:
        raise ValueError(f"unknown adaptive leaf: {leaf_id}")
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


def read_inputs(parent_path: Path, spec_path: Path) -> tuple[dict, dict, str, str]:
    return (json.loads(parent_path.read_text()), json.loads(spec_path.read_text()),
            parents.sha256(parent_path), parents.sha256(spec_path))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    create = commands.add_parser("manifest")
    create.add_argument("--parent-manifest", type=Path, required=True)
    create.add_argument("--tree-spec", type=Path, required=True)
    create.add_argument("--base", type=Path, required=True)
    create.add_argument("--output", type=Path, required=True)
    emit = commands.add_parser("materialize")
    emit.add_argument("--manifest", type=Path, required=True)
    emit.add_argument("--parent-manifest", type=Path, required=True)
    emit.add_argument("--tree-spec", type=Path, required=True)
    emit.add_argument("--base", type=Path, required=True)
    emit.add_argument("--leaf", required=True)
    emit.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    parent, spec, parent_hash, spec_hash = read_inputs(
        args.parent_manifest, args.tree_spec)
    if args.command == "manifest":
        result = build_manifest(parent, parent_hash, spec, spec_hash, args.base)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    else:
        result = json.loads(args.manifest.read_text())
        leaves = validate_bound_manifest(
            result, parent, parent_hash, spec, spec_hash, args.base)
        materialize(result, leaves, args.base, args.leaf, args.output)
    print(f"WROTE {args.output}")


if __name__ == "__main__":
    main()
