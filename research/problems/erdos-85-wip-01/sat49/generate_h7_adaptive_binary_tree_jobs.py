#!/usr/bin/env python3
"""Build adaptive prefix-tree jobs below one hard H7 parent cube."""

from __future__ import annotations

import argparse
import json
import os
import re
import tempfile
from pathlib import Path

from generate_h7_t0_cube_one_cover_jobs import inspect_dimacs, sha256


SPEC_SCHEMA = "erdos85-h7-adaptive-binary-tree-spec-v1"
MANIFEST_SCHEMA = "erdos85-h7-adaptive-binary-tree-jobs-v1"


def validate_nodes(raw: object, variables: int,
                   parent_units: list[int]) -> dict[str, int]:
    if not isinstance(raw, dict) or not raw:
        raise ValueError("adaptive tree nodes must be a nonempty object")
    if len(raw) > 4095:
        raise ValueError("adaptive tree exceeds the 4095-node safety bound")
    nodes: dict[str, int] = {}
    fixed = {abs(unit) for unit in parent_units}
    for path, variable in raw.items():
        if (not isinstance(path, str) or re.fullmatch(r"[01]*", path) is None or
                not isinstance(variable, int) or isinstance(variable, bool) or
                not 1 <= variable <= variables):
            raise ValueError(f"invalid adaptive node {path!r}={variable!r}")
        nodes[path] = variable
    if "" not in nodes:
        raise ValueError("adaptive tree must contain the root path")
    for path, variable in nodes.items():
        if path and path[:-1] not in nodes:
            raise ValueError(f"adaptive node has no internal parent: {path}")
        ancestor_variables = {nodes[path[:depth]] for depth in range(len(path))}
        if variable in fixed or variable in ancestor_variables:
            raise ValueError(f"split variable is already fixed on path {path!r}")
    return nodes


def leaf_paths(nodes: dict[str, int]) -> list[str]:
    leaves = {path + bit for path in nodes for bit in "01"
              if path + bit not in nodes}
    result = sorted(leaves, key=lambda path: (len(path), path))
    if len(result) != len(nodes) + 1:
        raise AssertionError("finite full binary tree must have n+1 leaves")
    return result


def units_for_path(path: str, nodes: dict[str, int]) -> list[int]:
    return [nodes[path[:depth]] if bit == "1" else -nodes[path[:depth]]
            for depth, bit in enumerate(path)]


def expected_leaves(parent_id: str, nodes: dict[str, int],
                    parent_units: list[int]) -> list[dict]:
    result = []
    for path in leaf_paths(nodes):
        path_units = units_for_path(path, nodes)
        result.append({
            "id": f"{parent_id}.adaptive.leaf-{path}",
            "path": path,
            "path_units": path_units,
            "units": [*parent_units, *path_units],
        })
    return result


def validate_bound_manifest(manifest: dict) -> tuple[Path, dict[str, int], list[dict]]:
    if manifest.get("schema") != MANIFEST_SCHEMA:
        raise ValueError("unsupported adaptive-tree manifest schema")
    parent_path, spec_path = (Path(manifest.get(key, ""))
                              for key in ("parent_manifest", "tree_spec"))
    base = Path(manifest.get("base", ""))
    if (not parent_path.is_file() or not spec_path.is_file() or not base.is_file() or
            sha256(parent_path) != manifest.get("parent_manifest_sha256") or
            sha256(spec_path) != manifest.get("tree_spec_sha256") or
            sha256(base) != manifest.get("base_sha256")):
        raise ValueError("bound adaptive parent/spec/base hash mismatch")
    parent, spec = json.loads(parent_path.read_text()), json.loads(spec_path.read_text())
    if (parent.get("schema") != "erdos85-h7-t0-cube1-cover-v1" or
            spec.get("schema") != SPEC_SCHEMA):
        raise ValueError("unsupported bound parent or adaptive spec schema")
    parent_id = spec.get("parent_id")
    matches = [job for job in parent.get("jobs", []) if job.get("id") == parent_id]
    if len(matches) != 1 or matches[0].get("kind") != "cube":
        raise ValueError("adaptive root must bind one positive parent cube")
    parent_units = matches[0].get("units")
    if not isinstance(parent_units, list) or any(
            not isinstance(unit, int) or unit == 0 for unit in parent_units):
        raise ValueError("malformed adaptive parent units")
    variables, clauses = inspect_dimacs(base)
    if (parent.get("base") != manifest.get("base") or
            parent.get("base_sha256") != manifest.get("base_sha256") or
            (variables, clauses) != (30646, 1330469) or
            (variables, clauses) != (parent.get("variables"), parent.get("base_clauses")) or
            (variables, clauses) != (manifest.get("variables"), manifest.get("base_clauses"))):
        raise ValueError("adaptive base metadata mismatch")
    nodes = validate_nodes(spec.get("nodes"), variables, parent_units)
    leaves = expected_leaves(parent_id, nodes, parent_units)
    if (manifest.get("parent_id") != parent_id or
            manifest.get("parent_units") != parent_units or
            manifest.get("nodes") != nodes or
            manifest.get("internal_node_count") != len(nodes) or
            manifest.get("leaf_count") != len(leaves) or
            manifest.get("leaves") != leaves):
        raise ValueError("adaptive manifest inventory differs from bound spec")
    return base, nodes, leaves


def write_manifest(parent_path: Path, spec_path: Path, output: Path) -> None:
    parent, spec = json.loads(parent_path.read_text()), json.loads(spec_path.read_text())
    if parent.get("schema") != "erdos85-h7-t0-cube1-cover-v1":
        raise ValueError("unsupported H7 parent manifest schema")
    if spec.get("schema") != SPEC_SCHEMA:
        raise ValueError("unsupported adaptive-tree spec schema")
    parent_id = spec.get("parent_id")
    matches = [job for job in parent.get("jobs", []) if job.get("id") == parent_id]
    if len(matches) != 1 or matches[0].get("kind") != "cube":
        raise ValueError("adaptive root must be one positive parent cube")
    parent_units = matches[0].get("units")
    base = Path(parent.get("base", ""))
    if not base.is_file() or sha256(base) != parent.get("base_sha256"):
        raise ValueError("H7 base CNF is missing or changed")
    variables, clauses = inspect_dimacs(base)
    if (variables, clauses) != (parent.get("variables"), parent.get("base_clauses")):
        raise ValueError("H7 base shape differs from parent manifest")
    nodes = validate_nodes(spec.get("nodes"), variables, parent_units)
    leaves = expected_leaves(parent_id, nodes, parent_units)
    manifest = {
        "schema": MANIFEST_SCHEMA, "identifier_convention": "one-based DIMACS",
        "parent_manifest": str(parent_path.resolve()),
        "parent_manifest_sha256": sha256(parent_path),
        "tree_spec": str(spec_path.resolve()), "tree_spec_sha256": sha256(spec_path),
        "parent_id": parent_id, "parent_units": parent_units, "nodes": nodes,
        "internal_node_count": len(nodes), "leaf_count": len(leaves),
        "base": str(base.resolve()), "base_sha256": parent["base_sha256"],
        "variables": variables, "base_clauses": clauses, "leaves": leaves,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name(f".{output.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, output)


def materialize(manifest_path: Path, leaf_id: str, output: Path) -> None:
    manifest = json.loads(manifest_path.read_text())
    base, _, leaves = validate_bound_manifest(manifest)
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
        if inspect_dimacs(temporary) != (
                manifest["variables"], manifest["base_clauses"] + len(units)):
            raise AssertionError("adaptive leaf DIMACS shape mismatch")
        os.replace(temporary, output)
    finally:
        temporary.unlink(missing_ok=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    create = commands.add_parser("manifest")
    create.add_argument("--parent-manifest", type=Path, required=True)
    create.add_argument("--tree-spec", type=Path, required=True)
    create.add_argument("--output", type=Path, required=True)
    emit = commands.add_parser("materialize")
    emit.add_argument("--manifest", type=Path, required=True)
    emit.add_argument("--leaf", required=True)
    emit.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "manifest":
        write_manifest(args.parent_manifest.resolve(), args.tree_spec.resolve(),
                       args.output.resolve())
    else:
        materialize(args.manifest.resolve(), args.leaf, args.output.resolve())
    print(f"WROTE {args.output.resolve()}")


if __name__ == "__main__":
    main()
