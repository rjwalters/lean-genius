#!/usr/bin/env python3
"""Add signal-only lex leaders for an empty mask's exact S7 stabilizer.

The output is for performance probing only until the orbit/dominance bridge
described in H7_SMS_PIVOT_AUDIT.md is formalized.
"""

from __future__ import annotations

import argparse
import itertools
import json
import os
import tempfile
from pathlib import Path

import check_h7_t0_by_empty_graph as cubes
import generate_h7_empty_cube_manifest as inventory


LOW_VERTICES = 42
LOW_EDGES = list(itertools.combinations(range(LOW_VERTICES), 2))
LOW_EDGE_INDEX = {edge: index + 1 for index, edge in enumerate(LOW_EDGES)}
LABEL_EDGES = list(cubes.quotient.EDGES)
LABEL_EDGE_INDEX = {tuple(sorted(edge)): index
                    for index, edge in enumerate(LABEL_EDGES)}


def act_mask(mask: int, permutation: tuple[int, ...]) -> int:
    result = 0
    for index, (left, right) in enumerate(LABEL_EDGES):
        if mask >> index & 1:
            image = tuple(sorted((permutation[left], permutation[right])))
            result |= 1 << LABEL_EDGE_INDEX[image]
    return result


def stabilizer(mask: int) -> list[tuple[int, ...]]:
    return [p for p in itertools.permutations(range(7))
            if act_mask(mask, p) == mask]


def low_vertex_image(vertex: int, permutation: tuple[int, ...]) -> int:
    if vertex < 7:
        return permutation[vertex]
    if vertex < 21:
        label, copy = divmod(vertex - 7, 2)
        return 7 + 2 * permutation[label] + copy
    left, right = LABEL_EDGES[vertex - 21]
    pair = tuple(sorted((permutation[left], permutation[right])))
    return 21 + LABEL_EDGE_INDEX[pair]


def edge_variable_permutation(permutation: tuple[int, ...]) -> list[int]:
    result = []
    for left, right in LOW_EDGES:
        image = tuple(sorted((low_vertex_image(left, permutation),
                              low_vertex_image(right, permutation))))
        result.append(LOW_EDGE_INDEX[image])
    if sorted(result) != list(range(1, 862)):
        raise AssertionError("induced low-edge action is not a permutation")
    return result


def lex_leader_clauses(images: list[int], first_aux: int
                       ) -> tuple[list[tuple[int, ...]], int]:
    """Encode x <=lex image(x); return clauses and next unused variable."""
    clauses = []
    prefix = first_aux
    clauses.append((prefix,))
    next_var = prefix + 1
    for source, image in enumerate(images, 1):
        # A first difference source=true,image=false is forbidden.
        clauses.append((-prefix, -source, image))
        following = next_var
        next_var += 1
        # following <-> prefix and (source == image)
        clauses.extend([
            (-following, prefix),
            (-following, -source, image),
            (-following, source, -image),
            (-prefix, -source, -image, following),
            (-prefix, source, image, following),
        ])
        prefix = following
    return clauses, next_var


def augment(base: Path, parent_job: dict, output: Path) -> dict:
    mask = parent_job["mask"]
    group = stabilizer(mask)
    nonidentity = [p for p in group if p != tuple(range(7))]
    original_lines = base.read_text().splitlines()
    headers = [i for i, line in enumerate(original_lines)
               if line.lstrip().startswith("p cnf")]
    if len(headers) != 1:
        raise ValueError("expected one DIMACS header")
    fields = original_lines[headers[0]].split()
    variables, clauses = int(fields[2]), int(fields[3])
    if (variables, clauses) != (inventory.VARIABLES, inventory.BASE_CLAUSES):
        raise ValueError("unexpected compact base shape")
    extra = [(literal,) for literal in parent_job["units"]]
    next_var = variables + 1
    for permutation in nonidentity:
        encoded, next_var = lex_leader_clauses(
            edge_variable_permutation(permutation), next_var)
        extra.extend(encoded)
    original_lines[headers[0]] = (
        f"p cnf {next_var - 1} {clauses + len(extra)}")
    output.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{output.name}.", suffix=".tmp", dir=output.parent)
    try:
        with os.fdopen(descriptor, "w") as stream:
            stream.write("\n".join(original_lines) + "\n")
            for clause in extra:
                stream.write(" ".join(map(str, clause)) + " 0\n")
        os.replace(temporary_name, output)
    finally:
        Path(temporary_name).unlink(missing_ok=True)
    return {"parent_id": parent_job["id"], "stabilizer_size": len(group),
            "nonidentity_lex_leaders": len(nonidentity),
            "variables": next_var - 1, "clauses": clauses + len(extra),
            "signal_only": True}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--parent-manifest", type=Path, required=True)
    parser.add_argument("--base", type=Path, required=True)
    parser.add_argument("--parent", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    manifest = json.loads(args.parent_manifest.read_text())
    if (manifest.get("schema") != inventory.SCHEMA or
            inventory.sha256(args.base) != manifest.get("base_sha256")):
        raise ValueError("parent manifest/base binding mismatch")
    matches = [job for job in manifest["jobs"] if job["id"] == args.parent]
    if len(matches) != 1 or matches[0].get("status") != "missing":
        raise ValueError("lex probe requires exactly one missing parent")
    summary = augment(args.base, matches[0], args.output)
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
