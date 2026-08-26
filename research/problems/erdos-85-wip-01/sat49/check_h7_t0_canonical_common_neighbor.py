#!/usr/bin/env python3
"""Emit signal-only H7 CNF using common-neighbor C4 constraints.

This encoding is propositionally equivalent to the canonical direct C4
clauses, but it is not part of the formal LRAT replay boundary yet.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

import check_h7_t0_canonical_completion as canonical
import check_h7_t0_canonical_compact as compact
import generate_h7_empty_cube_manifest as inventory


SCHEMA = "erdos85-h7-common-neighbor-signal-v1"


def and_literal(cnf: compact.CompactCnf, left: bool | int,
                right: bool | int) -> bool | int:
    """Return a literal equivalent to ``left and right``."""
    if left is False or right is False:
        return False
    if left is True:
        return right
    if right is True:
        return left
    result = cnf.variable()
    cnf.add(-result, left)
    cnf.add(-result, right)
    cnf.add(result, -left, -right)
    return result


def add_common_neighbor_at_most_one(
        cnf: compact.CompactCnf,
        candidates: list[tuple[bool | int, bool | int]]) -> None:
    """Forbid two candidates whose two incident edges are both present."""
    literals: list[int] = []
    truths = 0
    for left, right in candidates:
        conjunction = and_literal(cnf, left, right)
        if conjunction is True:
            truths += 1
        elif conjunction is not False:
            literals.append(conjunction)
    if truths > 1:
        cnf.add()
    elif truths == 1:
        for literal in literals:
            cnf.add(-literal)
    elif len(literals) > 1:
        cnf.at_most(literals, 1)


def build_cnf() -> tuple[compact.CompactCnf,
                         dict[tuple[int, int], int], int]:
    cnf = compact.CompactCnf()
    edge_variables = {
        edge: cnf.variable() for edge in itertools.combinations(canonical.LOW, 2)
    }
    for vertex in canonical.LOW:
        incident = [variable for edge, variable in edge_variables.items()
                    if vertex in edge]
        support_card = (0 if vertex in canonical.EMPTY else
                        1 if vertex in canonical.SINGLETON else 2)
        cnf.exactly(incident, 7 - support_card)

    def status(left: int, right: int) -> bool | int:
        if left == right:
            return False
        edge = canonical.normalized_edge(left, right)
        if edge in canonical.FIXED_TRUE:
            return True
        return edge_variables.get(edge, False)

    degree_clauses = len(cnf.clauses)
    for left, right in itertools.combinations(canonical.VERTICES, 2):
        add_common_neighbor_at_most_one(cnf, [
            (status(left, middle), status(right, middle))
            for middle in canonical.VERTICES if middle not in (left, right)
        ])
    return cnf, edge_variables, len(cnf.clauses) - degree_clauses


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--parent-manifest", type=Path, required=True)
    parser.add_argument("--parent", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    parent = json.loads(args.parent_manifest.read_text())
    if parent.get("schema") != inventory.SCHEMA:
        raise ValueError("unsupported canonical parent manifest")
    matches = [job for job in parent.get("jobs", []) if job.get("id") == args.parent]
    if len(matches) != 1 or matches[0].get("status") != "missing":
        raise ValueError("common-neighbor probe requires exactly one missing parent")
    job = matches[0]
    cnf, edge_variables, c4_clauses = build_cnf()
    if (len(edge_variables) != 861 or
            any(edge_variables[edge] != index for index, edge in
                enumerate(itertools.combinations(canonical.LOW, 2), start=1))):
        raise AssertionError("semantic edge variables differ from canonical IDs")
    for unit in job["units"]:
        cnf.add(unit)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    cnf.write(args.output)
    summary = {
        "schema": SCHEMA,
        "parent_id": job["id"],
        "signal_only": True,
        "variables": cnf.variable_count,
        "clauses": len(cnf.clauses),
        "c4_clauses": c4_clauses,
        "sha256": hashlib.sha256(args.output.read_bytes()).hexdigest(),
    }
    print(json.dumps(summary, sort_keys=True))


if __name__ == "__main__":
    main()
