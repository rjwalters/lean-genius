#!/usr/bin/env python3
"""Rank reproducible H7 binary splits by two-sided unit propagation."""

from __future__ import annotations

import argparse
import json
from collections import defaultdict, deque
from pathlib import Path


def read_dimacs(path: Path) -> tuple[int, list[tuple[int, ...]]]:
    variables = 0
    expected_clauses = None
    clauses: list[tuple[int, ...]] = []
    for line_number, line in enumerate(path.read_text().splitlines(), 1):
        stripped = line.strip()
        if not stripped or stripped.startswith(("c", "%")):
            continue
        if stripped.startswith("p cnf "):
            fields = stripped.split()
            if len(fields) != 4 or variables:
                raise ValueError(f"{path}:{line_number}: malformed/duplicate header")
            variables, expected_clauses = int(fields[2]), int(fields[3])
            continue
        fields = tuple(map(int, stripped.split()))
        if not fields or fields[-1] != 0:
            raise ValueError(f"{path}:{line_number}: malformed clause")
        clause = fields[:-1]
        if any(literal == 0 or abs(literal) > variables for literal in clause):
            raise ValueError(f"{path}:{line_number}: literal outside header")
        clauses.append(clause)
    if not variables or len(clauses) != expected_clauses:
        raise ValueError("DIMACS header/actual clause count mismatch")
    return variables, clauses


def propagate(clauses: list[tuple[int, ...]], occurrence: dict[int, list[int]],
              initial: tuple[int, ...]) -> tuple[bool, dict[int, bool]]:
    assignment: dict[int, bool] = {}
    queue = deque(initial)
    while queue:
        literal = queue.popleft()
        variable, value = abs(literal), literal > 0
        prior = assignment.get(variable)
        if prior is not None:
            if prior != value:
                return False, assignment
            continue
        assignment[variable] = value
        for clause_index in occurrence.get(-literal, ()):
            clause = clauses[clause_index]
            open_literal = None
            open_count = 0
            satisfied = False
            for entry in clause:
                entry_value = assignment.get(abs(entry))
                if entry_value is None:
                    open_literal = entry
                    open_count += 1
                elif entry_value == (entry > 0):
                    satisfied = True
                    break
            if satisfied:
                continue
            if open_count == 0:
                return False, assignment
            if open_count == 1:
                queue.append(open_literal)
    return True, assignment


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("base", type=Path)
    parser.add_argument("--parent-units", type=int, nargs="+", required=True)
    parser.add_argument("--limit", type=int, default=32)
    args = parser.parse_args()
    if args.limit <= 0:
        parser.error("--limit must be positive")

    variables, clauses = read_dimacs(args.base)
    occurrence: dict[int, list[int]] = defaultdict(list)
    candidate_variables = set()
    initial = list(args.parent_units)
    for clause_index, clause in enumerate(clauses):
        for literal in clause:
            occurrence[literal].append(clause_index)
        if len(clause) == 1:
            initial.append(clause[0])
        if len(clause) == 8 and all(literal > 0 for literal in clause):
            candidate_variables.update(clause)
    consistent, baseline = propagate(clauses, occurrence, tuple(initial))
    if not consistent:
        raise ValueError("base plus parent units is already unit-inconsistent")

    results = []
    for variable in sorted(candidate_variables - baseline.keys()):
        branches = []
        for literal in (-variable, variable):
            consistent, assignment = propagate(
                clauses, occurrence,
                (*[v if value else -v for v, value in baseline.items()], literal))
            branches.append({"consistent": consistent,
                             "forced": len(assignment) - len(baseline)})
        gains = [branch["forced"] for branch in branches]
        results.append({"variable": variable, "false": branches[0],
                        "true": branches[1], "min_gain": min(gains),
                        "product_gain": gains[0] * gains[1],
                        "sum_gain": sum(gains)})
    results.sort(key=lambda row: (-row["min_gain"], -row["product_gain"],
                                  -row["sum_gain"], row["variable"]))
    print(json.dumps({"variables": variables, "clauses": len(clauses),
                      "baseline_assigned": len(baseline),
                      "candidate_variables": len(results),
                      "ranking": results[:args.limit]}, indent=2))


if __name__ == "__main__":
    main()
