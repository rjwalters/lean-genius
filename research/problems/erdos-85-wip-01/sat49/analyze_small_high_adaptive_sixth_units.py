#!/usr/bin/env python3
"""Audit unit propagation over an exact adaptive-sixth manifest.

This is a read-only structural probe, not a SAT solver.  It reports immediate
unit conflicts and literals forced by Boolean constraint propagation in each
of the 768 exact sixth cells.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict, deque
from pathlib import Path


def read_dimacs(path: Path) -> tuple[int, list[tuple[int, ...]]]:
    variables = None
    expected_clauses = None
    clauses: list[tuple[int, ...]] = []
    with path.open("rt", encoding="ascii") as source:
        for raw in source:
            line = raw.strip()
            if not line or line.startswith("c"):
                continue
            if line.startswith("p"):
                fields = line.split()
                if len(fields) != 4 or fields[:2] != ["p", "cnf"]:
                    raise ValueError(f"malformed DIMACS header: {path}")
                if variables is not None:
                    raise ValueError(f"duplicate DIMACS header: {path}")
                variables = int(fields[2])
                expected_clauses = int(fields[3])
                continue
            literals = tuple(int(field) for field in line.split())
            if not literals or literals[-1] != 0:
                raise ValueError(f"unterminated DIMACS clause: {path}")
            clause = literals[:-1]
            if not clause:
                raise ValueError(f"empty base clause: {path}")
            clauses.append(clause)
    if variables is None or expected_clauses is None:
        raise ValueError(f"missing DIMACS header: {path}")
    if len(clauses) != expected_clauses:
        raise ValueError(
            f"DIMACS clause mismatch: expected={expected_clauses} "
            f"actual={len(clauses)}"
        )
    return variables, clauses


def build_falsified_occurrences(
    clauses: list[tuple[int, ...]],
) -> dict[int, list[int]]:
    occurrences: dict[int, list[int]] = defaultdict(list)
    for clause_id, clause in enumerate(clauses):
        for literal in clause:
            occurrences[-literal].append(clause_id)
    return occurrences


def propagate(
    clauses: list[tuple[int, ...]],
    occurrences: dict[int, list[int]],
    base_units: tuple[int, ...],
    assumptions: list[int],
) -> tuple[bool, dict[int, bool]]:
    assignment: dict[int, bool] = {}
    queue: deque[int] = deque((*base_units, *assumptions))
    while queue:
        literal = queue.popleft()
        variable = abs(literal)
        value = literal > 0
        previous = assignment.get(variable)
        if previous is not None:
            if previous != value:
                return False, assignment
            continue
        assignment[variable] = value
        for clause_id in occurrences.get(literal, ()):
            clause = clauses[clause_id]
            unassigned = 0
            last_unassigned = 0
            satisfied = False
            for candidate in clause:
                candidate_value = assignment.get(abs(candidate))
                if candidate_value is None:
                    unassigned += 1
                    last_unassigned = candidate
                elif candidate_value == (candidate > 0):
                    satisfied = True
                    break
            if satisfied:
                continue
            if unassigned == 0:
                return False, assignment
            if unassigned == 1:
                queue.append(last_unassigned)
    return True, assignment


def manifest_jobs(manifest: dict) -> list[tuple[str, list[int]]]:
    result = []
    for leaf in manifest.get("leaves", {}).values():
        parent_units = leaf.get("parent_units")
        if not isinstance(parent_units, list):
            raise ValueError("manifest leaf has no parent_units list")
        for job in leaf.get("jobs", []):
            if job.get("kind") != "cube":
                raise ValueError(f"unexpected job kind: {job.get('id')}")
            result.append(
                (str(job["id"]), [*parent_units, *job.get("units", [])])
            )
    return result


def edge_endpoints(variable: int) -> list[int] | None:
    """Decode a one-based order-49 edge variable."""
    if not 1 <= variable <= 1176:
        return None
    for left in range(49):
        start = 1176 - (49 - left) * (48 - left) // 2
        width = 48 - left
        if start < variable <= start + width:
            return [left, left + (variable - start)]
    raise AssertionError(f"failed to decode edge variable {variable}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--top", type=int, default=30)
    parser.add_argument("--probe-literal", type=int, action="append", default=[])
    parser.add_argument("--track-literal", type=int, action="append", default=[])
    args = parser.parse_args()

    manifest = json.loads(args.manifest.read_text())
    if manifest.get("schema") != "erdos85-small-high-adaptive-sixth-jobs-v1":
        raise ValueError(f"unsupported manifest schema: {args.manifest}")
    jobs = manifest_jobs(manifest)
    if len(jobs) != manifest.get("positive_residual_jobs"):
        raise ValueError("manifest job-count metadata mismatch")
    bases = {
        Path(leaf["base"]) for leaf in manifest.get("leaves", {}).values()
    }
    if len(bases) != 1:
        raise ValueError(f"expected one shared base CNF, found {len(bases)}")
    base = next(iter(bases))
    variables, clauses = read_dimacs(base)
    occurrences = build_falsified_occurrences(clauses)
    base_units = tuple(clause[0] for clause in clauses if len(clause) == 1)
    common_assumptions = sorted(
        set.intersection(*(set(assumptions) for _, assumptions in jobs))
    )
    baseline_consistent, baseline_assignment = propagate(
        clauses, occurrences, base_units, common_assumptions
    )
    if not baseline_consistent:
        raise ValueError("base CNF has a unit-propagation conflict")

    conflicts = []
    derived_counts: Counter[int] = Counter()
    derived_sizes: Counter[int] = Counter()
    tracked_derived_jobs: dict[int, list[str]] = {
        literal: []
        for variable in (*args.probe_literal, *args.track_literal)
        for literal in (abs(variable), -abs(variable))
    }
    for job_id, assumptions in jobs:
        consistent, assignment = propagate(
            clauses, occurrences, base_units, assumptions
        )
        if not consistent:
            conflicts.append(job_id)
            continue
        assumed_variables = {abs(literal) for literal in assumptions}
        baseline_variables = set(baseline_assignment)
        derived = [
            variable if value else -variable
            for variable, value in assignment.items()
            if variable not in assumed_variables and variable not in baseline_variables
        ]
        derived_sizes[len(derived)] += 1
        derived_counts.update(derived)
        derived_set = set(derived)
        for literal, tracked_jobs in tracked_derived_jobs.items():
            if literal in derived_set:
                tracked_jobs.append(job_id)

    probes = {}
    for variable in args.probe_literal:
        variable = abs(variable)
        if not 1 <= variable <= variables:
            raise ValueError(f"probe variable outside DIMACS header: {variable}")
        outcomes = {}
        for literal in (variable, -variable):
            conflict_count = 0
            for _, assumptions in jobs:
                consistent, _ = propagate(
                    clauses, occurrences, base_units,
                    [*assumptions, literal],
                )
                conflict_count += not consistent
            outcomes[str(literal)] = {"unit_conflicts": conflict_count}
        probes[str(variable)] = outcomes

    report = {
        "base": str(base),
        "variables": variables,
        "clauses": len(clauses),
        "jobs": len(jobs),
        "common_assumptions": common_assumptions,
        "baseline_forced_variables": len(baseline_assignment),
        "unit_conflicts": len(conflicts),
        "conflict_job_ids": conflicts[: args.top],
        "derived_size_histogram": dict(sorted(derived_sizes.items())),
        "shared_derived_literal_count": sum(
            count == len(jobs) for count in derived_counts.values()
        ),
        "most_common_derived_literals": [
            {"literal": literal, "jobs": count}
            for literal, count in derived_counts.most_common(args.top)
        ],
        "most_common_nonshared_edge_literals": [
            {
                "literal": literal,
                "edge": edge_endpoints(abs(literal)),
                "jobs": count,
            }
            for literal, count in sorted(
                (
                    (literal, count)
                    for literal, count in derived_counts.items()
                    if abs(literal) <= 1176 and count < len(jobs)
                ),
                key=lambda item: (-item[1], abs(item[0]), item[0]),
            )[: args.top]
        ],
        "shared_derived_edge_literals": [
            {
                "literal": literal,
                "edge": edge_endpoints(abs(literal)),
            }
            for literal, count in sorted(derived_counts.items())
            if abs(literal) <= 1176 and count == len(jobs)
        ],
        "mixed_polarity_derived_variables": [
            {
                "variable": variable,
                "edge": edge_endpoints(variable),
                "positive_jobs": derived_counts[variable],
                "negative_jobs": derived_counts[-variable],
                "covered_jobs": (
                    derived_counts[variable] + derived_counts[-variable]
                ),
            }
            for variable in sorted(
                (
                    variable
                    for variable in range(1, variables + 1)
                    if derived_counts[variable] and derived_counts[-variable]
                ),
                key=lambda variable: (
                    -(derived_counts[variable] + derived_counts[-variable]),
                    -min(derived_counts[variable], derived_counts[-variable]),
                    variable,
                ),
            )[: args.top]
        ],
        "probes": probes,
        "tracked_derived_job_ids": {
            str(literal): job_ids
            for literal, job_ids in tracked_derived_jobs.items()
        },
    }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
