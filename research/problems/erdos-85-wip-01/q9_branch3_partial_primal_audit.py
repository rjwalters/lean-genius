#!/usr/bin/env python3
"""Audit the three-row local-to-global primal form of the branch-3 selector."""

from __future__ import annotations

import argparse
import hashlib
import json
from itertools import combinations
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

from q9_symmetric_point_mass_obstruction import (
    dual,
    exact_certificate,
    fixed_system,
    primal,
    random_outer,
)


def partial_primal(system: dict, degree_rows: set[int]):
    """Keep global symmetry/capacities, but only selected degree equations."""
    edges = system["edges"]
    blocks = system["blocks"]
    caps = system["caps"]
    matrix_eq = np.zeros((len(degree_rows), len(edges)))
    rhs_eq = np.zeros(len(degree_rows))
    for target, row in enumerate(sorted(degree_rows)):
        rhs_eq[target] = system["degree"][row]
        for column, edge in enumerate(edges):
            matrix_eq[target, column] = int(row in edge)
    matrix_cap = np.zeros((len(caps), len(edges)))
    for target, (row, point) in enumerate(caps):
        for column, edge in enumerate(edges):
            if row not in edge:
                continue
            other = edge[1] if edge[0] == row else edge[0]
            matrix_cap[target, column] = int(point in blocks[other])
    return linprog(
        np.zeros(len(edges)),
        A_ub=matrix_cap,
        b_ub=np.ones(len(caps)),
        A_eq=matrix_eq,
        b_eq=rhs_eq,
        bounds=(0, None),
        method="highs",
    )


def audit(system: dict) -> dict:
    if system["branch"] != 3:
        raise ValueError("partial primal audit requires branch 3")
    records = []
    mismatches = []
    for hole in (24, 25):
        for first, second in combinations(range(24), 2):
            support = {hole, first, second}
            primal_result = partial_primal(system, support)
            dual_result = dual(system, support)
            certificate = (
                exact_certificate(system, dual_result)
                if dual_result.success else None
            )
            primal_feasible = primal_result.success
            dual_strict = certificate is not None
            record = {
                "hole": hole,
                "regular_rows": [first, second],
                "partial_primal_feasible": primal_feasible,
                "strict_dual_certificate": dual_strict,
            }
            if dual_strict:
                record["margin"] = certificate["margin"]
                record["row_prices"] = certificate["row_prices"]
            records.append(record)
            if primal_feasible == dual_strict:
                mismatches.append(record)
    globally_feasible = primal(system).success
    infeasible = [record for record in records
                  if not record["partial_primal_feasible"]]
    return {
        "global_primal_feasible": globally_feasible,
        "support_count": len(records),
        "partial_primal_infeasible_count": len(infeasible),
        "strict_dual_count": sum(
            record["strict_dual_certificate"] for record in records
        ),
        "farkas_mismatch_count": len(mismatches),
        "farkas_mismatches": mismatches,
        "infeasible_supports": infeasible,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("payload", type=Path, nargs="?")
    parser.add_argument("--random-seed", type=int)
    parser.add_argument("--timeout-seconds", type=int, default=30)
    args = parser.parse_args()
    if args.payload is None:
        if args.random_seed is None:
            parser.error("provide a payload or --random-seed")
        payload = random_outer(3, args.random_seed, args.timeout_seconds)
    else:
        payload = json.loads(args.payload.read_text())
    canonical = json.dumps(
        payload, sort_keys=True, separators=(",", ":")
    ).encode()
    result = audit(fixed_system(payload))
    result["payload_sha256"] = hashlib.sha256(canonical).hexdigest()
    print(json.dumps(result, separators=(",", ":")))


if __name__ == "__main__":
    main()
