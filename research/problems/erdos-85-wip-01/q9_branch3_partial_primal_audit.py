#!/usr/bin/env python3
"""Audit the three-row local-to-global primal form of the branch-3 selector."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from fractions import Fraction
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


def covering_partial_primal(system: dict, degree_rows: set[int]):
    """Replace selected exact degrees by lower bounds on those degrees."""
    edges = system["edges"]
    blocks = system["blocks"]
    caps = system["caps"]
    matrix_degree = np.zeros((len(degree_rows), len(edges)))
    rhs_degree = np.zeros(len(degree_rows))
    for target, row in enumerate(sorted(degree_rows)):
        rhs_degree[target] = system["degree"][row]
        for column, edge in enumerate(edges):
            matrix_degree[target, column] = int(row in edge)
    matrix_cap = np.zeros((len(caps), len(edges)))
    for target, (row, point) in enumerate(caps):
        for column, edge in enumerate(edges):
            if row not in edge:
                continue
            other = edge[1] if edge[0] == row else edge[0]
            matrix_cap[target, column] = int(point in blocks[other])
    return linprog(
        np.zeros(len(edges)),
        A_ub=np.vstack((matrix_cap, -matrix_degree)),
        b_ub=np.concatenate((np.ones(len(caps)), -rhs_degree)),
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
            covering_feasible = (
                True if primal_result.success
                else covering_partial_primal(system, support).success
            )
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
                "covering_partial_primal_feasible": covering_feasible,
                "strict_dual_certificate": dual_strict,
            }
            if dual_strict:
                record["margin"] = certificate["margin"]
                record["row_prices"] = certificate["row_prices"]
            records.append(record)
            if primal_feasible == dual_strict:
                mismatches.append(record)
    globally_feasible = primal(system).success
    row_stratum_feasibility = {
        "regular_triples_0_23": partial_primal(
            system, set(range(24))
        ).success,
        "all_triples_0_25": partial_primal(
            system, set(range(26))
        ).success,
        "pair_rows_26_46": partial_primal(
            system, set(range(26, 47))
        ).success,
        "exceptional_and_pair_rows_24_46": partial_primal(
            system, set(range(24, 47))
        ).success,
    }
    infeasible = [record for record in records
                  if not record["partial_primal_feasible"]]
    covering_mismatches = [
        record for record in records
        if record["partial_primal_feasible"]
        != record["covering_partial_primal_feasible"]
    ]
    row_prices = [
        Fraction(value)
        for record in infeasible
        for _, value in record["row_prices"]
    ]
    return {
        "global_primal_feasible": globally_feasible,
        "row_stratum_feasibility": row_stratum_feasibility,
        "support_count": len(records),
        "partial_primal_infeasible_count": len(infeasible),
        "exceptional_three_row_selector_counterexample":
            not globally_feasible and not infeasible,
        "covering_partial_primal_infeasible_count": sum(
            not record["covering_partial_primal_feasible"]
            for record in records
        ),
        "exact_covering_mismatch_count": len(covering_mismatches),
        "exact_covering_mismatches": covering_mismatches,
        "strict_dual_count": sum(
            record["strict_dual_certificate"] for record in records
        ),
        "farkas_mismatch_count": len(mismatches),
        "farkas_mismatches": mismatches,
        "negative_row_price_count": sum(value < 0 for value in row_prices),
        "all_strict_duals_have_nonnegative_row_prices":
            all(value >= 0 for value in row_prices),
        "nonzero_row_support_histogram": dict(sorted(Counter(
            len(record["row_prices"]) for record in infeasible
        ).items())),
        "infeasible_supports": infeasible,
    }


def first_infeasible_partial(system: dict) -> dict | None:
    """Return one failing three-row projection, without solving any duals."""
    for hole in (24, 25):
        for first, second in combinations(range(24), 2):
            support = {hole, first, second}
            if not partial_primal(system, support).success:
                return {"hole": hole, "regular_rows": [first, second]}
    return None


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("payload", type=Path, nargs="?")
    parser.add_argument("--random-seed", type=int)
    parser.add_argument("--scan-start", type=int)
    parser.add_argument("--scan-count", type=int, default=1)
    parser.add_argument("--timeout-seconds", type=int, default=30)
    args = parser.parse_args()
    if args.scan_start is not None:
        for seed in range(args.scan_start, args.scan_start + args.scan_count):
            payload = random_outer(3, seed, args.timeout_seconds)
            system = fixed_system(payload)
            globally_feasible = primal(system).success
            witness = first_infeasible_partial(system)
            canonical = json.dumps(
                payload, sort_keys=True, separators=(",", ":")
            ).encode()
            print(json.dumps({
                "seed": seed,
                "payload_sha256": hashlib.sha256(canonical).hexdigest(),
                "global_primal_feasible": globally_feasible,
                "first_infeasible_partial": witness,
                "selector_counterexample":
                    not globally_feasible and witness is None,
            }, separators=(",", ":")), flush=True)
            if not globally_feasible and witness is None:
                break
        return
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
