#!/usr/bin/env python3
"""Exact corpus check for the q=9 fiber-plus-one-auxiliary template.

For every U1 point ``p``, its canonical fiber consists of the four B0 rows
through ``p`` other than the fixed diagonal row ``p % 8``.  This verifier
asks whether the symmetric point-mass Farkas dual has a certificate whose row
prices are supported on that fiber together with at most one arbitrary row.
Point prices are restricted too: they may be outgoing from one of those at
most five rows, or incoming at the common point ``p``.  Row prices are
nonnegative.  Thus this is the direct one-auxiliary extension of the reduced
four-row fiber-price template, rather than merely a row-support coincidence.

This is deliberately only a corpus classifier.  It does not infer the
fiber-plus-auxiliary property for every admissible outer design.  Floating LP
answers count only after the shared Fraction-exact certificate audit passes.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

from q9_symmetric_point_mass_obstruction import (
    N,
    N_U1,
    exact_certificate,
    fixed_system,
)


DEFAULT_PAYLOADS = (
    "q9_13f_counterexample.json",
    "q9_13t_counterexample.json",
    "q9_gram_fractional_gap_witness.json",
    "q9_branch4_row40_interval_witness.json",
)


def restricted_dual(system: dict, point: int, allowed: set[int]):
    """Reduced dual: outgoing prices at allowed rows, or incoming at p."""
    variable_count = 2 * N + len(system["caps"])
    matrix = []
    upper = []
    for u, v in system["edges"]:
        row = np.zeros(variable_count)
        row[u] = row[v] = 1
        row[N + u] = row[N + v] = -1
        for q in system["blocks"][v]:
            row[2 * N + system["cap_index"][u, q]] -= 1
        for q in system["blocks"][u]:
            row[2 * N + system["cap_index"][v, q]] -= 1
        matrix.append(row)
        upper.append(0)
    margin = np.zeros(variable_count)
    for row in range(N):
        margin[row] = -system["degree"][row]
        margin[N + row] = system["degree"][row]
    margin[2 * N:] = 1
    matrix.append(margin)
    upper.append(-1)

    bounds = []
    for index in range(variable_count):
        if index < N:
            permitted = index in allowed
        elif index < 2 * N:
            # The reduced template uses nonnegative row prices.
            permitted = False
        else:
            row, q = system["caps"][index - 2 * N]
            permitted = row in allowed or q == point
        bounds.append((0, None) if permitted else (0, 0))
    return linprog(
        np.ones(variable_count), A_ub=np.array(matrix),
        b_ub=np.array(upper), bounds=bounds, method="highs",
    )


def exact_witnesses(system: dict) -> list[dict]:
    witnesses = []
    for point in range(N_U1):
        fiber = {
            row for row, block in enumerate(system["blocks"])
            if point in block and row != point % 8
        }
        if len(fiber) != 4:
            raise RuntimeError(
                f"point {point} has non-diagonal fiber {sorted(fiber)}"
            )
        # ``None`` tests the pure fiber first.  Auxiliary rows already in the
        # fiber add nothing and are omitted from the subsequent search.
        for auxiliary in [None] + [row for row in range(N) if row not in fiber]:
            allowed = fiber if auxiliary is None else fiber | {auxiliary}
            result = restricted_dual(system, point, allowed)
            if not result.success:
                continue
            certificate = exact_certificate(system, result)
            if certificate is None:
                raise RuntimeError(
                    f"floating solution failed exact audit at p={point}, "
                    f"auxiliary={auxiliary}"
                )
            actual = {row for row, _ in certificate["row_prices"]}
            if not actual <= allowed:
                raise RuntimeError("audited certificate leaked row support")
            for (row, q), _ in certificate["point_prices"]:
                if row not in allowed and q != point:
                    raise RuntimeError("audited certificate leaked point support")
            witnesses.append({
                "point": point,
                "fiber": sorted(fiber),
                "auxiliary": auxiliary,
                "actual_row_support": sorted(actual),
                "actual_row_support_size": len(actual),
                "margin": certificate["margin"],
            })
    return witnesses


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("payloads", type=Path, nargs="*")
    parser.add_argument("--show-all", action="store_true")
    args = parser.parse_args()
    base = Path(__file__).resolve().parent
    payloads = args.payloads or [base / name for name in DEFAULT_PAYLOADS]

    corpus = []
    for path in payloads:
        system = fixed_system(json.loads(path.read_text()))
        witnesses = exact_witnesses(system)
        if not witnesses:
            raise SystemExit(f"{path.name}: no exact fiber-plus-auxiliary witness")
        witnesses.sort(key=lambda item: (
            item["auxiliary"] is not None,
            item["actual_row_support_size"],
            item["point"],
            -1 if item["auxiliary"] is None else item["auxiliary"],
        ))
        item = {
            "payload": path.name,
            "branch": system["branch"],
            "best": witnesses[0],
            "pure_fiber_witness": any(
                witness["auxiliary"] is None for witness in witnesses
            ),
            "witness_count": len(witnesses),
        }
        if args.show_all:
            item["witnesses"] = witnesses
        corpus.append(item)

    print(json.dumps(corpus, indent=2, sort_keys=True))
    print("fiber_plus_one_auxiliary_corpus=EXACT")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
