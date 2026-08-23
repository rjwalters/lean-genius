#!/usr/bin/env python3
"""Exact restricted U1-fiber price certificates for q=9 B.3.

For a U1 point ``p``, let ``S_p`` be its four incident non-diagonal B0 rows.
This searches the global symmetric row/point dual with nonnegative row prices
supported on ``S_p`` and ordered point prices ``z[u,q]`` allowed only when
``u`` lies in ``S_p`` or ``q=p``.  Thus all non-fiber rows can contribute
only the one common-point compensation price.

Writing ``a[u,q]=z[u,q]`` for ``u in S_p`` and ``t[v]=z[v,p]`` otherwise,
the only nontrivial edge inequalities reduce exactly to

``y[u] <= sum(q in B_v, a[u,q]) + t[v]`` for a cross edge, and
``y[u]+y[v] <= a[u](B_v)+a[v](B_u)`` for an internal fiber edge.

The strict margin is ``sum(d[u]y[u]) > sum(a)+sum(t)``.  This is the finite
four-row local-cover plus common-point-compensation template suggested by the
sparse certificates.  Every floating solution is rechecked by the
Fraction-exact verifier from ``q9_symmetric_point_mass_obstruction``.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

from q9_symmetric_point_mass_obstruction import (
    N,
    exact_certificate,
    fixed_system,
)


def fiber_dual(system: dict, point: int):
    blocks = system["blocks"]
    degree = system["degree"]
    edges = system["edges"]
    caps = system["caps"]
    cap_index = system["cap_index"]
    fiber = {
        row for row, block in enumerate(blocks)
        if point in block and row != point % 8
    }
    if len(fiber) != 4:
        raise ValueError(f"point {point} has non-diagonal fiber size {len(fiber)}")

    variable_count = 2 * N + len(caps)
    matrix = []
    upper = []
    for u, v in edges:
        row = np.zeros(variable_count)
        row[u] = row[v] = 1
        row[N + u] = row[N + v] = -1
        for q in blocks[v]:
            row[2 * N + cap_index[u, q]] -= 1
        for q in blocks[u]:
            row[2 * N + cap_index[v, q]] -= 1
        matrix.append(row)
        upper.append(0)
    margin = np.zeros(variable_count)
    for u in range(N):
        margin[u] = -degree[u]
        margin[N + u] = degree[u]
    margin[2 * N:] = 1
    matrix.append(margin)
    upper.append(-1)

    bounds = []
    for index in range(variable_count):
        if index < N:
            allowed = index in fiber
        elif index < 2 * N:
            # The successful fiber templates need nonnegative row prices;
            # fixing the negative parts to zero makes the reduced criterion
            # substantially cleaner than the unrestricted Farkas dual.
            allowed = False
        else:
            row, q = caps[index - 2 * N]
            allowed = row in fiber or q == point
        bounds.append((0, None) if allowed else (0, 0))
    result = linprog(
        np.ones(variable_count), A_ub=np.array(matrix),
        b_ub=np.array(upper), bounds=bounds, method="highs",
    )
    return fiber, result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("payload", type=Path)
    parser.add_argument("--show-certificates", action="store_true")
    args = parser.parse_args()

    system = fixed_system(json.loads(args.payload.read_text()))
    successful = []
    for point in range(24):
        fiber, result = fiber_dual(system, point)
        if not result.success:
            continue
        certificate = exact_certificate(system, result)
        if certificate is None:
            raise RuntimeError(
                f"fiber {point} floating solution failed exact audit")
        row_support = [row for row, _ in certificate["row_prices"]]
        if not set(row_support) <= fiber:
            raise RuntimeError(f"fiber {point} leaked row support")
        for (row, q), _ in certificate["point_prices"]:
            if row not in fiber and q != point:
                raise RuntimeError(f"fiber {point} leaked point price {(row, q)}")
        summary = {
            "point": point,
            "fiber": sorted(fiber),
            "row_support": row_support,
            "point_price_count": len(certificate["point_prices"]),
            "margin": certificate["margin"],
            "minimum_edge_slack": certificate["minimum_edge_slack"],
        }
        if args.show_certificates:
            summary["certificate"] = certificate
        successful.append(summary)

    print("payload=" + args.payload.name)
    print("successful_fibers=" + json.dumps(
        successful, sort_keys=True, separators=(",", ":")))
    print("successful_points=" + json.dumps(
        [item["point"] for item in successful], separators=(",", ":")))
    print("fiber_price_template=EXACT")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
