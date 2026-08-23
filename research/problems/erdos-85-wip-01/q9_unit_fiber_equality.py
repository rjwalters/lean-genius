#!/usr/bin/env python3
"""Exact unit-fiber cover optimum and equality rigidity diagnostic.

Unlike the strict-certificate scan, this retains an optimum whose cost equals
the four-row demanded total.  It Fraction-checks both the point-price cover
and its LP-dual edge mass.  Equality therefore exposes the precise local
fractional packing which saturates the prospective fiber bound.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

from q9_symmetric_point_mass_obstruction import fixed_system


def rational(value: float) -> Fraction:
    return Fraction(float(value)).limit_denominator(10**6)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("payload", type=Path)
    parser.add_argument("--point", type=int, required=True, choices=range(24))
    args = parser.parse_args()

    system = fixed_system(json.loads(args.payload.read_text()))
    point = args.point
    fiber = {
        row for row, block in enumerate(system["blocks"])
        if point in block and row != point % 8
    }
    if len(fiber) != 4:
        raise RuntimeError(f"bad non-diagonal fiber {sorted(fiber)}")
    allowed = [
        index for index, (row, q) in enumerate(system["caps"])
        if row in fiber or q == point
    ]
    position = {old: new for new, old in enumerate(allowed)}
    constrained_edges = []
    cover_rows = []
    needs = []
    for edge in system["edges"]:
        u, v = edge
        need = int(u in fiber) + int(v in fiber)
        if not need:
            continue
        row = [0] * len(allowed)
        for q in system["blocks"][v]:
            index = system["cap_index"][u, q]
            if index in position:
                row[position[index]] += 1
        for q in system["blocks"][u]:
            index = system["cap_index"][v, q]
            if index in position:
                row[position[index]] += 1
        constrained_edges.append(edge)
        cover_rows.append(row)
        needs.append(need)

    cover = np.array(cover_rows, dtype=float)
    result = linprog(
        np.ones(len(allowed)), A_ub=-cover, b_ub=-np.array(needs),
        bounds=(0, None), method="highs",
    )
    if not result.success:
        raise RuntimeError(result.message)
    prices = [rational(value) for value in result.x]
    edge_mass = [rational(-value) for value in result.ineqlin.marginals]

    cover_slacks = []
    for row, need in zip(cover_rows, needs):
        load = sum((Fraction(coefficient) * price
                    for coefficient, price in zip(row, prices)), Fraction())
        if load < need:
            raise RuntimeError("rational point prices violate an edge cover")
        cover_slacks.append(load - need)
    cap_loads = []
    for column in range(len(allowed)):
        load = sum((Fraction(row[column]) * mass
                    for row, mass in zip(cover_rows, edge_mass)), Fraction())
        if load > 1:
            raise RuntimeError("rational dual edge mass violates a capacity")
        cap_loads.append(load)
    price_cost = sum(prices, Fraction())
    dual_value = sum((Fraction(need) * mass
                      for need, mass in zip(needs, edge_mass)), Fraction())
    if price_cost != dual_value:
        raise RuntimeError(f"duality gap: {price_cost} != {dual_value}")

    target = sum(system["degree"][row] for row in fiber)
    row_loads = {
        row: sum((mass for edge, mass in zip(constrained_edges, edge_mass)
                  if row in edge), Fraction())
        for row in sorted(fiber)
    }
    active_prices = [
        (system["caps"][allowed[index]], str(price))
        for index, price in enumerate(prices) if price
    ]
    active_edges = [
        (edge, str(mass)) for edge, mass in zip(constrained_edges, edge_mass)
        if mass
    ]
    print("payload=" + args.payload.name)
    print(f"point={point} fiber={sorted(fiber)}")
    print(f"cost={price_cost} target={target} gap={price_cost-target}")
    print("fiber_row_loads=" + json.dumps(
        {str(row): str(load) for row, load in row_loads.items()},
        separators=(",", ":")))
    print(f"active_point_prices={len(active_prices)} "
          f"tight_edge_covers={sum(slack == 0 for slack in cover_slacks)}")
    print(f"active_dual_edges={len(active_edges)} "
          f"tight_point_caps={sum(load == 1 for load in cap_loads)}")
    print("point_prices=" + json.dumps(active_prices, separators=(",", ":")))
    print("dual_edge_mass=" + json.dumps(active_edges, separators=(",", ":")))
    print("unit_fiber_primal_dual=EXACT")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
