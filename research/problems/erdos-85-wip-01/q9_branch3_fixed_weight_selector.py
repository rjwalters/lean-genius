#!/usr/bin/env python3
"""Audit two fixed-weight branch-3 incident-point Farkas templates."""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

from q9_symmetric_point_mass_obstruction import (
    N_TRIPLE,
    fixed_system,
    random_outer,
)


TEMPLATES = {
    "balanced": (Fraction(1), Fraction(2), Fraction(1)),
    "exceptional_heavy": (Fraction(3), Fraction(0), Fraction(8)),
}


def fixed_weight_certificate(
    system: dict,
    hole: int,
    diagonal: int,
    offdiagonal: int,
    weights: tuple[Fraction, Fraction, Fraction],
) -> dict | None:
    """Minimize point price with fixed row weights and audit exactly."""
    intersection = (
        system["blocks"][hole] & system["blocks"][offdiagonal]
    )
    if len(intersection) != 1:
        return None
    incident_point = next(iter(intersection))
    diagonal_weight, offdiagonal_weight, hole_weight = weights
    row_price = {
        diagonal: diagonal_weight,
        offdiagonal: offdiagonal_weight,
        hole: hole_weight,
    }
    caps = system["caps"]
    cap_index = system["cap_index"]
    matrix = []
    upper = []
    for u, v in system["edges"]:
        row = np.zeros(len(caps))
        for point in system["blocks"][v]:
            row[cap_index[u, point]] -= 1
        for point in system["blocks"][u]:
            row[cap_index[v, point]] -= 1
        matrix.append(row)
        upper.append(-float(row_price.get(u, 0) + row_price.get(v, 0)))
    support = {hole, diagonal, offdiagonal}
    allowed = [
        cap_row in support or point == incident_point
        for cap_row, point in caps
    ]
    result = linprog(
        np.ones(len(caps)),
        A_ub=np.array(matrix),
        b_ub=np.array(upper),
        bounds=[(0, None) if keep else (0, 0) for keep in allowed],
        method="highs",
    )
    if not result.success:
        return None
    point_price = [
        Fraction(float(value)).limit_denominator(10**6)
        for value in result.x
    ]
    if any(value < 0 for value in point_price):
        return None
    for u, v in system["edges"]:
        cover = sum(
            (point_price[cap_index[u, point]]
             for point in system["blocks"][v]),
            Fraction(),
        ) + sum(
            (point_price[cap_index[v, point]]
             for point in system["blocks"][u]),
            Fraction(),
        )
        if cover < row_price.get(u, 0) + row_price.get(v, 0):
            return None
    target = sum(
        Fraction(system["degree"][row]) * weight
        for row, weight in row_price.items()
    )
    margin = target - sum(point_price, Fraction())
    if margin <= 0:
        return None
    return {
        "hole": hole,
        "diagonal": diagonal,
        "offdiagonal": offdiagonal,
        "incident_point": incident_point,
        "weights": [str(weight) for weight in weights],
        "margin": str(margin),
        "point_price_count": sum(value != 0 for value in point_price),
    }


def scan(system: dict) -> dict:
    if system["branch"] != 3:
        raise ValueError("fixed-weight selector requires branch 3")
    holes_begin = N_TRIPLE - 2
    certificates = {name: [] for name in TEMPLATES}
    for name, weights in TEMPLATES.items():
        for hole in range(holes_begin, N_TRIPLE):
            for offdiagonal in range(8, 16):
                if system["blocks"][hole].isdisjoint(
                    system["blocks"][offdiagonal]
                ):
                    continue
                for diagonal in range(8):
                    certificate = fixed_weight_certificate(
                        system, hole, diagonal, offdiagonal, weights
                    )
                    if certificate is not None:
                        certificates[name].append(certificate)
    return {
        "counts": {
            name: len(found) for name, found in certificates.items()
        },
        "exists_fixed_weight_certificate": any(certificates.values()),
        "certificates": certificates,
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
    system = fixed_system(payload)
    print(json.dumps(scan(system), separators=(",", ":")))


if __name__ == "__main__":
    main()
