#!/usr/bin/env python3
"""Exact feasibility audit for nonlinear quadratic H16 square sectors.

Let ``alpha`` be an adjacency eigenvalue on the order-16 residual block and
``mu = 7 - alpha^2`` the corresponding defect eigenvalue.  This script
enumerates every irreducible quadratic minimal polynomial
``alpha^2 - s*alpha + n`` whose two real roots lie in ``[-sqrt(14),sqrt(14)]``.
The coefficient bounds are exhaustive: ``|s| <= 7`` and ``|n| <= 14``.
Changing ``alpha`` to ``-alpha`` lets us retain only ``s > 0``; ``s = 0``
makes ``alpha^2``, hence ``mu``, rational and belongs to the linear audit.

It then performs exact unbounded-knapsack enumeration (dimension at most 15)
of these sectors together with rational square sectors ``mu = 6,3,-2``.
Necessary conditions are the H16 first two defect moments, Cauchy on the
remaining spectrum, the multiplicity-three cap, trace -8, cubic color order
at most 16, and even dimension of the remaining nonsquare primary sectors.
The asserted result is that no quadratic-square configuration survives.
"""

from __future__ import annotations

import math
from dataclasses import dataclass


@dataclass(frozen=True)
class Sector:
    name: str
    degree: int
    defect_trace: int
    defect_square_trace: int
    adjacency_trace: int
    adjacency_cube_trace: int


def quadratic_sectors() -> list[Sector]:
    sectors: list[Sector] = []
    for trace in range(1, 8):
        for norm in range(-14, 15):
            discriminant = trace * trace - 4 * norm
            if discriminant <= 0 or math.isqrt(discriminant) ** 2 == discriminant:
                continue
            root = math.sqrt(discriminant)
            conjugates = ((trace + root) / 2, (trace - root) / 2)
            if max(abs(value) for value in conjugates) > math.sqrt(14) + 1e-12:
                continue
            alpha2_trace = trace * trace - 2 * norm
            alpha3_trace = trace**3 - 3 * norm * trace
            alpha4_trace = trace**4 - 4 * trace * trace * norm + 2 * norm * norm
            defect_trace = 14 - alpha2_trace
            defect_square_trace = 98 - 14 * alpha2_trace + alpha4_trace
            if defect_square_trace <= 63:
                sectors.append(Sector(
                    f"x^2-{trace}x+({norm})", 2,
                    defect_trace, defect_square_trace,
                    trace, alpha3_trace,
                ))
    return sectors


def main() -> int:
    sectors = [
        Sector("mu=6", 1, 6, 36, 1, 1),
        Sector("mu=3", 1, 3, 9, 2, 8),
        Sector("mu=-2", 1, -2, 4, 3, 27),
        *quadratic_sectors(),
    ]
    if len(sectors) != 19:
        raise AssertionError(f"unexpected sector census: {len(sectors)}")

    survivors: list[tuple] = []

    def visit(start: int, dimension: int, defect_trace: int,
              defect_square_trace: int, adjacency_trace: int,
              adjacency_cube_trace: int, mu3_count: int,
              chosen: tuple[tuple[str, int], ...]) -> None:
        residual_dimension = 15 - dimension
        residual_trace = -7 - defect_trace
        residual_square_trace = 63 - defect_square_trace
        if (residual_dimension >= 0 and residual_dimension % 2 == 0
                and adjacency_trace == -8
                and -32 <= adjacency_cube_trace <= 0
                and residual_square_trace >= 0
                and ((residual_dimension == 0
                      and residual_trace == 0
                      and residual_square_trace == 0)
                     or (residual_dimension > 0
                         and residual_trace**2 <=
                         residual_dimension * residual_square_trace))):
            survivors.append((chosen, residual_dimension, residual_trace,
                              residual_square_trace,
                              -adjacency_cube_trace // 2))
        if dimension >= 15:
            return
        for index in range(start, len(sectors)):
            sector = sectors[index]
            if dimension + sector.degree > 15:
                continue
            if defect_square_trace + sector.defect_square_trace > 63:
                continue
            if sector.name == "mu=3" and mu3_count >= 3:
                continue
            for sign in (-1, 1):
                visit(
                    index,
                    dimension + sector.degree,
                    defect_trace + sector.defect_trace,
                    defect_square_trace + sector.defect_square_trace,
                    adjacency_trace + sign * sector.adjacency_trace,
                    adjacency_cube_trace + sign * sector.adjacency_cube_trace,
                    mu3_count + (sector.name == "mu=3"),
                    chosen + ((sector.name, sign),),
                )

    visit(0, 0, 0, 0, 0, 0, 0, ())
    if survivors:
        raise AssertionError(f"quadratic square-sector survivor: {survivors[0]}")
    print(f"sector_types={len(sectors)} quadratic_types={len(sectors) - 3}")
    print("survivors=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
