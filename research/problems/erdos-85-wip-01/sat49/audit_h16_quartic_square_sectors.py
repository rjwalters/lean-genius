#!/usr/bin/env python3
"""Exact feasibility audit with one quartic H16 square sector.

Quartic candidates are generated from their first four integer power sums.
Newton identities recover the monic polynomial of ``alpha``; its recurrence
then supplies the even power sums needed to construct the polynomial of
``mu = 7 - alpha^2``.  Exact Sturm counting requires all four ``mu`` roots
to lie in ``(-7,7)``.  Reducible candidates are deliberately retained, so
the resulting 1904 types are an over-approximation of irreducible quartic
square sectors.

Each quartic type is combined with every reachable rational/quadratic/cubic
state under the H16 trace, cubic-color, moment, parity, and Cauchy constraints.
No state survives in this scope. Combinations containing two or more
quartic sectors are not covered by this audit.
"""

from __future__ import annotations

import math
from collections import defaultdict

from audit_h16_quadratic_square_sectors import Sector, quadratic_sectors
from audit_h16_cubic_square_sectors import cubic_sectors, roots_between


def quartic_sectors() -> list[Sector]:
    sectors: list[Sector] = []
    degree = 4
    for alpha2_trace in range(14 * degree + 1):
        for defect_square_trace in range(64):
            alpha4_trace = (
                defect_square_trace - 49 * degree + 14 * alpha2_trace
            )
            if not 0 <= alpha4_trace <= 14 * alpha2_trace:
                continue
            if alpha2_trace**2 > degree * alpha4_trace:
                continue
            defect_trace = 7 * degree - alpha2_trace
            if defect_trace**2 > degree * defect_square_trace:
                continue
            for alpha_trace in range(math.isqrt(degree * alpha2_trace) + 1):
                if (alpha_trace**2 - alpha2_trace) % 2:
                    continue
                e1 = alpha_trace
                e2 = (alpha_trace**2 - alpha2_trace) // 2
                cube_bound = math.isqrt(alpha2_trace * alpha4_trace)
                for alpha3_trace in range(-cube_bound, cube_bound + 1):
                    if alpha_trace == 0 and alpha3_trace < 0:
                        continue
                    numerator3 = alpha3_trace - e1 * alpha2_trace + e2 * e1
                    if numerator3 % 3:
                        continue
                    e3 = numerator3 // 3
                    numerator4 = (
                        e1 * alpha3_trace - e2 * alpha2_trace
                        + e3 * e1 - alpha4_trace
                    )
                    if numerator4 % 4:
                        continue
                    e4 = numerator4 // 4
                    hankel_det = (
                        degree * (alpha2_trace * alpha4_trace - alpha3_trace**2)
                        - alpha_trace *
                        (alpha_trace * alpha4_trace
                         - alpha2_trace * alpha3_trace)
                        + alpha2_trace *
                        (alpha_trace * alpha3_trace - alpha2_trace**2)
                    )
                    if hankel_det < 0:
                        continue

                    alpha_powers = [
                        degree, alpha_trace, alpha2_trace,
                        alpha3_trace, alpha4_trace,
                    ]
                    for power in range(5, 9):
                        alpha_powers.append(
                            e1 * alpha_powers[power - 1]
                            - e2 * alpha_powers[power - 2]
                            + e3 * alpha_powers[power - 3]
                            - e4 * alpha_powers[power - 4]
                        )
                    defect_powers = [degree]
                    for power in range(1, 5):
                        defect_powers.append(sum(
                            math.comb(power, index) * 7 ** (power - index)
                            * (-1) ** index * alpha_powers[2 * index]
                            for index in range(power + 1)
                        ))
                    defect_e = [1]
                    for power in range(1, 5):
                        numerator = sum(
                            (-1) ** (index - 1)
                            * defect_e[power - index] * defect_powers[index]
                            for index in range(1, power + 1)
                        )
                        if numerator % power:
                            raise AssertionError("Newton division was not exact")
                        defect_e.append(numerator // power)
                    defect_poly = [
                        1, -defect_e[1], defect_e[2],
                        -defect_e[3], defect_e[4],
                    ]
                    if roots_between(defect_poly, -7, 7) != 4:
                        continue
                    sectors.append(Sector(
                        f"quartic:{e1},{e2},{e3},{e4}", degree,
                        defect_trace, defect_square_trace,
                        alpha_trace, alpha3_trace,
                    ))
    return sectors


def lower_states() -> set[tuple[int, ...]]:
    sectors = [
        Sector("mu=6", 1, 6, 36, 1, 1),
        Sector("mu=3", 1, 3, 9, 2, 8),
        Sector("mu=-2", 1, -2, 4, 3, 27),
        *quadratic_sectors(),
        *cubic_sectors(),
    ]
    initial = (0, 0, 0, 0, 0, 0)
    states = {initial}
    frontier = {initial}
    while frontier:
        new_states: set[tuple[int, ...]] = set()
        for dimension, defect_trace, defect_square_trace, adjacency_trace, \
                adjacency_cube_trace, mu3_count in frontier:
            for sector in sectors:
                if dimension + sector.degree > 11:
                    continue
                if defect_square_trace + sector.defect_square_trace > 63:
                    continue
                increment = sector.name == "mu=3"
                if mu3_count + increment > 3:
                    continue
                for sign in (-1, 1):
                    new_states.add((
                        dimension + sector.degree,
                        defect_trace + sector.defect_trace,
                        defect_square_trace + sector.defect_square_trace,
                        adjacency_trace + sign * sector.adjacency_trace,
                        adjacency_cube_trace + sign * sector.adjacency_cube_trace,
                        mu3_count + increment,
                    ))
        frontier = new_states - states
        states.update(frontier)
    return states


def main() -> int:
    quartics = quartic_sectors()
    states = lower_states()
    if len(quartics) != 1904 or len(states) != 92465:
        raise AssertionError("unexpected quartic or lower-state census")
    index: dict[tuple[int, int], list[tuple[int, ...]]] = defaultdict(list)
    for state in states:
        index[(state[3], state[4])].append(state)

    survivors = []
    for sector in quartics:
        for sign in (-1, 1):
            needed_trace = -8 - sign * sector.adjacency_trace
            for total_cube in range(-32, 1):
                needed_cube = total_cube - sign * sector.adjacency_cube_trace
                for state in index.get((needed_trace, needed_cube), ()):
                    dimension = sector.degree + state[0]
                    if dimension > 15:
                        continue
                    residual_dimension = 15 - dimension
                    if residual_dimension % 2:
                        continue
                    residual_trace = -7 - (sector.defect_trace + state[1])
                    residual_square_trace = 63 - (
                        sector.defect_square_trace + state[2]
                    )
                    if residual_square_trace < 0:
                        continue
                    if ((residual_dimension == 0 and residual_trace == 0
                         and residual_square_trace == 0)
                            or (residual_dimension > 0
                                and residual_trace**2 <= residual_dimension
                                * residual_square_trace)):
                        survivors.append((sector, sign, state, total_cube))

    if survivors:
        raise AssertionError(f"quartic square-sector survivor: {survivors[0]}")
    print(f"quartic_types={len(quartics)} lower_states={len(states)} survivors=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
