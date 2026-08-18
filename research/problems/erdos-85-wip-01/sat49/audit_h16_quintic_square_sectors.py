#!/usr/bin/env python3
"""Exact feasibility audit through quintic H16 square sectors.

Global trace/moment feasibility first reduces 36488 fifth-degree moment
signatures to 3405.  For each, the fifth elementary coefficient is bounded
by AM--GM, exact Hankel determinants discard non-real-root candidates, and
Sturm chains certify both the adjacency-root polynomial and the polynomial
of ``mu = 7 - alpha^2``.  Certified quintics are tested against every
reachable degree-at-most-four state.
"""

from __future__ import annotations

import math
from collections import defaultdict

from audit_h16_circulant_tree_squares import bareiss_determinant
from audit_h16_quadratic_square_sectors import Sector, quadratic_sectors
from audit_h16_cubic_square_sectors import cubic_sectors, roots_between
from audit_h16_quartic_square_sectors import quartic_sectors


def lower_states() -> set[tuple[int, ...]]:
    sectors = [
        Sector("mu=6", 1, 6, 36, 1, 1),
        Sector("mu=3", 1, 3, 9, 2, 8),
        Sector("mu=-2", 1, -2, 4, 3, 27),
        *quadratic_sectors(), *cubic_sectors(), *quartic_sectors(),
    ]
    initial = (0, 0, 0, 0, 0, 0)
    states = {initial}
    frontier = {initial}
    while frontier:
        new_states: set[tuple[int, ...]] = set()
        for dimension, defect_trace, defect_square_trace, adjacency_trace, \
                adjacency_cube_trace, mu3_count in frontier:
            for sector in sectors:
                if dimension + sector.degree > 10:
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


def globally_feasible_signatures(states: set[tuple[int, ...]]) -> list[tuple[int, ...]]:
    index: dict[tuple[int, int], list[tuple[int, ...]]] = defaultdict(list)
    for state in states:
        index[(state[3], state[4])].append(state)
    feasible: list[tuple[int, ...]] = []
    degree = 5
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
                e2 = (alpha_trace**2 - alpha2_trace) // 2
                cube_bound = math.isqrt(alpha2_trace * alpha4_trace)
                for alpha3_trace in range(-cube_bound, cube_bound + 1):
                    if alpha_trace == 0 and alpha3_trace < 0:
                        continue
                    numerator3 = (
                        alpha3_trace - alpha_trace * alpha2_trace
                        + e2 * alpha_trace
                    )
                    if numerator3 % 3:
                        continue
                    e3 = numerator3 // 3
                    numerator4 = (
                        alpha_trace * alpha3_trace - e2 * alpha2_trace
                        + e3 * alpha_trace - alpha4_trace
                    )
                    if numerator4 % 4:
                        continue
                    e4 = numerator4 // 4
                    hankel3 = [
                        [degree, alpha_trace, alpha2_trace],
                        [alpha_trace, alpha2_trace, alpha3_trace],
                        [alpha2_trace, alpha3_trace, alpha4_trace],
                    ]
                    if bareiss_determinant(hankel3) < 0:
                        continue
                    possible = False
                    for sign in (-1, 1):
                        needed_trace = -8 - sign * alpha_trace
                        for total_cube in range(-32, 1):
                            needed_cube = total_cube - sign * alpha3_trace
                            for state in index.get((needed_trace, needed_cube), ()):
                                residual_dimension = 10 - state[0]
                                if residual_dimension < 0 or residual_dimension % 2:
                                    continue
                                residual_trace = -7 - (defect_trace + state[1])
                                residual_square_trace = 63 - (
                                    defect_square_trace + state[2]
                                )
                                if residual_square_trace < 0:
                                    continue
                                if ((residual_dimension == 0
                                     and residual_trace == 0
                                     and residual_square_trace == 0)
                                        or (residual_dimension > 0
                                            and residual_trace**2 <=
                                            residual_dimension
                                            * residual_square_trace)):
                                    possible = True
                                    break
                            if possible:
                                break
                        if possible:
                            break
                    if possible:
                        feasible.append((
                            alpha_trace, alpha2_trace, alpha3_trace,
                            alpha4_trace, e2, e3, e4,
                            defect_trace, defect_square_trace,
                        ))
    return feasible


def certified_quintics(signatures: list[tuple[int, ...]]) -> list[Sector]:
    sectors: list[Sector] = []
    degree = 5
    for signature in signatures:
        alpha_trace, alpha2_trace, alpha3_trace, alpha4_trace, \
            e2, e3, e4, defect_trace, defect_square_trace = signature
        # AM--GM on the five nonnegative squared roots:
        # 5^5 * e5^2 <= (sum alpha_i^2)^5.
        e5_bound = math.isqrt(alpha2_trace**5 // degree**5)
        for e5 in range(-e5_bound, e5_bound + 1):
            alpha_poly = [1, -alpha_trace, e2, -e3, e4, -e5]
            alpha5_trace = (
                alpha_trace * alpha4_trace - e2 * alpha3_trace
                + e3 * alpha2_trace - e4 * alpha_trace + degree * e5
            )
            alpha_powers = [
                degree, alpha_trace, alpha2_trace,
                alpha3_trace, alpha4_trace, alpha5_trace,
            ]
            for power in range(6, 11):
                alpha_powers.append(
                    alpha_trace * alpha_powers[power - 1]
                    - e2 * alpha_powers[power - 2]
                    + e3 * alpha_powers[power - 3]
                    - e4 * alpha_powers[power - 4]
                    + e5 * alpha_powers[power - 5]
                )
            # Exact necessary Gram positivity before the costlier Sturm pass.
            if any(bareiss_determinant([
                    [alpha_powers[i + j] for j in range(size)]
                    for i in range(size)
                ]) < 0 for size in (4, 5)):
                continue
            if roots_between(alpha_poly, -4, 4) != degree:
                continue
            defect_powers = [degree]
            for power in range(1, degree + 1):
                defect_powers.append(sum(
                    math.comb(power, index) * 7 ** (power - index)
                    * (-1) ** index * alpha_powers[2 * index]
                    for index in range(power + 1)
                ))
            defect_e = [1]
            for power in range(1, degree + 1):
                numerator = sum(
                    (-1) ** (index - 1)
                    * defect_e[power - index] * defect_powers[index]
                    for index in range(1, power + 1)
                )
                if numerator % power:
                    raise AssertionError("Newton division was not exact")
                defect_e.append(numerator // power)
            defect_poly = [
                1, -defect_e[1], defect_e[2], -defect_e[3],
                defect_e[4], -defect_e[5],
            ]
            if roots_between(defect_poly, -7, 7) == degree:
                sectors.append(Sector(
                    f"quintic:{alpha_trace},{e2},{e3},{e4},{e5}", degree,
                    defect_trace, defect_square_trace,
                    alpha_trace, alpha3_trace,
                ))
    return sectors


def main() -> int:
    states = lower_states()
    signatures = globally_feasible_signatures(states)
    quintics = certified_quintics(signatures)
    if len(states) != 182489 or len(signatures) != 3405:
        raise AssertionError("unexpected lower-state or signature census")
    # Every certified quintic arose from a signature already tested against
    # every lower state.  An empty list therefore closes degree five.
    if quintics:
        raise AssertionError(f"certified quintic survivor: {quintics[0]}")
    print(
        f"lower_states={len(states)} feasible_signatures={len(signatures)} "
        "certified_quintics=0 survivors=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
