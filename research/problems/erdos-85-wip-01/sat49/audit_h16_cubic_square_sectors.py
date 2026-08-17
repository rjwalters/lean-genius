#!/usr/bin/env python3
"""Exact feasibility audit through cubic H16 square sectors.

This extends ``audit_h16_quadratic_square_sectors.py`` to every irreducible
cubic minimal polynomial of an adjacency square root ``alpha``.  Vieta and
``|alpha_i| <= sqrt(14)`` give the exhaustive coefficient bounds
``|e1| <= 11``, ``|e2| <= 42``, ``|e3| <= 52``.  We quotient by
``alpha -> -alpha`` and retain nonnegative trace.

All interval checks are exact: the polynomial of ``mu = 7 - alpha^2`` is
constructed over the integers and a rational Sturm chain verifies that its
three roots lie in ``(-7,7)``.  A bounded reachability search then combines
all rational, quadratic, and cubic square sectors.  The asserted census has
161 sector types, 132108 reachable states, and no feasible H16 spectrum.
"""

from __future__ import annotations

from fractions import Fraction
from math import isqrt

from audit_h16_quadratic_square_sectors import Sector, quadratic_sectors


def trim(poly: list[Fraction]) -> list[Fraction]:
    while poly and poly[0] == 0:
        poly.pop(0)
    return poly


def remainder(dividend: list[Fraction], divisor: list[Fraction]) -> list[Fraction]:
    work = dividend[:]
    while work and len(work) >= len(divisor):
        scale = work[0] / divisor[0]
        for index, coefficient in enumerate(divisor):
            work[index] -= scale * coefficient
        trim(work)
    return work


def derivative(poly: list[Fraction]) -> list[Fraction]:
    degree = len(poly) - 1
    return [coefficient * (degree - index)
            for index, coefficient in enumerate(poly[:-1])]


def evaluate(poly: list[Fraction], value: Fraction) -> Fraction:
    result = Fraction(0)
    for coefficient in poly:
        result = result * value + coefficient
    return result


def sign_variations(values: list[Fraction]) -> int:
    signs = [1 if value > 0 else -1 for value in values if value]
    return sum(left != right for left, right in zip(signs, signs[1:]))


def roots_between(poly: list[int], left: int, right: int) -> int:
    chain = [[Fraction(coefficient) for coefficient in poly]]
    chain.append(derivative(chain[0]))
    while chain[-1]:
        next_poly = [-coefficient
                     for coefficient in remainder(chain[-2], chain[-1])]
        if not next_poly:
            break
        chain.append(next_poly)
    left_variations = sign_variations(
        [evaluate(item, Fraction(left)) for item in chain]
    )
    right_variations = sign_variations(
        [evaluate(item, Fraction(right)) for item in chain]
    )
    return left_variations - right_variations


def integer_divisors(value: int) -> set[int]:
    absolute = abs(value)
    result: set[int] = set()
    for divisor in range(1, isqrt(absolute) + 1):
        if absolute % divisor == 0:
            result.update((divisor, -divisor,
                           absolute // divisor, -(absolute // divisor)))
    return result


def cubic_sectors() -> list[Sector]:
    sectors: list[Sector] = []
    for trace in range(0, 12):
        for e2 in range(-42, 43):
            for e3 in range(-52, 53):
                if e3 == 0 or (trace == 0 and e3 < 0):
                    continue
                discriminant = (
                    trace * trace * e2 * e2 - 4 * e2**3
                    - 4 * trace**3 * e3 - 27 * e3 * e3
                    + 18 * trace * e2 * e3
                )
                if discriminant <= 0:
                    continue
                if any(
                    root**3 - trace * root * root + e2 * root - e3 == 0
                    for root in integer_divisors(e3)
                ):
                    continue
                alpha2_trace = trace * trace - 2 * e2
                alpha3_trace = trace**3 - 3 * trace * e2 + 3 * e3
                alpha4_trace = (
                    trace * alpha3_trace - e2 * alpha2_trace + e3 * trace
                )
                defect_trace = 21 - alpha2_trace
                defect_square_trace = 147 - 14 * alpha2_trace + alpha4_trace
                if not 0 <= defect_square_trace <= 63:
                    continue
                defect_e2 = (
                    defect_trace * defect_trace - defect_square_trace
                ) // 2
                defect_e3 = 7 * (7 + e2) ** 2 - (7 * trace + e3) ** 2
                defect_poly = [1, -defect_trace, defect_e2, -defect_e3]
                if roots_between(defect_poly, -7, 7) != 3:
                    continue
                sectors.append(Sector(
                    f"x^3-{trace}x^2+({e2})x-({e3})", 3,
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
        *cubic_sectors(),
    ]
    if len(cubic_sectors()) != 142 or len(sectors) != 161:
        raise AssertionError("unexpected square-sector type census")

    # State: dimension, defect trace, defect square trace, adjacency trace,
    # adjacency cube trace, and multiplicity of defect eigenvalue 3.
    initial = (0, 0, 0, 0, 0, 0)
    states = {initial}
    frontier = {initial}
    while frontier:
        new_states: set[tuple[int, ...]] = set()
        for dimension, defect_trace, defect_square_trace, adjacency_trace, \
                adjacency_cube_trace, mu3_count in frontier:
            for sector in sectors:
                if dimension + sector.degree > 15:
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

    survivors = []
    for dimension, defect_trace, defect_square_trace, adjacency_trace, \
            adjacency_cube_trace, mu3_count in states:
        residual_dimension = 15 - dimension
        residual_trace = -7 - defect_trace
        residual_square_trace = 63 - defect_square_trace
        if residual_dimension < 0 or residual_dimension % 2:
            continue
        if adjacency_trace != -8 or not -32 <= adjacency_cube_trace <= 0:
            continue
        if residual_square_trace < 0:
            continue
        if ((residual_dimension == 0 and residual_trace == 0
             and residual_square_trace == 0)
                or (residual_dimension > 0 and residual_trace**2 <=
                    residual_dimension * residual_square_trace)):
            survivors.append((dimension, defect_trace, defect_square_trace,
                              adjacency_cube_trace, mu3_count))

    if len(states) != 132108:
        raise AssertionError(f"unexpected reachability census: {len(states)}")
    if survivors:
        raise AssertionError(f"cubic square-sector survivor: {survivors[0]}")
    print("linear_types=3 quadratic_types=16 cubic_types=142")
    print(f"reachable_states={len(states)} survivors=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
