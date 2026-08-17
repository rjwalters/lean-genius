#!/usr/bin/env python3
"""Exact coefficient extension for sextic H16 square sectors.

The frontier audit fixes the first four power sums and elementary
coefficients.  This script bounds ``e5`` from the fifth moment and ``e6``
from the sixth-moment interval, then applies exact Hankel and Sturm tests to
the alpha roots and their images ``mu = 7 - alpha^2``.
"""

from __future__ import annotations

import hashlib
import json
import math

from audit_h16_circulant_tree_squares import bareiss_determinant
from audit_h16_cubic_square_sectors import roots_between
from audit_h16_quadratic_square_sectors import Sector
from audit_h16_sextic_square_sector_signatures import sextic_frontier


def ceil_div(numerator: int, denominator: int) -> int:
    return -((-numerator) // denominator)


def all_two_by_two_principal_minors_nonnegative(
        matrix: list[list[int]]) -> bool:
    for row in range(len(matrix)):
        if matrix[row][row] < 0:
            return False
        for column in range(row):
            if (matrix[row][row] * matrix[column][column]
                    < matrix[row][column] ** 2):
                return False
    return True


def certified_sextics(signatures: list[tuple[int, ...]]) \
        -> tuple[int, int, int, int, int, list[Sector]]:
    degree = 6
    derivative_survivors = 0
    coefficient_pairs = 0
    minor_survivors = 0
    hankel_survivors = 0
    alpha_real_survivors = 0
    sectors: list[Sector] = []
    for signature in signatures:
        alpha_trace, alpha2_trace, alpha3_trace, alpha4_trace, \
            e2, e3, e4, defect_trace, defect_square_trace = signature

        # |p5| <= sqrt(14) p4, together with p5 = base5 + 5 e5.
        base5 = (
            alpha_trace * alpha4_trace - e2 * alpha3_trace
            + e3 * alpha2_trace - e4 * alpha_trace
        )
        fifth_bound = math.isqrt(14 * alpha4_trace**2)
        e5_low = ceil_div(-fifth_bound - base5, degree - 1)
        e5_high = (fifth_bound - base5) // (degree - 1)
        # AM--GM on the six nonnegative squared alpha roots.
        e6_bound = math.isqrt(alpha2_trace**degree // degree**degree)

        for e5 in range(e5_low, e5_high + 1):
            alpha5_trace = base5 + (degree - 1) * e5
            derivative_poly = [
                degree, -(degree - 1) * alpha_trace,
                (degree - 2) * e2, -(degree - 3) * e3,
                (degree - 4) * e4, -e5,
            ]
            # Rolle: a real-rooted sextic in the interval has all five
            # derivative roots there.  Crucially, this test precedes e6.
            if roots_between(derivative_poly, -4, 4) != degree - 1:
                continue
            derivative_survivors += 1
            base6 = (
                alpha_trace * alpha5_trace - e2 * alpha4_trace
                + e3 * alpha3_trace - e4 * alpha2_trace
                + e5 * alpha_trace
            )
            # Cauchy and the root bound alpha^2 <= 14 give
            # p4^2/p2 <= p6 <= 14 p4.  The zero case is forced.
            if alpha2_trace == 0:
                p6_low = p6_high = 0
            else:
                p6_low = ceil_div(alpha4_trace**2, alpha2_trace)
                p6_high = 14 * alpha4_trace
            e6_low = max(-e6_bound, ceil_div(base6 - p6_high, degree))
            e6_high = min(e6_bound, (base6 - p6_low) // degree)

            for e6 in range(e6_low, e6_high + 1):
                coefficient_pairs += 1
                alpha6_trace = base6 - degree * e6
                alpha_poly = [
                    1, -alpha_trace, e2, -e3, e4, -e5, e6,
                ]
                alpha_powers = [
                    degree, alpha_trace, alpha2_trace, alpha3_trace,
                    alpha4_trace, alpha5_trace, alpha6_trace,
                ]
                for power in range(7, 13):
                    alpha_powers.append(
                        alpha_trace * alpha_powers[power - 1]
                        - e2 * alpha_powers[power - 2]
                        + e3 * alpha_powers[power - 3]
                        - e4 * alpha_powers[power - 4]
                        + e5 * alpha_powers[power - 5]
                        - e6 * alpha_powers[power - 6]
                    )
                moment = [
                    [alpha_powers[i + j] for j in range(degree)]
                    for i in range(degree)
                ]
                localizing = [
                    [14 * alpha_powers[i + j] - alpha_powers[i + j + 2]
                     for j in range(degree - 1)]
                    for i in range(degree - 1)
                ]
                if not (all_two_by_two_principal_minors_nonnegative(moment)
                        and all_two_by_two_principal_minors_nonnegative(
                            localizing)):
                    continue
                minor_survivors += 1
                if any(bareiss_determinant([
                        [alpha_powers[i + j] for j in range(size)]
                        for i in range(size)
                    ]) < 0 for size in (4, 5, 6)):
                    continue
                hankel_survivors += 1
                if roots_between(alpha_poly, -4, 4) != degree:
                    continue
                alpha_real_survivors += 1

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
                    defect_e[4], -defect_e[5], defect_e[6],
                ]
                if roots_between(defect_poly, -7, 7) == degree:
                    sectors.append(Sector(
                        "sextic:"
                        f"{alpha_trace},{e2},{e3},{e4},{e5},{e6}",
                        degree, defect_trace, defect_square_trace,
                        alpha_trace, alpha3_trace,
                    ))
    return (derivative_survivors, coefficient_pairs,
            minor_survivors, hankel_survivors,
            alpha_real_survivors, sectors)


def main() -> int:
    state_count, examined, signatures = sextic_frontier()
    derivatives, pairs, minors, hankel, alpha_real, sextics = \
        certified_sextics(signatures)
    digest = hashlib.sha256(json.dumps(
        [sector.name for sector in sextics], separators=(",", ":")
    ).encode()).hexdigest()
    expected = (
        137417, 52434, 4761, 112877, 33484067, 2464, 0, 0, 0,
        "4f53cda18c2baa0c0354bb5f9a3ecbe5ed12ab4d8e11ba873c2f11161202b945",
    )
    observed = (
        state_count, examined, len(signatures), derivatives, pairs, minors,
        hankel, alpha_real, len(sextics), digest,
    )
    if observed != expected:
        raise AssertionError(
            f"unexpected sextic coefficient census: {observed!r}"
        )
    print(
        f"lower_states={state_count} examined_signatures={examined} "
        f"feasible_signatures={len(signatures)} "
        f"derivative_survivors={derivatives} coefficient_pairs={pairs} "
        f"minor_survivors={minors} hankel_survivors={hankel} "
        f"alpha_real_survivors={alpha_real} "
        f"certified_sextics={len(sextics)} sha256={digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
