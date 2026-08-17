#!/usr/bin/env python3
"""Exact moment-signature frontier for sextic H16 square sectors.

This is deliberately a frontier audit, not a degree-six exclusion.  It
enumerates every integer first-four-moment signature satisfying Newton
congruences and Hankel positivity, then retains those compatible with some
exact reachable degree-at-most-four state.  Extending the surviving
signatures by their fifth and sixth coefficients remains the next task.
"""

from __future__ import annotations

import hashlib
import json
import math
from collections import defaultdict

from audit_h16_circulant_tree_squares import bareiss_determinant
from audit_h16_quintic_square_sectors import lower_states


def sextic_frontier() -> tuple[int, int, list[tuple[int, ...]]]:
    """Return the checked lower-state count, examined count, and frontier."""
    states = {state for state in lower_states() if state[0] <= 9}
    index: dict[tuple[int, int], list[tuple[int, ...]]] = defaultdict(list)
    for state in states:
        index[(state[3], state[4])].append(state)

    examined = 0
    feasible: list[tuple[int, ...]] = []
    degree = 6
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
                    examined += 1
                    possible = False
                    for sign in (-1, 1):
                        needed_trace = -8 - sign * alpha_trace
                        for total_cube in range(-32, 1):
                            needed_cube = total_cube - sign * alpha3_trace
                            for state in index.get((needed_trace, needed_cube), ()):
                                residual_dimension = 9 - state[0]
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

    return len(states), examined, feasible


def main() -> int:
    state_count, examined, feasible = sextic_frontier()

    digest = hashlib.sha256(
        json.dumps(feasible, separators=(",", ":")).encode()
    ).hexdigest()
    expected_digest = "cf78e91367d09d8345ff7db4b4355c5283ce6c10fa711d2d1d18e9faa3713a5d"
    if (state_count != 137417 or examined != 52434
            or len(feasible) != 4761 or digest != expected_digest):
        raise AssertionError("unexpected sextic frontier census")
    print(
        f"lower_states={state_count} examined_signatures={examined} "
        f"feasible_signatures={len(feasible)} sha256={digest}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
