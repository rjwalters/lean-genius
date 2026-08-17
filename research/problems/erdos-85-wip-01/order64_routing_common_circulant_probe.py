#!/usr/bin/env python3
"""Rule out a common circulant atlas for the order-64 routing tables.

This is a deliberately restricted diagnostic, not a proof of the full
four-component contradiction.  Label every 16-point component by ``Z/16``
and suppose all six unordered component pairs use one common balanced color
table ``p(y-x)``.  Reversing a pair then uses ``p(x-y)``.  The checked Lean
routing law requires every direct edge of color ``k`` to have at least two
same-color completions through each third component.

Z3 proves that no such common table exists.  The stronger optional ``even``
case additionally imposes ``p(t)=p(-t)``.  Thus any surviving order-64 model
must break the most symmetric common-circulant ansatz: different component
pairs need genuinely different tables, non-circulant coordinates, or both.
"""

from __future__ import annotations

import itertools

import z3


def solve(even: bool) -> z3.CheckSatResult:
    solver = z3.Solver()
    colors = [z3.Int(f"p_{int(even)}_{t}") for t in range(16)]
    for color in colors:
        solver.add(0 <= color, color < 4)
    for k in range(4):
        solver.add(z3.Sum([z3.If(colors[t] == k, 1, 0) for t in range(16)]) == 4)
    if even:
        for t in range(16):
            solver.add(colors[t] == colors[-t % 16])

    def routing_color(left: int, right: int, difference: int):
        if left < right:
            return colors[difference % 16]
        return colors[-difference % 16]

    for left, middle, right in itertools.permutations(range(4), 3):
        for difference in range(16):
            direct = routing_color(left, right, difference)
            completions = [
                z3.If(
                    z3.And(
                        routing_color(left, middle, step) == direct,
                        routing_color(middle, right, difference - step) == direct,
                    ),
                    1,
                    0,
                )
                for step in range(16)
            ]
            solver.add(z3.Sum(completions) >= 2)

    # Quotient the global color permutation symmetry.
    solver.add(colors[0] == 0)
    return solver.check()


def main() -> None:
    results = {"common": solve(False), "common-even": solve(True)}
    for name, result in results.items():
        print(f"{name}: {result}")
    if any(result != z3.unsat for result in results.values()):
        raise SystemExit("expected both restricted models to be UNSAT")


if __name__ == "__main__":
    main()
