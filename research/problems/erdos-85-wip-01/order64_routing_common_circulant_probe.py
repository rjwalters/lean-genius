#!/usr/bin/env python3
"""Rule out a common circulant atlas for the order-64 routing tables.

This is a deliberately restricted diagnostic, not a proof of the full
four-component contradiction.  Label every 16-point component by ``Z/16``
and suppose all six unordered component pairs use one common balanced color
table ``p(y-x)``.  Reversing a pair then uses ``p(x-y)``.  The checked Lean
routing law requires every direct edge of color ``k`` to have at least two
same-color completions through each third component.

Z3 proves that no such common table exists.  The stronger optional ``even``
case additionally imposes ``p(t)=p(-t)``.  In contrast, allowing the six
pair tables to differ produces explicit SAT models even after fixing the
first table to ``t mod 4`` or ``(t // 2) mod 4``.  Thus the currently proved
routing-array axioms do not by themselves close the branch: the next model
must retain the cross-incidence/owner-factor certificate.
"""

from __future__ import annotations

import itertools

import z3


def solve_common(even: bool) -> z3.CheckSatResult:
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


def solve_pair_dependent(first_table: list[int]) -> tuple[z3.CheckSatResult, list[list[int]]]:
    """Allow all six circulant pair tables to differ, fixing table (0,1)."""
    solver = z3.Solver()
    tables = {
        (i, j): [z3.Int(f"q_{first_table[1]}_{i}_{j}_{t}") for t in range(16)]
        for i in range(4)
        for j in range(i + 1, 4)
    }
    for table in tables.values():
        for color in table:
            solver.add(0 <= color, color < 4)
        for k in range(4):
            solver.add(z3.Sum([z3.If(table[t] == k, 1, 0) for t in range(16)]) == 4)

    def routing_color(left: int, right: int, difference: int):
        if left < right:
            return tables[left, right][difference % 16]
        return tables[right, left][-difference % 16]

    for t, color in enumerate(first_table):
        solver.add(tables[0, 1][t] == color)
    for left, middle, right in itertools.permutations(range(4), 3):
        for difference in range(16):
            direct = routing_color(left, right, difference)
            solver.add(
                z3.Sum(
                    [
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
                )
                >= 2
            )
    result = solver.check()
    if result != z3.sat:
        return result, []
    model = solver.model()
    witness = [
        [model.eval(color).as_long() for color in tables[pair]]
        for pair in sorted(tables)
    ]
    return result, witness


def main() -> None:
    common_results = {"common": solve_common(False), "common-even": solve_common(True)}
    for name, result in common_results.items():
        print(f"{name}: {result}")
    if any(result != z3.unsat for result in common_results.values()):
        raise SystemExit("expected both restricted models to be UNSAT")

    first_tables = {
        "pair-dependent-mod4": [t % 4 for t in range(16)],
        "pair-dependent-pairs": [(t // 2) % 4 for t in range(16)],
    }
    for name, first_table in first_tables.items():
        result, witness = solve_pair_dependent(first_table)
        print(f"{name}: {result}")
        if result != z3.sat:
            raise SystemExit(f"expected {name} to be SAT")
        for pair, table in zip(itertools.combinations(range(4), 2), witness):
            print(f"  {pair}: {table}")


if __name__ == "__main__":
    main()
