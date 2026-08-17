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
routing-array axioms do not by themselves close the branch.  Both displayed
SAT atlases become UNSAT when the ten symmetric 2-regular incidence blocks
and the exact Gram factorization ``R_ce(d)=B_dc^T B_de`` are imposed.  This
confirms computationally that the next full model must retain that certificate.
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


def check_incidence_factorization(witness: list[list[int]]) -> z3.CheckSatResult:
    """Test exact realization by ten symmetric 2-regular incidence blocks."""
    pair_order = list(itertools.combinations(range(4), 2))
    tables = dict(zip(pair_order, witness))

    def routing_color(left: int, right: int, x: int, z: int) -> int:
        if left < right:
            return tables[left, right][(z - x) % 16]
        return tables[right, left][(x - z) % 16]

    solver = z3.Solver()
    blocks = {
        (i, j, x, y): z3.Bool(f"b_{witness[0][1]}_{i}_{j}_{x}_{y}")
        for i in range(4)
        for j in range(i, 4)
        for x in range(16)
        for y in range(16)
    }
    for i in range(4):
        for x in range(16):
            solver.add(z3.Not(blocks[i, i, x, x]))
            for y in range(x):
                solver.add(blocks[i, i, x, y] == blocks[i, i, y, x])

    def incidence(left: int, right: int, x: int, y: int):
        if left <= right:
            return blocks[left, right, x, y]
        return blocks[right, left, y, x]

    for left in range(4):
        for right in range(4):
            for x in range(16):
                solver.add(
                    z3.PbEq(
                        [(incidence(left, right, x, y), 1) for y in range(16)],
                        2,
                    )
                )
    for left, right in itertools.combinations(range(4), 2):
        for routing_component in range(4):
            for x in range(16):
                for z in range(16):
                    product_terms = [
                        z3.And(
                            incidence(routing_component, left, y, x),
                            incidence(routing_component, right, y, z),
                        )
                        for y in range(16)
                    ]
                    target = int(
                        routing_color(left, right, x, z) == routing_component
                    )
                    solver.add(z3.PbEq([(term, 1) for term in product_terms], target))
    return solver.check()


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
        factorization = check_incidence_factorization(witness)
        print(f"  exact-incidence-factorization: {factorization}")
        if factorization != z3.unsat:
            raise SystemExit(f"expected {name}'s factorization to be UNSAT")


if __name__ == "__main__":
    main()
