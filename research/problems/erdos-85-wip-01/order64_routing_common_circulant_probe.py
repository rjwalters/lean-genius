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
The final probe drops circulancy altogether and asks whether any such exact
ten-block certificate exists at this abstraction level.
"""

from __future__ import annotations

import argparse
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


def solve_free_incidence_factorization(
    first_cycle_type: tuple[int, ...] | None = None,
    timeout_ms: int = 300_000,
    enforce_minimum_lifts: bool = False,
    enforce_no_rectangles: bool = True,
    normalize_cross_first_rows: bool = True,
) -> tuple[z3.CheckSatResult, list[list[list[int]]]]:
    """Search for an exact certificate, optionally normalizing block (0,0)."""
    solver = z3.Solver()
    solver.set(timeout=timeout_ms)
    blocks = {
        (i, j, x, y): z3.Bool(f"u_{i}_{j}_{x}_{y}")
        for i in range(4)
        for j in range(i, 4)
        for x in range(16)
        for y in range(16)
    }

    def incidence(left: int, right: int, x: int, y: int):
        if left <= right:
            return blocks[left, right, x, y]
        return blocks[right, left, y, x]

    for i in range(4):
        for x in range(16):
            solver.add(z3.Not(blocks[i, i, x, x]))
            for y in range(x):
                solver.add(blocks[i, i, x, y] == blocks[i, i, y, x])
    if first_cycle_type is not None:
        if sum(first_cycle_type) != 16 or any(length < 3 for length in first_cycle_type):
            raise ValueError("a 2-factor cycle type must partition 16 into parts at least 3")
        canonical_edges: set[tuple[int, int]] = set()
        start = 0
        for length in first_cycle_type:
            cycle = list(range(start, start + length))
            canonical_edges.update(
                (min(cycle[t], cycle[(t + 1) % length]),
                 max(cycle[t], cycle[(t + 1) % length]))
                for t in range(length)
            )
            start += length
        for x in range(16):
            for y in range(16):
                solver.add(blocks[0, 0, x, y] == ((min(x, y), max(x, y)) in canonical_edges))
        if normalize_cross_first_rows:
            # Once component 0 is normalized, the other three component
            # labelings are still independent.  Normalize the two neighbors
            # of its vertex 0 in each first cross row to 0 and 1.
            for right in range(1, 4):
                for y in range(16):
                    solver.add(blocks[0, right, 0, y] == (y in (0, 1)))
    for left in range(4):
        for right in range(4):
            for x in range(16):
                solver.add(z3.PbEq(
                    [(incidence(left, right, x, y), 1) for y in range(16)], 2
                ))
    if enforce_no_rectangles:
        for left in range(4):
            for right in range(left, 4):
                for x1, x2 in itertools.combinations(range(16), 2):
                    for y1, y2 in itertools.combinations(range(16), 2):
                        solver.add(z3.Not(z3.And(
                            blocks[left, right, x1, y1],
                            blocks[left, right, x1, y2],
                            blocks[left, right, x2, y1],
                            blocks[left, right, x2, y2],
                        )))

    routing_cache: dict[tuple[int, int, int, int, int], z3.BoolRef] = {}

    def routing(owner: int, left: int, right: int, x: int, z: int):
        key = owner, left, right, x, z
        if key not in routing_cache:
            routing_cache[key] = z3.Or([
                z3.And(
                    incidence(owner, left, y, x),
                    incidence(owner, right, y, z),
                )
                for y in range(16)
            ])
        return routing_cache[key]

    # Across every pair of endpoint components, the four owner-coordinate
    # Gram products partition the complete 16-by-16 routing array exactly.
    for left, right in itertools.combinations(range(4), 2):
        for x in range(16):
            for z in range(16):
                terms = [
                    z3.And(
                        incidence(owner, left, y, x),
                        incidence(owner, right, y, z),
                    )
                    for owner in range(4)
                    for y in range(16)
                ]
                solver.add(z3.PbEq([(term, 1) for term in terms], 1))
    if enforce_minimum_lifts:
        for left, middle, right in itertools.permutations(range(4), 3):
            for owner in range(4):
                for x in range(16):
                    for w in range(16):
                        solver.add(z3.Implies(
                            routing(owner, left, right, x, w),
                            z3.PbGe([
                                (z3.And(
                                    routing(owner, left, middle, x, z),
                                    routing(owner, middle, right, z, w),
                                ), 1)
                                for z in range(16)
                            ], 2),
                        ))

    result = solver.check()
    if result != z3.sat:
        return result, []
    model = solver.model()
    witness = [
        [
            [y for y in range(16) if z3.is_true(model.eval(incidence(i, j, x, y)))]
            for x in range(16)
        ]
        for i in range(4)
        for j in range(i, 4)
    ]
    return result, witness


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--free-cycle-type",
        help="also solve the free exact system with block (0,0) normalized, e.g. 16 or 8,8",
    )
    parser.add_argument("--minimum-lifts", action="store_true")
    parser.add_argument(
        "--allow-rectangles",
        action="store_true",
        help="drop the ambient C4-free no-rectangle constraints from free blocks",
    )
    parser.add_argument("--timeout-ms", type=int, default=300_000)
    args = parser.parse_args()
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

    if args.free_cycle_type:
        cycle_type = tuple(int(part) for part in args.free_cycle_type.split(","))
        free_result, free_witness = solve_free_incidence_factorization(
            cycle_type, args.timeout_ms, args.minimum_lifts,
            not args.allow_rectangles,
        )
        print(
            f"free-exact-incidence-factorization[{cycle_type},"
            f" minimum-lifts={args.minimum_lifts},"
            f" no-rectangles={not args.allow_rectangles}]: {free_result}"
        )
        if free_result == z3.sat:
            for pair, rows in zip(
                itertools.combinations_with_replacement(range(4), 2), free_witness
            ):
                print(f"  block {pair}: {rows}")


if __name__ == "__main__":
    main()
