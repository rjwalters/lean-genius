#!/usr/bin/env python3
"""Probe compatibility of the three ordinary open-code partitions.

This deliberately forgets every ordinary edge not forced by membership in one
of the three high codes.  It retains the exact 46-point support profile, owner
cell sizes, symmetry of every represented edge, and the C4-free condition that
two distinct code owners have at most one common neighbor.  SAT therefore
falsifies a partition-only holonomy terminal; UNSAT would nominate a small
structural core for formalization.
"""

from __future__ import annotations

import argparse
import itertools

import z3


PAIR01, PAIR02, PAIR12 = 0, 1, 2
UNIQUE0 = tuple(range(3, 9))
UNIQUE1 = tuple(range(9, 15))
UNIQUE2 = tuple(range(15, 21))
OUTSIDE = tuple(range(21, 46))
CODES = (
    (PAIR01, PAIR02, *UNIQUE0),
    (PAIR01, PAIR12, *UNIQUE1),
    (PAIR02, PAIR12, *UNIQUE2),
)
SHARED = {(0, 1): PAIR01, (0, 2): PAIR02, (1, 2): PAIR12}


def support(vertex: int) -> int:
    return sum(vertex in code for code in CODES)


def degree(vertex: int) -> int:
    return 7 - support(vertex)


def build_solver() -> tuple[z3.Solver, list[list[z3.IntNumRef]]]:
    solver = z3.Solver()
    owner = [
        [z3.Int(f"owner_{h}_{v}") for v in range(46)] for h in range(3)
    ]

    # Every vertex chooses one owner from each code; loops are forbidden.
    for h, code in enumerate(CODES):
        for v in range(46):
            solver.add(z3.Or(*(owner[h][v] == a for a in code)))
            solver.add(owner[h][v] != v)

    # The owner cells are precisely open neighborhoods, hence have the graph
    # degrees dictated by the support profile.
    for h, code in enumerate(CODES):
        for a in code:
            solver.add(
                z3.Sum(*(z3.If(owner[h][v] == a, 1, 0) for v in range(46)))
                == degree(a)
            )

    # If x--y is represented because y owns x in one code, then every code
    # containing x must choose x as y's owner.  This is exactly edge symmetry
    # plus unique ownership, and includes the matching involutions on a code.
    for h, code in enumerate(CODES):
        for x in range(46):
            containing_x = [k for k, other_code in enumerate(CODES) if x in other_code]
            for y in code:
                for k in containing_x:
                    solver.add(z3.Implies(owner[h][x] == y, owner[k][y] == x))

    # A shared pairpoint owns exactly the same cell in the two corresponding
    # partitions.
    for (h, k), root in SHARED.items():
        for v in range(46):
            solver.add((owner[h][v] == root) == (owner[k][v] == root))

    # Apart from the repeated shared-root cell, every pair of owner labels can
    # occur at most once: two occurrences would be two common neighbors and a C4.
    for (h, k), root in SHARED.items():
        for v in range(46):
            for w in range(v + 1, 46):
                same_pair = z3.And(
                    owner[h][v] == owner[h][w], owner[k][v] == owner[k][w]
                )
                both_central = z3.And(
                    owner[h][v] == root,
                    owner[k][v] == root,
                    owner[h][w] == root,
                    owner[k][w] == root,
                )
                solver.add(z3.Implies(same_pair, both_central))

    return solver, owner


def add_full_ordinary_graph(
    solver: z3.Solver, owner: list[list[z3.IntNumRef]]
) -> dict[tuple[int, int], z3.BoolRef]:
    edges = {
        (x, y): z3.Bool(f"edge_{x}_{y}")
        for x in range(46) for y in range(x + 1, 46)
    }

    def edge(x: int, y: int) -> z3.BoolRef:
        if x == y:
            return z3.BoolVal(False)
        return edges[min(x, y), max(x, y)]

    # Ownership is exactly adjacency into each code.
    for h, code in enumerate(CODES):
        for v in range(46):
            for a in code:
                solver.add((owner[h][v] == a) == edge(v, a))

    # Ordinary degrees are 7 minus high support, so total graph degree is 7.
    for v in range(46):
        solver.add(z3.PbEq([(edge(v, w), 1) for w in range(46) if w != v], degree(v)))

    # An ordinary pair already sharing a high neighbor has no ordinary common
    # neighbor; a disjoint-support pair has at most one.  This is exactly the
    # C4-free condition after the three high vertices are restored.
    for x in range(46):
        for y in range(x + 1, 46):
            shared_high = sum(x in code and y in code for code in CODES)
            bound = 1 - shared_high
            common = [z3.And(edge(x, z), edge(y, z)) for z in range(46)]
            solver.add(z3.PbLe([(term, 1) for term in common], bound))
    return edges


def zero_pattern_bit_formula(
    owner: list[list[z3.IntNumRef]], h: int, k: int, root: int
) -> z3.BoolRef:
    other_h = next(a for a in CODES[h] if support(a) == 2 and a != root)
    other_k = next(a for a in CODES[k] if support(a) == 2 and a != root)
    return z3.And(
        *(z3.Not(z3.And(owner[h][v] == other_h, owner[k][v] == other_k))
          for v in range(46))
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout-ms", type=int, default=60_000)
    parser.add_argument("--print-model", action="store_true")
    parser.add_argument("--all-profiles", action="store_true")
    parser.add_argument("--full-ordinary", action="store_true")
    args = parser.parse_args()

    solver, owner = build_solver()
    if args.full_ordinary:
        add_full_ordinary_graph(solver, owner)
    solver.set(timeout=args.timeout_ms)
    bit_formulas = [
        zero_pattern_bit_formula(owner, h, k, root)
        for (h, k), root in SHARED.items()
    ]
    if args.all_profiles:
        profile_results = {}
        for profile in itertools.product((0, 1), repeat=3):
            solver.push()
            for bit, formula in zip(profile, bit_formulas, strict=True):
                solver.add(formula if bit else z3.Not(formula))
            profile_results[profile] = str(solver.check())
            solver.pop()
        print(f"profile_results {profile_results}")
        return 0 if all(value in ("sat", "unsat") for value in profile_results.values()) else 2
    result = solver.check()
    print(f"three_open_code_holonomy {result}")
    if result == z3.sat:
        model = solver.model()
        bits = []
        for formula in bit_formulas:
            bits.append(int(z3.is_true(model.eval(formula))))
        print(f"zero_pattern_bits {tuple(bits)}")
        if args.print_model:
            for h in range(3):
                values = tuple(model.eval(owner[h][v]).as_long() for v in range(46))
                print(f"owner_{h} {values}")
    return 0 if result in (z3.sat, z3.unsat) else 2


if __name__ == "__main__":
    raise SystemExit(main())
