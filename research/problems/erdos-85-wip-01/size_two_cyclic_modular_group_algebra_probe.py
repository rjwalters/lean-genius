#!/usr/bin/env python3
"""Calibrate the F2[Z/2^k] augmentation filtration on cyclic routing models.

For a subset R of relative base displacements, encode its row polynomial as

    f_R(z) = sum_{r in R} z^r  in F2[z]/(z^q-1).

When q is a power of two this ring is F2[eps]/(eps^q), eps=z+1.  The script
extracts exact SAT models from ``size_two_cyclic_exact_graph_probe`` and
reports eps-adic valuations of every target-difference part of every routing
row.  In particular, a two-route collision at separation d has valuation
2^v2(d); this tests whether reciprocity changes, raises, or merely preserves
the proposed 2-adic collision level.

The default q=4 run uses the full same-difference cap.  At q=8 one can pass
``--c4-difference`` twice to inspect the known satisfiable two-fiber
relaxations; adding 0,2,4 is UNSAT for a=1.
"""

from __future__ import annotations

import argparse
from collections import Counter
from itertools import combinations
from math import comb

import z3

from size_two_cyclic_exact_graph_probe import build


def augmentation_valuation(exponents: list[int], q: int) -> int:
    """Return the (z+1)-adic valuation, with q for the zero polynomial."""
    for degree in range(q):
        coefficient = sum(comb(r, degree) for r in exponents) % 2
        if coefficient:
            return degree
    return q


def v2(n: int) -> int:
    assert n > 0
    value = 0
    while n % 2 == 0:
        value += 1
        n //= 2
    return value


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("q", type=int)
    parser.add_argument("--a", type=int, required=True)
    parser.add_argument("--timeout-ms", type=int, default=300_000)
    parser.add_argument("--c4-difference", type=int, action="append")
    args = parser.parse_args()

    q = args.q
    assert q >= 2 and q & (q - 1) == 0, "q must be a power of two"
    selected = None if args.c4_difference is None else {
        t % q for t in args.c4_difference
    }
    solver, vertices, edge = build(
        q,
        args.a,
        c4_pair_mode="same-difference",
        c4_differences=selected,
    )
    solver.set(timeout=args.timeout_ms)
    result = solver.check()
    print(f"q={q} a={args.a % q} selected={selected}: {result}")
    if result != z3.sat:
        return

    model = solver.model()
    index = {vertex: i for i, vertex in enumerate(vertices)}

    def adjacent(u: tuple[int, int], v: tuple[int, int]) -> bool:
        i, j = index[u], index[v]
        if i == j:
            return False
        return z3.is_true(model.eval(edge[min(i, j), max(i, j)]))

    allowed = sorted({(y - x) % q for x, y in vertices})
    part_valuations: Counter[tuple[int, int]] = Counter()
    collision_pair_levels: Counter[tuple[int, int]] = Counter()
    collision_count = 0

    for x, y in vertices:
        source_t = (y - x) % q
        aggregate: list[int] = []
        for target_s in allowed:
            displacements = []
            for target_x in range(q):
                target = (target_x, (target_x + target_s) % q)
                if target in index and adjacent((x, y), target):
                    displacements.append((target_x - x) % q)
            if not displacements:
                continue
            aggregate.extend(displacements)
            valuation = augmentation_valuation(displacements, q)
            part_valuations[(len(displacements), valuation)] += 1
            for r, s in combinations(displacements, 2):
                collision_count += 1
                separation = (s - r) % q
                level = augmentation_valuation([r, s], q)
                predicted = 1 << v2(separation)
                assert level == predicted, (r, s, level, predicted)
                collision_pair_levels[(v2(separation), level)] += 1

        expected = [r for r in range(q) if r not in {source_t, (source_t + 1) % q}]
        assert sorted(aggregate) == expected
        assert augmentation_valuation(aggregate, q) == 1

    print(f"vertices={len(vertices)} allowed_differences={allowed}")
    print("target-part (cardinality, eps-valuation) distribution:")
    for key, count in sorted(part_valuations.items()):
        print(f"  {key}: {count}")
    print(f"collision_pairs={collision_count}")
    print("collision (v2(separation), eps-valuation) distribution:")
    for key, count in sorted(collision_pair_levels.items()):
        print(f"  {key}: {count}")


if __name__ == "__main__":
    main()
