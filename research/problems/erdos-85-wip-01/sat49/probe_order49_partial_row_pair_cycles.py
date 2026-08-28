#!/usr/bin/env python3
"""Census partial row-pair permutation types in the 31 owner triples."""

from __future__ import annotations

import argparse
from collections import Counter

import z3

from probe_order49_three_open_code_holonomy import (
    CODES, PAIR01, PAIR02, PAIR12, build_solver, support,
)


PAIRPOINTS = {0, 1, 2}


def occupied_triples(owner: list[list[int]]) -> set[tuple[int, int, int]]:
    return {
        tuple(owner[h][v] for h in range(3))
        for v in range(46)
        if not ({owner[h][v] for h in range(3)} & PAIRPOINTS)
    }


def partial_permutation_type(mapping: dict[int, int], symbols: tuple[int, ...]):
    undirected = {u: set() for u in symbols}
    indegree = Counter(mapping.values())
    for u, v in mapping.items():
        undirected[u].add(v)
        undirected[v].add(u)
    unseen = set(symbols)
    components = []
    while unseen:
        root = next(iter(unseen))
        stack, component = [root], set()
        while stack:
            u = stack.pop()
            if u in component:
                continue
            component.add(u)
            stack.extend(undirected[u] - component)
        unseen -= component
        edges = sum(1 for u in component if u in mapping)
        cycle = edges > 0 and all(
            u in mapping and indegree[u] == 1 for u in component
        )
        components.append(("C" if cycle else "P", edges))
    return tuple(sorted(components))


def row_pair_signature(owner: list[list[int]]):
    triples = occupied_triples(owner)
    orientations = []
    for row_axis in range(3):
        column_axis = (row_axis + 1) % 3
        symbol_axis = (row_axis + 2) % 3
        rows = tuple(u for u in CODES[row_axis] if support(u) == 1)
        columns = tuple(u for u in CODES[column_axis] if support(u) == 1)
        symbols = tuple(u for u in CODES[symbol_axis] if support(u) == 1)
        lookup = {(cell[row_axis], cell[column_axis]): cell[symbol_axis] for cell in triples}
        types = Counter()
        for i, first in enumerate(rows):
            for second in rows[i + 1:]:
                mapping = {
                    lookup[first, column]: lookup[second, column]
                    for column in columns
                    if (first, column) in lookup and (second, column) in lookup
                }
                types[partial_permutation_type(mapping, symbols)] += 1
        orientations.append(tuple(sorted(types.items())))
    return tuple(orientations)


def coarse_cycle_features(signature):
    """Counts of row pairs exhibiting each nontrivial cycle length by axis."""
    return tuple(
        tuple(sum(count for kind, count in orientation if ("C", length) in kind)
              for length in (2, 3, 4, 5))
        for orientation in signature
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", choices=("000", "001"), required=True)
    parser.add_argument("--samples", type=int, default=64)
    args = parser.parse_args()
    solver, variables = build_solver()
    edges = (
        variables[0][PAIR01] == PAIR02,
        variables[1][PAIR01] == PAIR12,
        variables[2][PAIR02] == PAIR12,
    )
    if args.profile == "000":
        solver.add(*(z3.Not(edge) for edge in edges))
    else:
        solver.add(z3.Not(edges[0]), edges[1], z3.Not(edges[2]))
    signatures = Counter()
    coarse = Counter()
    for _ in range(args.samples):
        if solver.check() != z3.sat:
            break
        model = solver.model()
        owner = [[model.eval(variables[h][v]).as_long() for v in range(46)] for h in range(3)]
        signature = row_pair_signature(owner)
        signatures[signature] += 1
        coarse[coarse_cycle_features(signature)] += 1
        solver.add(z3.Or(*(
            variables[h][v] != owner[h][v]
            for h in range(3) for v in range(46)
        )))
    print(f"profile={args.profile} samples={sum(signatures.values())} signatures={len(signatures)}")
    print(f"coarse_types={len(coarse)} coarse={coarse.most_common()}")
    for signature, count in signatures.most_common():
        print(f"count={count} signature={signature}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
