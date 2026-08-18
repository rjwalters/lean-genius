#!/usr/bin/env python3
"""Joint lambda-six owner-factorization check without representative classes.

For a fixed cycle partition H of 16, put M equal to the off-diagonal support
of H^2.  Quantify the six-regular graph R directly, impose RH=HR and
R disjoint from M, and define D to be the complement of M union R.  The
remaining variables ask for four two-factors which partition D-complement and
commute with D.  Thus this checker does not use ``r_classify.py``, a list of
representatives, or an identification of spectral H with an owner factor.

An UNSAT result proves the whole fixed-H stratum under these constraints.
A SAT result prints R, D, and the four factor edge sets for further analysis.

Requires the Python ``z3-solver`` package.
"""

from __future__ import annotations

import argparse
from collections.abc import Iterable
from time import monotonic

import z3


N = 16
COLORS = 4
Edge = tuple[int, int]


def edge(u: int, v: int) -> Edge:
    return (u, v) if u < v else (v, u)


ALL_EDGES = [(u, v) for u in range(N) for v in range(u + 1, N)]


def cycle_edges(partition: tuple[int, ...]) -> set[Edge]:
    answer: set[Edge] = set()
    start = 0
    for length in partition:
        vertices = list(range(start, start + length))
        for i, u in enumerate(vertices):
            answer.add(edge(u, vertices[(i + 1) % length]))
        start += length
    if start != N:
        raise ValueError(f"partition has order {start}, expected {N}")
    return answer


def square_support(h_edges: set[Edge]) -> set[Edge]:
    """Off-diagonal Boolean support of the integer adjacency square."""
    return {
        (u, v)
        for u, v in ALL_EDGES
        if any(edge(u, w) in h_edges and edge(w, v) in h_edges for w in range(N))
    }


def pb_eq(values: Iterable[z3.BoolRef], total: int) -> z3.BoolRef:
    return z3.PbEq([(value, 1) for value in values], total)


def solve_partition(
    partition: tuple[int, ...], timeout_ms: int, require_d_triangle: bool
) -> z3.CheckSatResult:
    label = "_".join(map(str, partition))
    h_edges = cycle_edges(partition)
    m_edges = square_support(h_edges)
    if len(m_edges) != N or any(
        sum(edge(u, v) in m_edges for v in range(N) if v != u) != 2
        for u in range(N)
    ):
        raise ValueError(f"{partition}: support(H^2) is not a two-factor")

    r = {pair: z3.Bool(f"p{label}_R_{pair[0]}_{pair[1]}") for pair in ALL_EDGES}
    factors = [
        {
            pair: z3.Bool(f"p{label}_F{color}_{pair[0]}_{pair[1]}")
            for pair in ALL_EDGES
        }
        for color in range(COLORS)
    ]

    def undirected(table: dict[Edge, z3.BoolRef], u: int, v: int) -> z3.BoolRef:
        return z3.BoolVal(False) if u == v else table[edge(u, v)]

    def h_entry(u: int, v: int) -> bool:
        return u != v and edge(u, v) in h_edges

    def m_entry(u: int, v: int) -> bool:
        return u != v and edge(u, v) in m_edges

    def d_entry(u: int, v: int) -> z3.BoolRef:
        if u == v or m_entry(u, v):
            return z3.BoolVal(False)
        return z3.Not(undirected(r, u, v))

    solver = z3.Solver()
    if timeout_ms:
        solver.set(timeout=timeout_ms)

    # R is six-regular and disjoint from support(H^2).
    for pair in m_edges:
        solver.add(z3.Not(r[pair]))
    for u in range(N):
        solver.add(pb_eq((undirected(r, u, v) for v in range(N) if v != u), 6))

    # R H = H R, entrywise over the integers.
    for u in range(N):
        for v in range(N):
            solver.add(
                z3.Sum(
                    [z3.If(undirected(r, u, w), int(h_entry(w, v)), 0) for w in range(N)]
                )
                == z3.Sum(
                    [z3.If(undirected(r, w, v), int(h_entry(u, w)), 0) for w in range(N)]
                )
            )

    # The four colors exactly partition D-complement = M union R.
    for pair in ALL_EDGES:
        selected = [factor[pair] for factor in factors]
        if pair in m_edges:
            solver.add(pb_eq(selected, 1))
        else:
            solver.add(z3.Implies(r[pair], pb_eq(selected, 1)))
            solver.add(z3.Implies(z3.Not(r[pair]), pb_eq(selected, 0)))

    for factor in factors:
        # Every owner color is a two-factor.
        for u in range(N):
            solver.add(
                pb_eq((undirected(factor, u, v) for v in range(N) if v != u), 2)
            )

        # F D = D F, entrywise over the integers.
        for u in range(N):
            for v in range(N):
                solver.add(
                    z3.Sum(
                        [
                            z3.If(z3.And(undirected(factor, u, w), d_entry(w, v)), 1, 0)
                            for w in range(N)
                        ]
                    )
                    == z3.Sum(
                        [
                            z3.If(z3.And(d_entry(u, w), undirected(factor, w, v)), 1, 0)
                            for w in range(N)
                        ]
                    )
                )

    if require_d_triangle:
        solver.add(
            z3.Or(
                [
                    z3.And(d_entry(u, v), d_entry(u, w), d_entry(v, w))
                    for u in range(N)
                    for v in range(u + 1, N)
                    for w in range(v + 1, N)
                ]
            )
        )

    started = monotonic()
    result = solver.check()
    elapsed = monotonic() - started
    print(f"partition {partition}: {result} ({elapsed:.3f}s)")
    if result == z3.sat:
        model = solver.model()

        def chosen(table: dict[Edge, z3.BoolRef]) -> list[Edge]:
            return [pair for pair in ALL_EDGES if z3.is_true(model.eval(table[pair]))]

        r_edges = chosen(r)
        d_edges = [
            pair
            for pair in ALL_EDGES
            if pair not in m_edges and pair not in set(r_edges)
        ]
        d_set = set(d_edges)
        triangles = sum(
            edge(u, v) in d_set
            and edge(u, w) in d_set
            and edge(v, w) in d_set
            for u in range(N)
            for v in range(u + 1, N)
            for w in range(v + 1, N)
        )
        max_codegree = max(
            sum(
                edge(u, w) in d_set and edge(v, w) in d_set
                for w in range(N)
                if w != u and w != v
            )
            for u, v in ALL_EDGES
            if (u, v) not in d_set
        )
        colors: dict[int, int] = {}
        bipartite = True
        for root in range(N):
            if root in colors:
                continue
            colors[root] = 0
            stack = [root]
            while stack:
                u = stack.pop()
                for v in range(N):
                    if u == v or edge(u, v) not in d_set:
                        continue
                    if v not in colors:
                        colors[v] = 1 - colors[u]
                        stack.append(v)
                    elif colors[v] == colors[u]:
                        bipartite = False
        print(f"  R_edges = {r_edges}")
        print(f"  D_edges = {d_edges}")
        print(
            f"  D_triangles = {triangles}; D_bipartite = {bipartite}; "
            f"max_nonedge_codegree = {max_codegree}"
        )
        for color, factor in enumerate(factors):
            print(f"  F{color}_edges = {chosen(factor)}")
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout-ms", type=int, default=0)
    parser.add_argument(
        "--require-d-triangle",
        action="store_true",
        help="restrict to the non-bipartite t(D)>0 strata",
    )
    args = parser.parse_args()
    results = [
        solve_partition((10, 6), args.timeout_ms, args.require_d_triangle),
        solve_partition((5, 5, 3, 3), args.timeout_ms, args.require_d_triangle),
    ]
    return 0 if all(result == z3.unsat for result in results) else 1


if __name__ == "__main__":
    raise SystemExit(main())
