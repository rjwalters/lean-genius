#!/usr/bin/env python3
"""Reduced q=16 countermodel to weight-two cycle synchronization.

This is deliberately not a full 256-vertex A-graph.  It realizes all exact
selector-pair laws visible from one weight-two defect component C: the
internal graph is 2-regular and C4-free, every point of C occurs in q-2
outside two-point traces, trace pairs do not repeat, and a trace pair cannot
already have an internal common neighbor.  Different internal cycles can
nevertheless have different trace/T orientations.
"""

from itertools import combinations

from z3 import Bool, If, Not, Solver, Sum, is_true, sat


Q = 16
N = 2 * Q
TRIANGLE = tuple(range(3))
LONG_CYCLE = tuple(range(3, N))


def cycle_edges(vertices: tuple[int, ...]) -> set[tuple[int, int]]:
    return {
        tuple(sorted((vertices[index], vertices[(index + 1) % len(vertices)])))
        for index in range(len(vertices))
    }


INTERNAL_EDGES = cycle_edges(TRIANGLE) | cycle_edges(LONG_CYCLE)
PAIRS = tuple(combinations(range(N), 2))


def main() -> None:
    selected = {pair: Bool(f"selected_{pair[0]}_{pair[1]}") for pair in PAIRS}
    solver = Solver()

    # Each x in C has q-2 outside A-neighbors.  Counting an outside vertex by
    # its two-point trace turns those traces into a (q-2)-regular simple graph
    # on C; simplicity is the no-repeated-trace consequence of C4-freeness.
    for vertex in range(N):
        solver.add(
            Sum(
                [
                    If(selected[tuple(sorted((vertex, other)))], 1, 0)
                    for other in range(N)
                    if other != vertex
                ]
            )
            == Q - 2
        )

    # A pair with an internal common neighbor already has codegree one and
    # therefore cannot also occur as an outside trace.
    distance_two_pairs = {
        pair
        for pair in PAIRS
        if any(
            tuple(sorted((pair[0], witness))) in INTERNAL_EDGES
            and tuple(sorted((pair[1], witness))) in INTERNAL_EDGES
            for witness in range(N)
        )
    }
    for pair in distance_two_pairs:
        solver.add(Not(selected[pair]))

    # Opposite orientations: the triangle's edges already have their internal
    # common neighbor, whereas every edge of C29 is cross-triangulated.
    for pair in cycle_edges(TRIANGLE):
        solver.add(Not(selected[pair]))
    for pair in cycle_edges(LONG_CYCLE):
        solver.add(selected[pair])

    assert solver.check() == sat
    model = solver.model()
    chosen = {pair for pair in PAIRS if is_true(model.eval(selected[pair]))}

    assert len(chosen) == N * (Q - 2) // 2 == Q * Q - 2 * Q
    assert all(
        sum(tuple(sorted((vertex, other))) in chosen for other in range(N) if other != vertex)
        == Q - 2
        for vertex in range(N)
    )
    assert chosen.isdisjoint(distance_two_pairs)
    assert chosen.isdisjoint(cycle_edges(TRIANGLE))
    assert cycle_edges(LONG_CYCLE) <= chosen
    assert len(chosen & INTERNAL_EDGES) == len(LONG_CYCLE) == 29
    assert 0 < len(chosen & INTERNAL_EDGES) < Q * Q - 2 * Q

    print("verified reduced q=16 selector countermodel")
    print("internal type: C3 + C29")
    print("outside traces: 224; trace-edges: 29")


if __name__ == "__main__":
    main()
