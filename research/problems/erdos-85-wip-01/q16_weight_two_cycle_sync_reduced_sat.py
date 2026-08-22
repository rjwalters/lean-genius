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
SHORT_CYCLE = tuple(range(6))
LONG_CYCLE = tuple(range(6, N))


def cycle_edges(vertices: tuple[int, ...]) -> set[tuple[int, int]]:
    return {
        tuple(sorted((vertices[index], vertices[(index + 1) % len(vertices)])))
        for index in range(len(vertices))
    }


INTERNAL_EDGES = cycle_edges(SHORT_CYCLE) | cycle_edges(LONG_CYCLE)
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

    # The full cross-block equation HM + MK = J forces the exact integral
    # commutator [H, MM^T] = 0.  Off the diagonal, MM^T is precisely this
    # simple trace-pair graph, so impose [H,F] = 0 already at the reduced
    # layer rather than retaining only degree and pair exclusions.
    internal_neighbors = {
        vertex: [
            other
            for other in range(N)
            if tuple(sorted((vertex, other))) in INTERNAL_EDGES
        ]
        for vertex in range(N)
    }
    for first in range(N):
        for second in range(N):
            solver.add(
                Sum(
                    [
                        If(selected[tuple(sorted((witness, second)))], 1, 0)
                        for witness in internal_neighbors[first]
                        if witness != second
                    ]
                )
                == Sum(
                    [
                        If(selected[tuple(sorted((first, witness)))], 1, 0)
                        for witness in internal_neighbors[second]
                        if witness != first
                    ]
                )
            )

    # Opposite orientations on two genuinely orientable even cycles: C6 is
    # T-saturated, whereas every edge of C26 is cross-triangulated.
    for pair in cycle_edges(SHORT_CYCLE):
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
    assert chosen.isdisjoint(cycle_edges(SHORT_CYCLE))
    assert cycle_edges(LONG_CYCLE) <= chosen
    assert len(chosen & INTERNAL_EDGES) == len(LONG_CYCLE) == 26
    # With no internal triangles, the corrected synchronization endpoints are
    # zero and all 2q internal edges, not the total number of outside traces.
    assert 0 < len(chosen & INTERNAL_EDGES) < 2 * Q

    # Realize the unique-common-neighbor requirement on every cross edge.
    # Regard each chosen pair as one outside vertex, adjacent across the cut
    # to its two endpoints.  An edge-trace already resolves both cross edges
    # through the other endpoint in C.  At each x, pair the remaining
    # incident outside vertices; the resulting outside edge resolves those
    # two cross edges through an outside common neighbor.
    outside_vertices = tuple(sorted(chosen))
    trace_is_edge = {trace: trace in INTERNAL_EDGES for trace in outside_vertices}
    outside_edges: set[tuple[tuple[int, int], tuple[int, int]]] = set()
    for vertex in range(N):
        unresolved = sorted(
            trace
            for trace in outside_vertices
            if vertex in trace and not trace_is_edge[trace]
        )
        assert len(unresolved) % 2 == 0
        for index in range(0, len(unresolved), 2):
            edge = tuple(sorted((unresolved[index], unresolved[index + 1])))
            assert edge not in outside_edges
            outside_edges.add(edge)

    def outside_neighbors(trace):
        return {
            second if first == trace else first
            for first, second in outside_edges
            if trace in (first, second)
        }

    for trace in outside_vertices:
        expected_degree = 0 if trace_is_edge[trace] else 2
        assert len(outside_neighbors(trace)) == expected_degree
        for endpoint in trace:
            internal_resolvers = {
                other
                for other in trace
                if other != endpoint
                and tuple(sorted((endpoint, other))) in INTERNAL_EDGES
            }
            external_resolvers = {
                other_trace
                for other_trace in outside_neighbors(trace)
                if endpoint in other_trace
            }
            assert len(internal_resolvers | external_resolvers) == 1

    # No outside edge gets two component-side common neighbors: distinct
    # two-subsets in a simple trace graph intersect in at most one point.
    assert all(len(set(first) & set(second)) == 1 for first, second in outside_edges)

    print("verified reduced q=16 selector countermodel")
    print("internal type: C6 + C26 (oppositely oriented)")
    print("outside traces: 224; trace-edges: 26")
    print(f"outside resolution edges: {len(outside_edges)}")


if __name__ == "__main__":
    main()
