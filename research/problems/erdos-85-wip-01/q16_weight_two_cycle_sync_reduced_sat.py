#!/usr/bin/env python3
"""Reduced q=16 countermodel to weight-two cycle synchronization.

This is deliberately not a full 256-vertex A-graph.  It realizes all exact
selector-pair laws visible from one weight-two defect component C: the
internal graph is 2-regular and C4-free, every point of C occurs in q-2
outside two-point traces, trace pairs do not repeat, and a trace pair cannot
already have an internal common neighbor.  Different internal cycles can
nevertheless have different trace/T orientations.
"""

from collections import deque
from itertools import combinations

import networkx as nx
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix
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

    # Realize the actual alternating eigenline, not only even cycle lengths.
    # Every two-point outside trace must contain one +1 and one -1 point.
    alternating_sign = {
        vertex: 1 if (vertex if vertex < 6 else vertex - 6) % 2 == 0 else -1
        for vertex in range(N)
    }
    for first, second in PAIRS:
        if alternating_sign[first] == alternating_sign[second]:
            solver.add(Not(selected[first, second]))

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
    assert all(alternating_sign[first] + alternating_sign[second] == 0
               for first, second in chosen)
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
    assert len(chosen & INTERNAL_EDGES) + len(outside_edges) == Q * (Q - 2)

    # Internal vertices themselves select the two distance-two neighbors on
    # their H-cycle.  The exact selector-complement identity therefore
    # reconstructs the induced defect block as the complement of F together
    # with those distance-two selector pairs.
    defect_edges = set(PAIRS) - chosen - distance_two_pairs
    defect_neighbors = {vertex: set() for vertex in range(N)}
    for first, second in defect_edges:
        defect_neighbors[first].add(second)
        defect_neighbors[second].add(first)
    assert all(len(defect_neighbors[vertex]) == Q - 1 for vertex in range(N))

    reached = {0}
    queue = deque([0])
    while queue:
        for neighbor in defect_neighbors[queue.popleft()]:
            if neighbor not in reached:
                reached.add(neighbor)
                queue.append(neighbor)
    assert reached == set(range(N))

    color: dict[int, int] = {}
    bipartite = True
    for root in range(N):
        if root in color:
            continue
        color[root] = 0
        queue = deque([root])
        while queue:
            vertex = queue.popleft()
            for neighbor in defect_neighbors[vertex]:
                if neighbor not in color:
                    color[neighbor] = 1 - color[vertex]
                    queue.append(neighbor)
                elif color[neighbor] == color[vertex]:
                    bipartite = False
    assert not bipartite
    defect_graph = nx.Graph()
    defect_graph.add_nodes_from(range(N))
    defect_graph.add_edges_from(defect_edges)
    assert nx.edge_connectivity(defect_graph) == Q - 1

    # Minimize a cut with both shores of size at least two.  Binary variables
    # choose the shore and one auxiliary variable per D-edge records crossing.
    ordered_defect_edges = sorted(defect_edges)
    variable_count = N + len(ordered_defect_edges)
    objective = np.r_[np.zeros(N), np.ones(len(ordered_defect_edges))]
    rows: list[int] = []
    columns: list[int] = []
    values: list[int] = []
    lower: list[float] = []
    upper: list[float] = []

    def add_linear_row(coefficients, lo, hi) -> None:
        row = len(lower)
        for column, value in coefficients:
            rows.append(row)
            columns.append(column)
            values.append(value)
        lower.append(lo)
        upper.append(hi)

    for index, (first, second) in enumerate(ordered_defect_edges):
        crossing = N + index
        add_linear_row([(crossing, 1), (first, -1), (second, 1)], 0, np.inf)
        add_linear_row([(crossing, 1), (first, 1), (second, -1)], 0, np.inf)
    add_linear_row([(vertex, 1) for vertex in range(N)], 2, N - 2)
    add_linear_row([(0, 1)], 0, 0)  # break shore/complement symmetry
    constraint_matrix = coo_matrix(
        (values, (rows, columns)), shape=(len(lower), variable_count)
    ).tocsr()
    cut_result = milp(
        objective,
        integrality=np.ones(variable_count),
        bounds=Bounds(np.zeros(variable_count), np.ones(variable_count)),
        constraints=LinearConstraint(constraint_matrix, lower, upper),
    )
    assert cut_result.success
    assert round(cut_result.fun) == 2 * Q - 4
    assert all(
        sum(alternating_sign[neighbor] for neighbor in defect_neighbors[vertex])
        == (Q - 5) * alternating_sign[vertex]
        for vertex in range(N)
    )

    print("verified reduced q=16 selector countermodel")
    print("internal type: C6 + C26 (oppositely oriented)")
    print("outside traces: 224; trace-edges: 26")
    print(f"outside resolution edges: {len(outside_edges)}")
    print("induced defect block: connected, nonbipartite, 15-regular, edge-connectivity 15")
    print("minimum nontrivial-shore defect cut: 28")
    print("alternating vector: cross-kernel and defect eigenvalue 11")


if __name__ == "__main__":
    main()
