#!/usr/bin/env python3
"""Exhaust the q=4 size-two-component trace dichotomy.

Fix the two second-order-defect components to have eight vertices each.
The component quotient laws make both induced A-graphs 2-regular and the
cross graph 2-regular.  C4-freeness leaves only C8 and C5 + C3 as the
possible induced types.  For each of the four ordered type pairs, this
script asks Z3 for a graph in which strictly between zero and eight outside
vertices have an A-edge as their two-neighbor trace in the first component.
"""

from itertools import combinations

from z3 import And, Bool, If, Or, Solver, Sum, unsat


N = 16
LEFT = tuple(range(8))
RIGHT = tuple(range(8, 16))


def cycle(vertices: tuple[int, ...]) -> set[tuple[int, int]]:
    return {
        tuple(sorted((vertices[index], vertices[(index + 1) % len(vertices)])))
        for index in range(len(vertices))
    }


LEFT_TYPES = {
    "C8": cycle(LEFT),
    "C5+C3": cycle(LEFT[:5]) | cycle(LEFT[5:]),
}
RIGHT_TYPES = {
    "C8": cycle(RIGHT),
    "C5+C3": cycle(RIGHT[:5]) | cycle(RIGHT[5:]),
}


def boolean_sum(expressions):
    return Sum([If(expression, 1, 0) for expression in expressions])


def intermediate_trace_instance(
    left_edges: set[tuple[int, int]], right_edges: set[tuple[int, int]]
) -> Solver:
    cross = {
        (left, right): Bool(f"cross_{left}_{right}")
        for left in LEFT
        for right in RIGHT
    }

    def adjacent(first: int, second: int):
        if first == second:
            return False
        edge = tuple(sorted((first, second)))
        if first in LEFT and second in LEFT:
            return edge in left_edges
        if first in RIGHT and second in RIGHT:
            return edge in right_edges
        if first in RIGHT:
            first, second = second, first
        return cross[first, second]

    solver = Solver()

    # Every vertex has two neighbors in its own defect component and two in
    # the other one.  The internal degrees are already fixed by the cycles.
    for vertex in LEFT:
        solver.add(boolean_sum(adjacent(vertex, other) for other in RIGHT) == 2)
    for vertex in RIGHT:
        solver.add(boolean_sum(adjacent(vertex, other) for other in LEFT) == 2)

    common = {}
    for first, second in combinations(range(N), 2):
        common[first, second] = boolean_sum(
            And(adjacent(first, witness), adjacent(second, witness))
            for witness in range(N)
            if witness not in (first, second)
        )
        # This is precisely the C4-free pair-codegree condition.
        solver.add(common[first, second] <= 1)
        # Distinct defect components have no D-edge, hence codegree one.
        if (first in LEFT) != (second in LEFT):
            solver.add(common[first, second] == 1)

    # Each fixed block is an actual q=4 defect component: internal D-degree
    # three.  Together with the absence of cross D-edges this is the exact
    # second-order-defect degree condition.
    for block in (LEFT, RIGHT):
        for vertex in block:
            solver.add(
                boolean_sum(
                    common[tuple(sorted((vertex, other)))] == 0
                    for other in block
                    if other != vertex
                )
                == 3
            )

    trace_is_edge = [
        Or(
            [
                And(
                    adjacent(apex, first),
                    adjacent(apex, second),
                    adjacent(first, second),
                )
                for first, second in combinations(LEFT, 2)
            ]
        )
        for apex in RIGHT
    ]
    trace_edge_count = boolean_sum(trace_is_edge)
    solver.add(0 < trace_edge_count, trace_edge_count < 8)
    return solver


def main() -> None:
    for left_name, left_edges in LEFT_TYPES.items():
        for right_name, right_edges in RIGHT_TYPES.items():
            result = intermediate_trace_instance(left_edges, right_edges).check()
            assert result == unsat, (left_name, right_name, result)
            print(f"verified UNSAT: {left_name} versus {right_name}")
    print("verified: the q=4 trace-edge count is always 0 or 8")


if __name__ == "__main__":
    main()
