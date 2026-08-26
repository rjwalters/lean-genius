#!/usr/bin/env python3
"""Local q=5 falsifier for D-edge exclusive-contact pairing.

The q=4 full-model census found that, for a zero-common-neighbor pair u,v,
the remote vertices contacting only N(u) and those contacting only N(v) are
perfectly matched by ambient edges.  This script asks whether that follows
from the constraints visible inside the two rooted stars.

We fix disjoint five-vertex stars U=N(u), V=N(v), and the thirteen remaining
vertices R.  We impose C4-freeness, the forced adjacencies at u and v, exact
ambient degree five on R, and degree at most five on U and V.  We then demand
different cardinalities for the U-only and V-only remote-contact classes.
A SAT witness is only a locally completable obstruction, not a 5-regular
order-25 graph: unused degree at U and V is deliberately allowed.
"""

from __future__ import annotations

import itertools

from z3 import And, Bool, If, Not, Or, Solver, Sum, is_true, sat


Q = 5
U_ROOT, V_ROOT = 0, 1
U = tuple(range(2, 2 + Q))
V = tuple(range(2 + Q, 2 + 2 * Q))
R = tuple(range(2 + 2 * Q, Q * Q))
N = Q * Q


def main() -> None:
    solver = Solver()
    solver.set(timeout=120_000, random_seed=850076)
    variables = {
        (left, right): Bool(f"a_{left}_{right}")
        for left in range(N)
        for right in range(left + 1, N)
    }

    def edge(left: int, right: int):
        if left == right:
            return False
        return variables[tuple(sorted((left, right)))]

    for vertex in range(2, N):
        solver.add(edge(U_ROOT, vertex) == (vertex in U))
        solver.add(edge(V_ROOT, vertex) == (vertex in V))
    solver.add(Not(edge(U_ROOT, V_ROOT)))

    for vertex in R:
        solver.add(Sum([If(edge(vertex, other), 1, 0) for other in range(N) if other != vertex]) == Q)
    for vertex in U + V:
        solver.add(Sum([If(edge(vertex, other), 1, 0) for other in range(N) if other != vertex]) <= Q)

    for left, right in itertools.combinations(range(N), 2):
        solver.add(
            Sum(
                [
                    If(And(edge(left, middle), edge(right, middle)), 1, 0)
                    for middle in range(N)
                    if middle != left and middle != right
                ]
            )
            <= 1
        )

    u_contact = {r: Or([edge(r, vertex) for vertex in U]) for r in R}
    v_contact = {r: Or([edge(r, vertex) for vertex in V]) for r in R}
    u_only = {r: And(u_contact[r], Not(v_contact[r])) for r in R}
    v_only = {r: And(v_contact[r], Not(u_contact[r])) for r in R}
    u_only_count = Sum([If(u_only[r], 1, 0) for r in R])
    v_only_count = Sum([If(v_only[r], 1, 0) for r in R])
    solver.add(u_only_count != v_only_count)

    result = solver.check()
    print(f"result={result}")
    if result != sat:
        raise SystemExit(2)
    model = solver.model()
    edges = [pair for pair, variable in variables.items() if is_true(model.eval(variable))]
    u_only_vertices = [r for r in R if is_true(model.eval(u_only[r]))]
    v_only_vertices = [r for r in R if is_true(model.eval(v_only[r]))]
    degrees = {
        vertex: sum(is_true(model.eval(edge(vertex, other))) for other in range(N) if other != vertex)
        for vertex in range(N)
    }
    print(f"u_only={u_only_vertices}")
    print(f"v_only={v_only_vertices}")
    print(f"degrees={degrees}")
    print(f"edges={edges}")
    print("exclusive_contact_cardinality_equality_from_local_constraints=false")


if __name__ == "__main__":
    main()
