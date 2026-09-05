#!/usr/bin/env python3
"""Bounded q=8 [5,3] exterior-carrier relaxation.

The variables are the full symmetric ambient adjacency matrix, split into
40- and 24-vertex shores.  We retain exact component degrees, C4-freeness,
all cross pairs having one common neighbor, and a displayed defect triangle
on the large shore.  Connectivity of the two induced defect graphs is
deliberately omitted in this first probe, so UNSAT is useful while SAT is
only a relaxation countermodel.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from itertools import combinations

import z3


Q = 8
LARGE = 40
ORDER = 64
SMALL = ORDER - LARGE


def edge(a: list[list[z3.BoolRef]], u: int, v: int) -> z3.BoolRef:
    if u == v:
        return z3.BoolVal(False)
    return a[min(u, v)][max(u, v)]


def build(timeout_ms: int, triangle_ambient_edges: int
          ) -> tuple[z3.Solver, list[list[z3.BoolRef]]]:
    solver = z3.Solver()
    solver.set(timeout=timeout_ms)
    a = [[z3.Bool(f"a_{u}_{v}") for v in range(ORDER)] for u in range(ORDER)]

    # The upper triangle is the only live part of a.  Component-neighbor
    # cardinalities imply internal/exterior degrees (5,3) and (3,5).
    for u in range(ORDER):
        own = range(0, LARGE) if u < LARGE else range(LARGE, ORDER)
        other = range(LARGE, ORDER) if u < LARGE else range(0, LARGE)
        own_degree = 5 if u < LARGE else 3
        other_degree = 3 if u < LARGE else 5
        solver.add(z3.PbEq([(edge(a, u, v), 1) for v in own if v != u], own_degree))
        solver.add(z3.PbEq([(edge(a, u, v), 1) for v in other], other_degree))

    common: dict[tuple[int, int], list[z3.BoolRef]] = {}
    for u in range(ORDER):
        for v in range(u + 1, ORDER):
            terms = [z3.And(edge(a, u, w), edge(a, v, w))
                     for w in range(ORDER) if w != u and w != v]
            common[u, v] = terms
            # Ambient C4-freeness.
            solver.add(z3.PbLe([(term, 1) for term in terms], 1))
            # Distinct defect components have no cross defect edge.
            if (u < LARGE) != (v < LARGE):
                solver.add(z3.PbEq([(term, 1) for term in terms], 1))

    # Name the internal defect relation explicitly.  Seven-regularity follows
    # from the degree/C4 equations, but exposing it avoids asking the solver
    # to rediscover that global counting argument.
    defect: dict[tuple[int, int], z3.BoolRef] = {}
    for shore in (range(0, LARGE), range(LARGE, ORDER)):
        for u, v in combinations(shore, 2):
            d = z3.Bool(f"d_{u}_{v}")
            defect[u, v] = d
            solver.add(d == z3.Not(z3.Or(common[u, v])))
        for u in shore:
            solver.add(z3.PbEq([
                (defect[min(u, v), max(u, v)], 1)
                for v in shore if v != u
            ], Q - 1))

    # The large induced defect graph contains the triangle 0-1-2.
    for u, v in [(0, 1), (1, 2), (0, 2)]:
        solver.add(z3.PbEq([(term, 1) for term in common[u, v]], 0))

    # Safe orbit fixing.  Ambient edges on a defect triangle form a matching:
    # two incident ambient edges would make their opposite endpoints share
    # the triangle vertex as a common neighbor.  Up to triangle symmetry the
    # only cases are zero edges or the single edge 0--1.  The three ambient
    # neighborhoods are pairwise disjoint, so permutations of all remaining
    # labels in each shore put them in the canonical sets below.
    assert triangle_ambient_edges in (0, 1)
    triangle_edges = {(0, 1)} if triangle_ambient_edges == 1 else set()
    for u, v in [(0, 1), (0, 2), (1, 2)]:
        solver.add(edge(a, u, v) == ((u, v) in triangle_edges))
    if triangle_ambient_edges == 0:
        internal = [set(range(3, 8)), set(range(8, 13)), set(range(13, 18))]
    else:
        internal = [{1, 3, 4, 5, 6}, {0, 7, 8, 9, 10}, set(range(11, 16))]
    external = [set(range(40, 43)), set(range(43, 46)), set(range(46, 49))]
    for u in range(3):
        for v in range(LARGE):
            if u != v:
                solver.add(edge(a, u, v) == (v in internal[u]))
        for v in range(LARGE, ORDER):
            solver.add(edge(a, u, v) == (v in external[u]))

    # Entrywise D_C B=B D_F: every point in one carrier part has at least one
    # defect neighbor in each other part.  These clauses are consequences of
    # the matrix equations, retained explicitly as propagation lemmas.
    for i in range(3):
        for f in external[i]:
            for j in range(3):
                if i != j:
                    solver.add(z3.Or([
                        defect[min(f, g), max(f, g)] for g in external[j]
                    ]))
    return solver, a


def extract(model: z3.ModelRef, a: list[list[z3.BoolRef]]) -> list[list[int]]:
    return [[v for v in range(ORDER) if u != v and
             z3.is_true(model.eval(edge(a, u, v), model_completion=True))]
            for u in range(ORDER)]


def verify(neighbors: list[list[int]]) -> dict[str, object]:
    sets = [set(row) for row in neighbors]
    assert all(u not in sets[u] for u in range(ORDER))
    assert all((v in sets[u]) == (u in sets[v])
               for u in range(ORDER) for v in range(ORDER))
    assert all(len(sets[u] & set(range(LARGE))) == (5 if u < LARGE else 5)
               for u in range(ORDER))
    assert all(len(sets[u] & set(range(LARGE, ORDER))) == (3 if u < LARGE else 3)
               for u in range(ORDER))
    common = {(u, v): len(sets[u] & sets[v])
              for u in range(ORDER) for v in range(u + 1, ORDER)}
    assert max(common.values()) <= 1
    assert all(common[u, v] == 1
               for u in range(LARGE) for v in range(LARGE, ORDER))
    assert all(common[pair] == 0 for pair in [(0, 1), (1, 2), (0, 2)])

    # Named odd-cycle carrier in the small shore.
    carrier = [sum(1 for u in (0, 1, 2) if f in sets[u]) % 2
               for f in range(LARGE, ORDER)]
    assert sum(carrier) % 2 == 1  # exterior weight n=3
    payload = json.dumps(neighbors, separators=(",", ":")).encode()
    return {
        "carrier_support": [LARGE + i for i, bit in enumerate(carrier) if bit],
        "carrier_weight": sum(carrier),
        "model_sha256": hashlib.sha256(payload).hexdigest(),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout-seconds", type=int, default=60)
    parser.add_argument("--triangle-ambient-edges", type=int,
                        choices=(0, 1), required=True)
    parser.add_argument("--write-model")
    args = parser.parse_args()
    solver, adjacency = build(args.timeout_seconds * 1000,
                              args.triangle_ambient_edges)
    result = solver.check()
    report: dict[str, object] = {
        "interface": "q8-[5,3]-cross-exact-c4-defect-triangle-relaxation",
        "result": str(result),
        "timeout_seconds": args.timeout_seconds,
        "triangle_ambient_edges": args.triangle_ambient_edges,
    }
    if result == z3.sat:
        neighbors = extract(solver.model(), adjacency)
        report.update(verify(neighbors))
        if args.write_model:
            with open(args.write_model, "x", encoding="utf-8") as stream:
                json.dump(neighbors, stream, separators=(",", ":"))
                stream.write("\n")
    elif result == z3.unknown:
        report["reason_unknown"] = solver.reason_unknown()
    print(json.dumps(report, sort_keys=True))


if __name__ == "__main__":
    main()
