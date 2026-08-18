#!/usr/bin/env python3
"""Fixed-WIT linear commuting relaxation for the paired Stage-1 H-lift.

This is a research signal only, never a class-level certificate.  It fixes
the validated baseline Stage-1 phases and asks for a symmetric 0/1 matrix H
with the paired quotient, exact cube-root color balances, and HA=AH.  The
optional mixed-moment flag adds the service-independent overlap ledgers.
Quadratic common-neighbor equations are deliberately absent.
"""

import argparse
from itertools import combinations

from ortools.sat.python import cp_model

from test_symbolic_hlift_service import WIT
from verify_stage1_color_action import graphs

COMPS = range(4)
ORPHANS = [(omit, copy) for omit in COMPS for copy in range(4)]
N = 192
PAIRED = {0: 1, 1: 0, 2: 3, 3: 2}


def build(include_moments):
    service_graph = graphs(WIT)
    service_neighbors = [set() for _ in range(N)]
    for pair in service_graph:
        left, right = pair
        service_neighbors[left].add(right)
        service_neighbors[right].add(left)

    model = cp_model.CpModel()
    edges = {(left, right): model.NewBoolVar(f"e{left}_{right}")
             for left, right in combinations(range(N), 2)}

    def edge(left, right):
        if left == right:
            return 0
        return edges[min(left, right), max(left, right)]

    for vertex in range(N):
        source = ORPHANS[vertex // 12][0]
        for target in COMPS:
            candidates = [edge(vertex, other) for other in range(N)
                          if other != vertex and
                          ORPHANS[other // 12][0] == target]
            model.Add(sum(candidates) ==
                      (1 if target == PAIRED[source] else 4))
        for component in COMPS:
            expected = 4 if component == PAIRED[source] else 3
            for residue in range(3):
                candidates = []
                for other in range(N):
                    if other == vertex:
                        continue
                    orphan = ORPHANS[other // 12]
                    if component in WIT[orphan] and \
                            ((other % 12) + WIT[orphan][component]) % 3 == residue:
                        candidates.append(edge(vertex, other))
                model.Add(sum(candidates) == expected)

    # Entrywise HA=AH.  Symmetry lets us keep only the upper triangle.
    for left in range(N):
        for right in range(left, N):
            model.Add(sum(edge(left, x) for x in service_neighbors[right]
                          if x != left) ==
                      sum(edge(x, right) for x in service_neighbors[left]
                          if x != right))

    if include_moments:
        overlap = [edge(left, right)
                   for left, right in combinations(range(N), 2)
                   if frozenset((left, right)) in service_graph]
        model.Add(sum(overlap) == 264)
        weighted = []
        for left, right in combinations(range(N), 2):
            weight = len(service_neighbors[left] & service_neighbors[right])
            weighted.append(weight * edge(left, right))
        model.Add(sum(weighted) == 7848)
        for vertex in range(N):
            local = sum(edge(vertex, other)
                        for other in service_neighbors[vertex])
            model.AddAllowedAssignments([local],
                                        [(value,) for value in range(1, 14, 2)])
    return model


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--time", type=float, default=60)
    parser.add_argument("--workers", type=int, default=8)
    parser.add_argument("--mixed-moments", action="store_true")
    parser.add_argument("--log", action="store_true")
    args = parser.parse_args()
    model = build(args.mixed_moments)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = args.time
    solver.parameters.num_search_workers = args.workers
    solver.parameters.log_search_progress = args.log
    status = solver.Solve(model)
    print("COMMUTING RELAXATION SIGNAL", solver.StatusName(status),
          {"mixed_moments": args.mixed_moments,
           "wall": solver.WallTime(), "branches": solver.NumBranches(),
           "conflicts": solver.NumConflicts()})
    # An UNSAT signal is baseline-WIT-only until independently certified.
    if status == cp_model.INFEASIBLE:
        print("SIGNAL UNSAT: REQUIRES INDEPENDENT CERTIFICATE; NOT CLASS-LEVEL")


if __name__ == "__main__":
    main()
