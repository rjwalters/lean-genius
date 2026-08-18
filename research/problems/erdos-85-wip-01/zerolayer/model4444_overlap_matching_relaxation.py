#!/usr/bin/env python3
"""Global overlap matching relaxation for the corrected Stage-1 geometry.

This is a signal model, not a class certificate.  It keeps the 48 service
point-clique matchings, the 16 defect cycles, odd overlap degrees, the exact
264-edge ledger, and the certified localization of degree-one vertices to
their paired-component clique.  ``--fixed-sparse`` pins an explicit set of
six sparse vertices per omitted type solely to search quickly for a SAT
countermodel to this relaxation.
"""

import argparse
from itertools import combinations

import z3

from test_symbolic_hlift_service import WIT
from verify_stage1_color_action import graphs, ORPHANS, N, vid


parser = argparse.ArgumentParser()
parser.add_argument("--fixed-sparse", action="store_true")
parser.add_argument("--h-quotas", action="store_true")
parser.add_argument("--a-independent", action="store_true")
parser.add_argument("--c4-free", action="store_true")
parser.add_argument("--timeout-ms", type=int, default=120_000)
args = parser.parse_args()

paired = {0: 1, 1: 0, 2: 3, 3: 2}
solver = z3.Solver()
solver.set(timeout=args.timeout_ms)

# Every service edge belongs to its unique shared point clique.  Pair
# injectivity in WIT ensures no pair is generated from two components.
service_edges = []
service_incidence = [[] for _ in range(N)]
overlap_neighbors = [[] for _ in range(N)]
clique_edges = {}
for component in range(4):
    for point in range(12):
        clique = [
            vid(orphan, x)
            for orphan in ORPHANS if component in WIT[orphan]
            for x in range(12)
            if (x + WIT[orphan][component]) % 12 == point
        ]
        assert len(clique) == 12
        edges = []
        for index, left in enumerate(clique):
            for right in clique[index + 1:]:
                edge = z3.Bool(f"s_{component}_{point}_{left}_{right}")
                record = (edge, left, right, component)
                edges.append(record)
                service_edges.append(record)
                service_incidence[left].append((edge, component))
                service_incidence[right].append((edge, component))
                overlap_neighbors[left].append((edge, right))
                overlap_neighbors[right].append((edge, left))
        clique_edges[component, point] = edges
        for vertex in clique:
            solver.add(z3.PbLe([
                (edge, 1) for edge, left, right, _ in edges
                if vertex in (left, right)
            ], 1))

assert len(service_edges) == 48 * 66
assert len({frozenset((left, right)) for _, left, right, _ in service_edges}) \
       == len(service_edges)

defect_edges = []
defect_incidence = [[] for _ in range(N)]
for orphan in ORPHANS:
    for x in range(12):
        left, right = vid(orphan, x), vid(orphan, x + 1)
        edge = z3.Bool(f"d_{left}_{right}")
        defect_edges.append((edge, left, right))
        defect_incidence[left].append(edge)
        defect_incidence[right].append(edge)
        overlap_neighbors[left].append((edge, right))
        overlap_neighbors[right].append((edge, left))

edge_by_pair = {
    frozenset((left, right)): edge
    for edge, left, right, _ in service_edges
}
edge_by_pair.update({frozenset((left, right)): edge
                     for edge, left, right in defect_edges})
assert len(edge_by_pair) == len(service_edges) + len(defect_edges)

if args.h_quotas:
    for vertex in range(N):
        source_type = ORPHANS[vertex // 12][0]
        for target_type in range(4):
            solver.add(z3.PbLe([
                (edge, 1) for edge, other in overlap_neighbors[vertex]
                if ORPHANS[other // 12][0] == target_type
            ], 1 if target_type == paired[source_type] else 4))
        for component in range(4):
            bound = 4 if component == paired[source_type] else 3
            for color in range(3):
                solver.add(z3.PbLe([
                    (edge, 1) for edge, other in overlap_neighbors[vertex]
                    if component in WIT[ORPHANS[other // 12]] and
                    (other % 12 + WIT[ORPHANS[other // 12]][component]) % 3
                    == color
                ], bound))

if args.a_independent:
    a_pairs = graphs(WIT)
    for vertex in range(N):
        incidence = overlap_neighbors[vertex]
        for index, (left_edge, left) in enumerate(incidence):
            for right_edge, right in incidence[index + 1:]:
                if frozenset((left, right)) in a_pairs:
                    solver.add(z3.Or(z3.Not(left_edge),
                                     z3.Not(right_edge)))

if args.c4_free:
    a_neighbors = [set() for _ in range(N)]
    for pair in graphs(WIT):
        left, right = tuple(pair)
        a_neighbors[left].add(right)
        a_neighbors[right].add(left)
    c4_constraints = 0
    for left in range(N):
        for right in range(left + 1, N):
            for top, bottom in combinations(
                    sorted(a_neighbors[left] & a_neighbors[right]), 2):
                solver.add(z3.Or(
                    z3.Not(edge_by_pair[frozenset((left, top))]),
                    z3.Not(edge_by_pair[frozenset((top, right))]),
                    z3.Not(edge_by_pair[frozenset((right, bottom))]),
                    z3.Not(edge_by_pair[frozenset((bottom, left))])))
                c4_constraints += 1
    print("c4_constraints", c4_constraints)

fixed = ({vid((omitted_type, 0), x)
          for omitted_type in range(4) for x in range(6)}
         if args.fixed_sparse else None)
sparse = []
for vertex in range(N):
    degree = z3.Sum(
        [z3.If(edge, 1, 0) for edge, _ in service_incidence[vertex]] +
        [z3.If(edge, 1, 0) for edge in defect_incidence[vertex]])
    is_sparse = z3.Bool(f"sparse_{vertex}")
    sparse.append(is_sparse)
    solver.add(z3.Or(degree == 1, degree == 3, degree == 5),
               is_sparse == (degree == 1))
    if fixed is not None:
        # With exactly 24 degree-one vertices and 264 total edges, the ledger
        # forces every remaining vertex to have degree three.
        solver.add(degree == (1 if vertex in fixed else 3))

    omitted_type = ORPHANS[vertex // 12][0]
    solver.add(z3.Implies(is_sparse, z3.And(
        *[z3.Not(edge) for edge in defect_incidence[vertex]])))
    for edge, component in service_incidence[vertex]:
        if component != paired[omitted_type]:
            solver.add(z3.Implies(is_sparse, z3.Not(edge)))

# Test the strongest hoped-for consequence by forbidding sparse-sparse
# service edges.  Sparse defect edges were already forbidden above.
for edge, left, right, _ in service_edges:
    solver.add(z3.Implies(edge,
                          z3.Or(z3.Not(sparse[left]),
                                z3.Not(sparse[right]))))

if fixed is None:
    solver.add(z3.PbEq(
        [(edge, 1) for edge, _, _, _ in service_edges] +
        [(edge, 1) for edge, _, _ in defect_edges], 264))

if args.fixed_sparse:
    # One explicit six-per-type placement: copy zero, coordinates 0,...,5.
    for vertex in range(N):
        solver.add(sparse[vertex] if vertex in fixed else z3.Not(sparse[vertex]))
else:
    for omitted_type in range(4):
        solver.add(z3.PbGe([
            (sparse[vertex], 1) for vertex in range(N)
            if ORPHANS[vertex // 12][0] == omitted_type
        ], 6 if omitted_type == 0 else 0))

verdict = solver.check()
print(verdict)
if verdict == z3.sat:
    model = solver.model()
    sparse_counts = [sum(
        z3.is_true(model.eval(sparse[vertex])) for vertex in range(N)
        if ORPHANS[vertex // 12][0] == omitted_type)
        for omitted_type in range(4)]
    service_count = sum(z3.is_true(model.eval(edge))
                        for edge, _, _, _ in service_edges)
    defect_count = sum(z3.is_true(model.eval(edge))
                       for edge, _, _ in defect_edges)
    print("sparse_by_type", sparse_counts)
    print("service_edges", service_count, "defect_edges", defect_count)
elif verdict == z3.unknown:
    print("reason", solver.reason_unknown())
