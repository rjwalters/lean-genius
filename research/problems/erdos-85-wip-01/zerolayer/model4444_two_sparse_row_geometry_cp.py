#!/usr/bin/env python3
"""Fixed-WIT CP signal for exact two-sparse mixed-row geometry.

Unlike the symbolic CNF probe, this fixes the validated baseline Stage-1
phase witness and uses native integer products for B-row norms and dots.
SAT is only a countermodel to this necessary-condition relaxation; UNSAT is
only a fixed-WIT signal until lifted to the symbolic class and certified.
"""

import argparse

from ortools.sat.python import cp_model

from test_symbolic_hlift_service import WIT
from verify_stage1_color_action import graphs, ORPHANS, N, vid


parser = argparse.ArgumentParser()
parser.add_argument("distance", type=int, choices=range(1, 7))
parser.add_argument("--time", type=float, default=300)
parser.add_argument("--workers", type=int, default=8)
args = parser.parse_args()

A_pairs = graphs(WIT)
A_neighbors = [set() for _ in range(N)]
for pair in A_pairs:
    left, right = tuple(pair)
    A_neighbors[left].add(right)
    A_neighbors[right].add(left)
assert all(len(row) == 35 for row in A_neighbors)

model = cp_model.CpModel()
X = [model.NewBoolVar(f"X_{v}") for v in range(N)]
Z = [model.NewBoolVar(f"Z_{v}") for v in range(N)]
left_center = vid((0, 0), 0)
right_center = vid((0, 0), args.distance)


def neighborhood_constraints(selected, center):
    model.Add(sum(selected) == 13)
    model.Add(selected[center] == 0)
    for pair in A_pairs:
        left, right = tuple(pair)
        model.Add(selected[left] + selected[right] <= 1)
    model.Add(sum(selected[v] for v in A_neighbors[center]) == 1)

    center_color = center % 3
    for vertex in A_neighbors[center]:
        orphan = ORPHANS[vertex // 12]
        if 1 not in WIT[orphan] or \
                (vertex % 12 + WIT[orphan][1]) % 3 != center_color:
            model.Add(selected[vertex] == 0)
    for color in range(3):
        model.Add(sum(
            selected[vertex] for vertex in range(N)
            if 1 in WIT[ORPHANS[vertex // 12]] and
            (vertex % 12 + WIT[ORPHANS[vertex // 12]][1]) % 3 == color
        ) == 4)


neighborhood_constraints(X, left_center)
neighborhood_constraints(Z, right_center)
model.Add(X[right_center] == Z[left_center])

common = []
for vertex in range(N):
    both = model.NewBoolVar(f"common_{vertex}")
    model.AddMultiplicationEquality(both, [X[vertex], Z[vertex]])
    common.append(both)
model.Add(sum(common) == (0 if args.distance == 1 else 1))

cross = []
for left, neighbors in enumerate(A_neighbors):
    for right in neighbors:
        both = model.NewBoolVar(f"cross_{left}_{right}")
        model.AddMultiplicationEquality(both, [X[left], Z[right]])
        cross.append(both)
model.Add(sum(cross) == [44, 31, 29, 32, 32, 29][args.distance - 1])


def mixed_row(selected, label):
    row, squares = [], []
    for target in range(N):
        value = model.NewIntVar(0, 9, f"B_{label}_{target}")
        model.Add(value == sum(selected[source]
                               for source in A_neighbors[target]))
        square = model.NewIntVar(0, 81, f"B2_{label}_{target}")
        model.AddMultiplicationEquality(square, [value, value])
        row.append(value)
        squares.append(square)
    model.Add(sum(row) == 455)
    model.Add(sum(squares) == 1255)
    for target_type in range(4):
        model.Add(sum(row[target] for target in range(N)
                      if ORPHANS[target // 12][0] == target_type)
                  == (107 if target_type == 1 else 116))
    return row


left_row = mixed_row(X, "x")
right_row = mixed_row(Z, "z")
products = []
for target in range(N):
    product = model.NewIntVar(0, 81, f"dot_{target}")
    model.AddMultiplicationEquality(
        product, [left_row[target], right_row[target]])
    products.append(product)
model.Add(sum(products) ==
          [997, 1093, 1068, 1081, 1081, 1069][args.distance - 1])

solver = cp_model.CpSolver()
solver.parameters.max_time_in_seconds = args.time
solver.parameters.num_search_workers = args.workers
status = solver.Solve(model)
print("status", solver.StatusName(status))
print("wall", solver.WallTime(), "branches", solver.NumBranches(),
      "conflicts", solver.NumConflicts())
if status in (cp_model.FEASIBLE, cp_model.OPTIMAL):
    print("X", [v for v in range(N) if solver.Value(X[v])])
    print("Z", [v for v in range(N) if solver.Value(Z[v])])
