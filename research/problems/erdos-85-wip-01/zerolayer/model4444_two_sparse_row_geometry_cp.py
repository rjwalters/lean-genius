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
parser.add_argument("--left-overlap", type=int)
parser.add_argument("--right-overlap", type=int)
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
if args.left_overlap is not None:
    if args.left_overlap not in A_neighbors[left_center]:
        raise ValueError("--left-overlap is not an A-neighbor of left center")
    model.Add(X[args.left_overlap] == 1)
if args.right_overlap is not None:
    if args.right_overlap not in A_neighbors[right_center]:
        raise ValueError("--right-overlap is not an A-neighbor of right center")
    model.Add(Z[args.right_overlap] == 1)
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
    for component in range(4):
        for color in range(3):
            model.Add(sum(
                row[target] for target in range(N)
                if component in WIT[ORPHANS[target // 12]] and
                (target % 12 + WIT[ORPHANS[target // 12]][component]) % 3
                == color
            ) == (116 if component == 1 else 113))
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

# The exact signed A-energy of the mixed-row difference, counted once per
# unordered A-edge.
difference = []
for target in range(N):
    value = model.NewIntVar(-9, 9, f"difference_{target}")
    model.Add(value == left_row[target] - right_row[target])
    difference.append(value)
energy_terms = []
for pair in A_pairs:
    left, right = tuple(pair)
    product = model.NewIntVar(-81, 81, f"energy_{left}_{right}")
    model.AddMultiplicationEquality(
        product, [difference[left], difference[right]])
    energy_terms.append(product)
model.Add(sum(energy_terms) ==
          [-591, -65, -99, -230, -231, -87][args.distance - 1])

# One further exact spectral moment: δ^T A^2 δ = ||Aδ||^2.  Computing Aδ
# first needs only 192 additional square constraints, rather than dense
# pairwise products weighted by A^2.
a_difference = []
a_difference_squares = []
for target in range(N):
    # Cauchy from ||δ||² ≤ 516 and 35 summands gives |(Aδ)_t| ≤ 134.
    value = model.NewIntVar(-134, 134, f"A_difference_{target}")
    model.Add(value == sum(difference[source]
                           for source in A_neighbors[target]))
    square = model.NewIntVar(0, 17956, f"A_difference_sq_{target}")
    model.AddMultiplicationEquality(square, [value, value])
    a_difference.append(value)
    a_difference_squares.append(square)
model.Add(sum(a_difference_squares) ==
          [14282, 10440, 13654, 11160, 11186, 13104][args.distance - 1])


def next_even_spectral_moment(previous, bound, norm_values, label):
    transformed, squares = [], []
    for target in range(N):
        value = model.NewIntVar(-bound, bound, f"{label}_{target}")
        model.Add(value == sum(previous[source]
                               for source in A_neighbors[target]))
        square = model.NewIntVar(0, bound * bound,
                                 f"{label}_sq_{target}")
        model.AddMultiplicationEquality(square, [value, value])
        transformed.append(value)
        squares.append(square)
    model.Add(sum(squares) == norm_values[args.distance - 1])
    return transformed


aa_difference = next_even_spectral_moment(
    a_difference, 707,
    [578818, 681420, 851346, 676776, 676450, 804276], "AA_difference")
next_even_spectral_moment(
    aa_difference, 4500,
    [33790878, 58358040, 70899854, 59501760, 58858110, 67005144],
    "AAA_difference")

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
