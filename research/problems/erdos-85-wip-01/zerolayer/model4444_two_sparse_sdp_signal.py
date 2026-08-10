#!/usr/bin/env python3
"""Fixed-WIT Shor SDP signal for two sparse same-block centers.

This is a numerical relaxation only.  The 0/1 neighborhood vectors X,Z are
lifted into one PSD moment matrix with Boolean diagonal identities.  All
known linear neighborhood laws and quadratic row/spectral moments become
linear constraints on that lift.  Numerical infeasibility is not a proof;
it must be converted to an exact rational certificate before use.
"""

import argparse
import time

import cvxpy as cp
import numpy as np

from test_symbolic_hlift_service import WIT
from verify_stage1_color_action import graphs, ORPHANS, N, vid


parser = argparse.ArgumentParser()
parser.add_argument("distance", type=int, choices=range(1, 7))
parser.add_argument("--max-iters", type=int, default=50_000)
parser.add_argument("--eps", type=float, default=1e-5)
parser.add_argument("--solver", choices=("SCS", "CLARABEL"), default="SCS")
parser.add_argument("--rlt", action="store_true")
parser.add_argument("--moment-depth", type=int, choices=range(7), default=6)
parser.add_argument("--lp-cuts", type=int, default=0,
                    help="replace PSD by this many integer-vector cuts")
parser.add_argument("--cut-support", type=int, default=48)
parser.add_argument("--lp-time", type=float, default=300)
parser.add_argument("--lp-solver", choices=("simplex", "ipm"), default="ipm")
args = parser.parse_args()

A = np.zeros((N, N), dtype=float)
A_pairs = graphs(WIT)
neighbors = [set() for _ in range(N)]
for pair in A_pairs:
    left, right = tuple(pair)
    A[left, right] = A[right, left] = 1
    neighbors[left].add(right)
    neighbors[right].add(left)

# Indices in the lifted vector (1, X, Z).
xi = np.arange(1, N + 1)
zi = np.arange(N + 1, 2 * N + 1)
Y = cp.Variable((2 * N + 1, 2 * N + 1), symmetric=True)
x, z = Y[0, xi], Y[0, zi]
XX = Y[np.ix_(xi, xi)]
XZ = Y[np.ix_(xi, zi)]
ZX = Y[np.ix_(zi, xi)]
ZZ = Y[np.ix_(zi, zi)]
W = XX - XZ - ZX + ZZ

constraints = [Y[0, 0] == 1,
               cp.diag(XX) == x, cp.diag(ZZ) == z,
               x >= 0, x <= 1, z >= 0, z <= 1,
               cp.sum(x) == 13, cp.sum(z) == 13]
if args.lp_cuts == 0:
    constraints.insert(0, Y >> 0)
elif not args.rlt:
    raise ValueError("--lp-cuts requires --rlt to bound the lifted entries")

if args.rlt:
    # First-level reformulation-linearization constraints for Boolean
    # products.  These are exact for rank-one 0/1 lifts and materially
    # stronger than PSD plus Boolean diagonals alone.
    constraints += [
        XX >= 0, XX <= cp.reshape(x, (N, 1), order="C"),
        XX <= cp.reshape(x, (1, N), order="C"),
        XX >= cp.reshape(x, (N, 1), order="C") +
        cp.reshape(x, (1, N), order="C") - 1,
        ZZ >= 0, ZZ <= cp.reshape(z, (N, 1), order="C"),
        ZZ <= cp.reshape(z, (1, N), order="C"),
        ZZ >= cp.reshape(z, (N, 1), order="C") +
        cp.reshape(z, (1, N), order="C") - 1,
        XZ >= 0, XZ <= cp.reshape(x, (N, 1), order="C"),
        XZ <= cp.reshape(z, (1, N), order="C"),
        XZ >= cp.reshape(x, (N, 1), order="C") +
        cp.reshape(z, (1, N), order="C") - 1,
        cp.sum(XX, axis=1) == 13 * x,
        cp.sum(ZZ, axis=1) == 13 * z,
        cp.sum(XZ, axis=1) == 13 * x,
        cp.sum(XZ, axis=0) == 13 * z,
    ]
    for pair in A_pairs:
        left, right = tuple(pair)
        constraints += [XX[left, right] == 0, ZZ[left, right] == 0]

left_center = vid((0, 0), 0)
right_center = vid((0, 0), args.distance)


def neighborhood_constraints(selected, center):
    result = [selected[center] == 0]
    for pair in A_pairs:
        left, right = tuple(pair)
        result.append(selected[left] + selected[right] <= 1)
    result.append(cp.sum(selected[list(neighbors[center])]) == 1)

    source_type = ORPHANS[center // 12][0]
    paired = {0: 1, 1: 0, 2: 3, 3: 2}[source_type]
    center_color = center % 3
    for vertex in neighbors[center]:
        orphan = ORPHANS[vertex // 12]
        if 1 not in WIT[orphan] or \
                (vertex % 12 + WIT[orphan][1]) % 3 != center_color:
            result.append(selected[vertex] == 0)
    for target_type in range(4):
        fiber = [v for v in range(N)
                 if ORPHANS[v // 12][0] == target_type]
        result.append(cp.sum(selected[fiber]) ==
                      (1 if target_type == paired else 4))
    for component in range(4):
        for color in range(3):
            fiber = [
                v for v in range(N)
                if component in WIT[ORPHANS[v // 12]] and
                (v % 12 + WIT[ORPHANS[v // 12]][component]) % 3 == color
            ]
            result.append(cp.sum(selected[fiber]) ==
                          (4 if component == paired else 3))
    # Every reconstructed B entry is at most nine.
    result.extend(cp.sum(selected[list(neighbors[target])]) <= 9
                  for target in range(N))
    return result


constraints += neighborhood_constraints(x, left_center)
constraints += neighborhood_constraints(z, right_center)
constraints.append(x[right_center] == z[left_center])

# H^2 and BH support masses, expressed through the X-Z cross block.
constraints.append(cp.trace(XZ) == (0 if args.distance == 1 else 1))
constraints.append(cp.sum(cp.multiply(A, XZ)) ==
                   [44, 31, 29, 32, 32, 29][args.distance - 1])

A2 = A @ A
constraints += [cp.sum(cp.multiply(A2, XX)) == 1255,
                cp.sum(cp.multiply(A2, ZZ)) == 1255,
                cp.sum(cp.multiply(A2, XZ)) ==
                [997, 1093, 1068, 1081, 1081, 1069][args.distance - 1]]

# B-row type and color masses are linear in the neighborhood vectors.
for selected in (x, z):
    mixed_row = A @ selected
    for target_type in range(4):
        fiber = [v for v in range(N)
                 if ORPHANS[v // 12][0] == target_type]
        constraints.append(cp.sum(mixed_row[fiber]) ==
                           (107 if target_type == 1 else 116))
    for component in range(4):
        for color in range(3):
            fiber = [
                v for v in range(N)
                if component in WIT[ORPHANS[v // 12]] and
                (v % 12 + WIT[ORPHANS[v // 12]][component]) % 3 == color
            ]
            constraints.append(cp.sum(mixed_row[fiber]) ==
                               (116 if component == 1 else 113))

moment_rows = [
    [516, -1182, 14282, 7610, 578818, 2530930, 33790878],
    [324, -130, 10440, 52430, 681420, 5734298, 58358040],
    [374, -198, 13654, 53786, 851346, 6463858, 70899854],
    [348, -460, 11160, 37832, 676776, 5291984, 59501760],
    [348, -462, 11186, 36986, 676450, 5185138, 58858110],
    [372, -174, 13104, 53910, 804276, 6240618, 67005144],
]
power = A2.copy()
for moment in moment_rows[args.distance - 1][:args.moment_depth + 1]:
    # Scaling improves SCS conditioning while preserving the equality.
    scale = max(1.0, abs(float(moment)))
    constraints.append(cp.sum(cp.multiply(power / scale, W)) ==
                       moment / scale)
    power = power @ A

problem = None
value = None
integer_cuts = []
if args.lp_cuts:
    for iteration in range(args.lp_cuts + 1):
        problem = cp.Problem(cp.Minimize(0), constraints)
        compiled_at = time.perf_counter()
        data, _, _ = problem.get_problem_data("HIGHS")
        compile_seconds = time.perf_counter() - compiled_at
        matrix = data.get("A")
        print("lp_compiled", iteration, "seconds", compile_seconds,
              "variables", len(data.get("c", [])),
              "rows", None if matrix is None else matrix.shape[0],
              "nonzeros", None if matrix is None else matrix.nnz,
              flush=True)
        value = problem.solve(solver="HIGHS", verbose=False,
                              highs_options={"time_limit": args.lp_time,
                                             "solver": args.lp_solver})
        print("lp_iteration", iteration, "status", problem.status, flush=True)
        if problem.status not in (cp.OPTIMAL, cp.OPTIMAL_INACCURATE) or \
                iteration == args.lp_cuts:
            break
        symmetric = (Y.value + Y.value.T) / 2
        eigenvalues, eigenvectors = np.linalg.eigh(symmetric)
        print("lp_min_eigenvalue", float(eigenvalues[0]), flush=True)
        if eigenvalues[0] >= -args.eps:
            break
        vector = eigenvectors[:, 0]
        support = np.argsort(np.abs(vector))[-args.cut_support:]
        integer = np.zeros(2 * N + 1, dtype=np.int64)
        scale = 100 / np.max(np.abs(vector[support]))
        integer[support] = np.rint(scale * vector[support]).astype(np.int64)
        divisor = np.gcd.reduce(np.abs(integer[integer != 0]))
        integer //= max(1, divisor)
        assert np.any(integer)
        cut_matrix = np.outer(integer, integer).astype(float)
        constraints.append(cp.sum(cp.multiply(cut_matrix, Y)) >= 0)
        integer_cuts.append(integer)
else:
    problem = cp.Problem(cp.Minimize(0), constraints)
    if args.solver == "SCS":
        value = problem.solve(solver="SCS", eps=args.eps,
                              max_iters=args.max_iters, verbose=False)
    else:
        value = problem.solve(solver="CLARABEL", max_iter=args.max_iters,
                              tol_gap_abs=args.eps, tol_feas=args.eps,
                              tol_gap_rel=args.eps, verbose=False)
print("status", problem.status, "value", value)
print("solver", problem.solver_stats.solver_name,
      "iters", problem.solver_stats.num_iters,
      "time", problem.solver_stats.solve_time)
if integer_cuts:
    print("integer_cuts", [
        [(int(index), int(value)) for index, value in enumerate(vector)
         if value]
        for vector in integer_cuts
    ])
if Y.value is not None and problem.status in (cp.OPTIMAL,
                                               cp.OPTIMAL_INACCURATE):
    eigenvalues = np.linalg.eigvalsh((Y.value + Y.value.T) / 2)
    print("min_eigenvalue", float(eigenvalues[0]))
    violations = sorted(
        ((float(np.max(np.abs(c.violation()))), index,
          type(c).__name__)
         for index, c in enumerate(constraints)), reverse=True)
    print("max_constraint_violation", violations[0][0])
    print("largest_violations", violations[:5])
