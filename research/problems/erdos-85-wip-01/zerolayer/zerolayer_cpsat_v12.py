#!/usr/bin/env python3
"""Zero-layer census v12: exact CP-SAT encoding with the FULL used-used
quotient matrix AND the child-cover lcm atom kills (supersedes v11, whose
diagonal-only excess term silently assumed cross-used local excess
vanishes -- falsified 2026-08-10, squad msgs 2383-2391).

Requires: pip install ortools

Constraint-to-lemma map (all cold-verified on feature/erdos85-assembly):
  load 12 per comp .... degree_sixteen_zeroLayer_used_to_orphan_quotient_sum_eq_twelve (6e7a50aafc)
  per-row budget ...... degree_sixteen_zeroLayer_used_component_row_after_contact_excess (77513d8b8b)
  used row sum 3 ...... zero-layer used-cell theorem (1c69a9107d):
                        every used vertex has exactly 3 R-neighbors, so
                        sum_j Q(e_i, e_j) = 3 including the diagonal
  balance ............. secondOrder_componentQuotientMatrix_balance
  k=4 diagonal != 3 ... degree_sixteen_orderTwelve_diagonalQuotient_ne_three
  A-atom equal-lcm .... degree_sixteen_two_quotientOne_legs_reduced_lcm (38911fccdb)
  C table ............. degree_sixteen_quotientThree_reduced_order_classification (91b41859e3)
  B 2-leg table ....... degree_sixteen_quotientTwo_reduced_order_classification (a08b18cbb9)
  B/A unit leg ........ degree_sixteen_quotientOne_reduced_balance (de8d357939)
  D atom .............. degree_sixteen_zeroLayer_nonThreeDivisible_orphan_D_atom (d113de27bd)
  orphan row sum 3 .... degree_sixteen_zeroLayer_orphan_to_used_quotient_sum_eq_three (0fefbff640)
  used mass 48, 3|k ... degree_sixteen_zeroLayer_used_component_order_package
  parts >= 2 .......... degree_sixteen_zeroLayer_used_component_reduced_partition
                        (aa1ee79fad; applied as a downstream filter --
                        survivors with a part 1 are not graph-compatible)

Atoms (structurally proved, see table commits above):
  A (b=1,1,1): triple with equal pairwise lcms, m = that lcm, excess 0.
  B (b=2,1): m = k_e or k_e = 2m on the 2-leg; 1-leg needs k_f | m.
     excess 2m/k_e on e.
  C (b=3): m = k or k = 3m. excess 6m/k.
  D (non-3-div): u = k, k >= 3, 3 nmid k. excess 2.
Counts are integers >= 0.  Per-comp: sum load = 12k; orphan-atom excess
plus ALL used-cell excess terms a_ij (a_ji - 1) (cross AND diagonal)
equals exactly 2(k-1).  Objective: minimize total orphan excess.
Verdicts: OPTIMAL -> SURVIVOR(min), INFEASIBLE -> DEAD.

2026-08-10 result: 45 raw survivors / 186 dead / 0 CAP; 12 survivors
after the parts>=2 graph-compatibility filter:
  16; 12,4; 12,2,2; 10,2,2,2; 8,8; 8,4,4; 6,6,2,2; 6,3,3,2,2;
  4,4,4,4; 4,4,4,2,2; 4,4,2,2,2,2; 2^8
Notable vs v10: {16},{12,4},{12,2,2},{10,2,2,2},{6,3,3,2,2} are
RESURRECTED (their v7-v10 deaths used the false vanishing assumption);
{8,2,2,2,2} and {5,5,2,2,2} are NEWLY DEAD (the used-cell row-sum-3
budget is a genuinely new constraint).  4^4 survives all-A via a
cross-pairing matrix (diag 0, paired a=3), confirming the all-A class
is NOT closed by the diagonal-only capstone.

v12 change (2026-08-11, squad msgs 2459+): every used comp e has the
mandatory unit child contact Q(e,c0)=1 with |c0|=3, so by
false_of_two_unit_componentQuotients_lcm_ncard_lt any SECOND unit
quotient Q(e,o)=1 into a 3-divisible component with |o| < |e| gives
lcm(3,|o|) = |o| < |e| -> C4 -> False.  This kills two whole atom
families globally: concentrated C(m=k/3) and doubled-owner B(m=k_e/2).
D atoms survive (3 nmid |o| makes the lcm 3|o| = |e|, not less).
Result: 35 raw survivors / 196 dead; 10 graph-compatible:
  16; 12,4; 10,2,2,2; 8,8; 8,4,4; 6,6,2,2; 4,4,4,4; 4,4,4,2,2;
  4,4,2,2,2,2; 2^8
Newly dead vs v11: {12,2,2} (also closed graph-facing, 00e0467941)
and {6,3,3,2,2}.
"""
import sys
from math import gcd
from itertools import combinations
from ortools.sat.python import cp_model

def partitions(n, mx=None):
    if mx is None: mx = n
    if n == 0:
        yield []
        return
    for p in range(min(n, mx), 0, -1):
        for rest in partitions(n - p, p):
            yield [p] + rest

def lcm(a, b): return a * b // gcd(a, b)

def solve(K):
    t = len(K)
    model = cp_model.CpModel()
    atoms = []  # (loadvec dict, excessvec dict, label)
    for tri in combinations(range(t), 3):
        a, b, c = tri
        lab_, lac, lbc = lcm(K[a], K[b]), lcm(K[a], K[c]), lcm(K[b], K[c])
        if lab_ == lac == lbc:
            m = lab_
            atoms.append(({a: m, b: m, c: m}, {}, f"A(m={m},{tri})"))
    for e in range(t):
        for f in range(t):
            if e == f: continue
            ke, kf = K[e], K[f]
            cands = {ke}  # v12: ke//2 doubled-owner B killed by child-cover lcm
            for m in cands:
                if not (m == kf or (m > kf and m % kf == 0)): continue
                ex = 2 * m // ke
                qe, qf = 2 * m // ke, m // kf
                if 2 * (qe - 1) + (qf - 1) > 3 * m - 3: continue
                atoms.append(({e: 2 * m, f: m}, {e: ex}, f"B(m={m},e={e},f={f})"))
    for e in range(t):
        k = K[e]
        cands = {k}  # v12: k//3 concentrated C killed by child-cover lcm
        for m in cands:
            ex = 6 * m // k
            q = 3 * m // k
            if 3 * (q - 1) > 3 * m - 3: continue
            atoms.append(({e: 3 * m}, {e: ex}, f"C(m={m},e={e})"))
    for e in range(t):
        k = K[e]
        if k >= 3 and k % 3 != 0:
            atoms.append(({e: k}, {e: 2}, f"D(u={k},e={e})"))

    counts = []
    for i, (ld, exv, lab) in enumerate(atoms):
        ub = min(12 * K[j] // v for j, v in ld.items())
        counts.append(model.NewIntVar(0, max(ub, 0), f"n{i}"))
    # v11: full used-used quotient matrix a[i][j] (per-vertex counts).
    a = [[model.NewIntVar(0, 3, f"a_{i}_{j}") for j in range(t)]
         for i in range(t)]
    for i in range(t):
        model.Add(sum(a[i][j] for j in range(t)) == 3)
    for i in range(t):
        for j in range(i + 1, t):
            model.Add(K[i] * a[i][j] == K[j] * a[j][i])
    for i in range(t):
        if K[i] == 4:
            model.Add(a[i][i] != 3)
    for e in range(t):
        rhs = 2 * (K[e] - 1)
        model.Add(sum(c * ld[e] for c, (ld, exv, lab) in zip(counts, atoms)
                      if e in ld) == 12 * K[e])
        used_terms = []
        for j in range(t):
            m = model.NewIntVar(-1, 2, f"m_{e}_{j}")
            model.Add(m == a[j][e] - 1)
            prod = model.NewIntVar(-3, 9, f"x_{e}_{j}")
            model.AddMultiplicationEquality(prod, [a[e][j], m])
            used_terms.append(prod)
        model.Add(sum(c * exv[e] for c, (ld, exv, lab) in zip(counts, atoms)
                      if e in exv) + sum(used_terms) == rhs)
    tot = sum(c * sum(exv.values()) for c, (ld, exv, lab) in zip(counts, atoms)
              if exv)
    z = model.NewIntVar(0, 1000, "z")
    model.Add(z == (tot if not isinstance(tot, int) else 0))
    model.Minimize(z)
    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = 60
    solver.parameters.num_search_workers = 4
    st = solver.Solve(model)
    if st == cp_model.OPTIMAL:
        val = int(solver.ObjectiveValue())
        wit = [(atoms[i][2], solver.Value(c))
               for i, c in enumerate(counts) if solver.Value(c) > 0]
        amat = [[solver.Value(a[i][j]) for j in range(t)] for i in range(t)]
        return "SURVIVOR", val, wit, amat
    if st == cp_model.INFEASIBLE:
        return "DEAD", None, None, None
    return "CAP", None, None, None

if __name__ == "__main__":
    dead, surv, cap = [], [], []
    for K in partitions(16):
        tag = ",".join(map(str, K))
        status, val, wit, amat = solve(K)
        if status == "SURVIVOR":
            surv.append((tag, val))
            print(f"[SURVIVOR] {tag} minexc={val} budget={2*(16-len(K))} " +
                  f"amat={amat} :: " +
                  "; ".join(f"{c}x{lab}" for lab, c in wit), flush=True)
        elif status == "DEAD":
            dead.append(tag)
            print(f"[DEAD] {tag}", flush=True)
        else:
            cap.append(tag)
            print(f"[CAP] {tag}", flush=True)
    print(f"\nTOTALS: SURVIVORS {len(surv)}  DEAD {len(dead)}  CAP {len(cap)}")
