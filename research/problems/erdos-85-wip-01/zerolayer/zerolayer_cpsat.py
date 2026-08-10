#!/usr/bin/env python3
"""Zero-layer census v5: exact CP-SAT encoding (replaces DFS).

Requires: pip install ortools

Constraint-to-lemma map (all cold-verified on feature/erdos85-assembly):
  load 12 per comp .... degree_sixteen_zeroLayer_used_to_orphan_quotient_sum_eq_twelve (6e7a50aafc)
  contact + budget .... degree_sixteen_zeroLayer_used_minimum_contact_total (c2ab08d5a7),
                        degree_sixteen_zeroLayer_used_total_local_excess (118861d303),
                        degree_sixteen_zeroLayer_used_after_contact_excess (4fba30ebd5)
  A-atom equal-lcm .... reduced_length_eq_lcm_of_oriented_pair_injective (33bce2ba77),
                        false_of_two_unit_componentQuotients_lcm_ncard_lt (02725f694e)
  unequal entries ..... exists_oriented_reverseCover_of_component_size_lt (6e1bfa4e6a),
                        secondOrder_componentQuotientMatrix_entries_of_size_lt
  balance ............. secondOrder_componentQuotientMatrix_balance
  orphan row sum 3 .... minimumLayer_orphan_service_card_eq_one + D1 (7d07a7dd6c)
  self budget ......... secondOrder_componentQuotientMatrix_local_excess_restrict_nat
  used mass 48, 3|k ... degree_sixteen_zeroLayer_used_component_order_package
  t <= 16 ............. degree_sixteen_zeroLayer_used_component_card_le_sixteen (d8ca492c72)

Atoms (structurally constrained):
  A (b=1,1,1): triple with equal pairwise lcms, m = that lcm, excess 0.
  B (b=2,1): m = k_e or k_e = 2m on the 2-leg; 1-leg needs m = k_f or
     k_f | m with m > k_f.  excess 2m/k_e on e.  self-budget check.
  C (b=3): m = k or k = 3m. excess 6m/k.
  D (non-3-div): u = k, k >= 3, 3 nmid k. excess 2.
Counts are integers >= 0.  Per-comp: sum load = 12k; sum excess <=
2(k-1)  [totals then match 2(16-t) automatically].  Objective:
minimize total excess.  Verdicts: OPTIMAL -> SURVIVOR(min), INFEASIBLE
-> DEAD.
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
            cands = {ke}
            if ke % 2 == 0: cands.add(ke // 2)
            for m in cands:
                if not (m == kf or (m > kf and m % kf == 0)): continue
                ex = 2 * m // ke
                qe, qf = 2 * m // ke, m // kf
                if 2 * (qe - 1) + (qf - 1) > 3 * m - 3: continue
                atoms.append(({e: 2 * m, f: m}, {e: ex}, f"B(m={m},e={e},f={f})"))
    for e in range(t):
        k = K[e]
        cands = {k}
        if k % 3 == 0: cands.add(k // 3)
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
    for e in range(t):
        model.Add(sum(c * ld[e] for c, (ld, exv, lab) in zip(counts, atoms)
                      if e in ld) == 12 * K[e])
        model.Add(sum(c * exv[e] for c, (ld, exv, lab) in zip(counts, atoms)
                      if e in exv) <= 2 * (K[e] - 1))
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
        return "SURVIVOR", val, wit
    if st == cp_model.INFEASIBLE:
        return "DEAD", None, None
    return "CAP", None, None

if __name__ == "__main__":
    dead, surv, cap = [], [], []
    for K in partitions(16):
        tag = ",".join(map(str, K))
        status, val, wit = solve(K)
        if status == "SURVIVOR":
            surv.append((tag, val))
            print(f"[SURVIVOR] {tag} minexc={val} budget={2*(16-len(K))} :: " +
                  "; ".join(f"{c}x{lab}" for lab, c in wit), flush=True)
        elif status == "DEAD":
            dead.append(tag)
            print(f"[DEAD] {tag}", flush=True)
        else:
            cap.append(tag)
            print(f"[CAP] {tag}", flush=True)
    print(f"\nTOTALS: SURVIVORS {len(surv)}  DEAD {len(dead)}  CAP {len(cap)}")
