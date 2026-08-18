#!/usr/bin/env python3
"""Zero-layer census v13: v12 + the ANTIPODAL COVERAGE filter
(squad msgs 2638/2640/2642/2646).  Requires: pip install ortools

Law: every orphan has even order (all graph-compatible parts are even);
its antipodal pairs (v, v + n/2) are never defect-adjacent, so by
card_common_eq_one_of_not_defectAdj they need exactly one common --
adjacency is NO escape (codex 2640: the law binds adjacent pairs too).
Witness channels:
  - equal-order blocks, ANY q: dead by antipodal covariance
    (cycleIntertwiner_antipodal_covariance /
     no_equalEvenCycleBlock_antipodal_commonSource, da0a11ff55):
    B(x+h,y) = B(x,y+h) at h = r/2, so a witness row for both antipodes
    forces a second witness row -> C4.
  - larger-order witness: surjective phi -> same double-witness. Dead.
  - smaller-order witness via unit cover (fiber step 3k): covers the
    antipodal class iff 2k | m -- and then EXACTLY once (fibers
    partition).  This is the ONLY live channel.
  - c0: orphans have no child contact.  Dead.
Atom coverability:
  A(m, tri): some leg k in tri with 2k | m
  B(m=k_e, e, f): unit leg with 2k_f | m  (the 2-leg host is equal-order)
  C: already killed in v12 (child-cover lcm)
  D(k): no channel, never coverable
Filter: every atom with count > 0 must be coverable (strict), or -- in
the conservative variant -- may be saved by an uncertified intra-orphan
cover from a smaller orphan of order 3m' with 2m' | m present in the
same economy.

2026-08-11 RESULT: ALL EIGHT v12 survivors are DEAD in both variants:
  16; 12,4(already dead graph-facing); 8,8; 8,4,4; 6,6,2,2; 4,4,4,4;
  4,4,4,2,2; 4,4,2,2,2,2; 2^8  -- i.e. the zero-layer s=0 case closes
entirely once (alpha) the q-general equal-order lemma (da0a11ff55, DONE)
and (beta) the unequal-order witness lemmas are graph-certified, plus
(gamma) these eight coverable-economy censuses as Lean endpoints.
Deaths are ECONOMIC (load/excess laws unsatisfiable by coverable atoms),
not mere channel-counting -- e.g. {8,4,4}: B24s are coverable (8|8) but
comp e2's excess 6 can only be paid by uncoverable atoms.
"""
import sys
from math import gcd
from itertools import combinations
from ortools.sat.python import cp_model

def lcm(a, b): return a * b // gcd(a, b)

SURV = [[16], [8, 8], [8, 4, 4], [6, 6, 2, 2], [4, 4, 4, 4],
        [4, 4, 4, 2, 2], [4, 4, 2, 2, 2, 2], [2] * 8]

def solve(K, intra_ok):
    t = len(K)
    model = cp_model.CpModel()
    atoms = []
    for tri in combinations(range(t), 3):
        a, b, c = tri
        l1, l2, l3 = lcm(K[a], K[b]), lcm(K[a], K[c]), lcm(K[b], K[c])
        if l1 == l2 == l3:
            m = l1
            cov = any(m % (2 * K[x]) == 0 for x in tri)
            atoms.append(({a: m, b: m, c: m}, {}, f"A(m={m},{tri})", m, cov))
    for e in range(t):
        for f in range(t):
            if e == f: continue
            ke, kf = K[e], K[f]
            m = ke  # v12: doubled-owner branch killed by child-cover lcm
            if not (m == kf or (m > kf and m % kf == 0)): continue
            q_f = m // kf
            if 2 + (q_f - 1) > 3 * m - 3: continue
            cov = (m % (2 * kf) == 0)
            atoms.append(({e: 2 * m, f: m}, {e: 2}, f"B(m={m},e={e},f={f})", m, cov))
    for e in range(t):
        k = K[e]
        if k >= 3 and k % 3:
            atoms.append(({e: k}, {e: 2}, f"D(u={k},e={e})", None, False))
    counts = []
    for i, (ld, exv, lab, m, cov) in enumerate(atoms):
        ub = min(12 * K[j] // v for j, v in ld.items())
        counts.append(model.NewIntVar(0, max(ub, 0), f"n{i}"))
    a_ = [[model.NewIntVar(0, 3, f"a{i}{j}") for j in range(t)] for i in range(t)]
    for i in range(t):
        model.Add(sum(a_[i][j] for j in range(t)) == 3)
    for i in range(t):
        for j in range(i + 1, t):
            model.Add(K[i] * a_[i][j] == K[j] * a_[j][i])
        if K[i] == 4:
            model.Add(a_[i][i] != 3)
    for e in range(t):
        model.Add(sum(c * ld[e] for c, (ld, exv, lab, m, cov) in zip(counts, atoms)
                      if e in ld) == 12 * K[e])
        terms = []
        for j in range(t):
            mm = model.NewIntVar(-1, 2, f"m{e}{j}")
            model.Add(mm == a_[j][e] - 1)
            pr = model.NewIntVar(-3, 9, f"p{e}{j}")
            model.AddMultiplicationEquality(pr, [a_[e][j], mm])
            terms.append(pr)
        model.Add(sum(c * exv[e] for c, (ld, exv, lab, m, cov) in zip(counts, atoms)
                      if e in exv) + sum(terms) == 2 * (K[e] - 1))
    if not intra_ok:
        for c, (ld, exv, lab, m, cov) in zip(counts, atoms):
            if not cov:
                model.Add(c == 0)
    else:
        for i, (ld, exv, lab, m, cov) in enumerate(atoms):
            if cov:
                continue
            if m is not None:
                saviors = [j for j, (l2, x2, lb2, m2, c2) in enumerate(atoms)
                           if m2 is not None and m2 < m and m % (2 * m2) == 0]
            else:
                k = int(lab.split("u=")[1].split(",")[0])
                saviors = [j for j, (l2, x2, lb2, m2, c2) in enumerate(atoms)
                           if m2 is not None and k % (6 * m2) == 0 and k % (2 * 3 * m2) == 0]
            if not saviors:
                model.Add(counts[i] == 0)
            else:
                b = model.NewBoolVar(f"sv{i}")
                model.Add(sum(counts[j] for j in saviors) >= 1).OnlyEnforceIf(b)
                model.Add(counts[i] == 0).OnlyEnforceIf(b.Not())
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = 60
    st = s.Solve(model)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        wit = [(atoms[i][2], s.Value(c)) for i, c in enumerate(counts)
               if s.Value(c) > 0]
        return "ALIVE", wit
    return "DEAD", None

if __name__ == "__main__":
    for K in SURV:
        tag = ",".join(map(str, K))
        v1, _ = solve(K, False)
        v2, w2 = solve(K, True)
        print(f"{tag}: strict={v1}  with-intraO-covers={v2}"
              + (f"  economy={w2}" if w2 else ""), flush=True)
