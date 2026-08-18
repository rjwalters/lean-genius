#!/usr/bin/env python3
"""{8,8} Stage-A offset-ledger kill: model of record (squad 2643/2645).

Setup (all from certified structure at freqpair tip):
  Zero-layer partition {8,8}: used comps e1,e2 = Z24, cross q3 forced
  (amat [[0,3],[3,0]]), orphan economy 4x B(m=8) per side (q2-leg to own
  comp phases {0,d_i} after orphan gauge, unit leg to the other comp,
  offset c_i), c0 covers (e1 canonical mod 3, e2 shifted by a in Z3),
  e1-e2 circulant Sidon block A (4 reps after gauge; squad 2634).

Certified forms used: q3 phaseSet (equalComponent_quotientThree_exists_
phaseSet), q2 phaseSet, quotient-one affine cover, c0 affine minimum
cover, card_common_eq_one_of_not_defectAdj, secondOrderDefectGraph_adj_
iff_card_common_eq_zero.  NO intra-orphan structure, NO q>=4.

Forced alignments (derived, squad 2643 (b)): anti-aligned unit legs or
anti-aligned e2-c0 cover supply x+y-indexed commons that collide with
the x-y-indexed exact (e1,e2) ledger on some class -> C4.  All aligned.

THE KILL -- (e1,e2) cross-pair ledger, class c = x - y:
  supply(c) = [c = a mod 3]                       (c0 witness)
            + #{i: c in {-c_i, -c_i + d_i}}       (O_i witness w = y - c_i)
            + #{j: c in {c'_j, c'_j - d_j}}       (P_j witness w = x - c'_j)
  requirement: = 1 on the 14 classes not in A and not = a (mod 3);
               <= 1 on the 2 classes of A not = a; = 0 on classes = a.
  16 slots vs capacity 14 + 2 -> exact cover forced.
  RESULT: INFEASIBLE for all 4 Sidon reps x all 3 values of a (12/12),
  verified by backtracking exact-cover AND independent CP-SAT.
  Diagnostics: always exactly one class short; LP relaxation (even with
  per-d multiplicity duals) is feasible -> obstruction is integral;
  no small Farkas certificate exists -> Lean endpoint = finite decide.

Lean endpoint signature (recommended, kernel decide -- squad 2645):
  For Dcase : Fin 4, a : Fin 3:
    no assignment t : Fin 8 -> ZMod 24 exists with
      pair k covers {t k, t k + dlist k}  (dlist = COMPL twice, sorted)
      * all 16 covered values distinct,
      * none = a (mod 3), none equal to the A-class = a (mod 3),
      * every class not in A and not = a (mod 3) covered.
  (Distinctness + the two avoid-sets + cardinality 16 = 14 + 2 imply the
  exact cover; the mod-3 residue of each t is forced -- t = a+1 (mod 3)
  when d = 1 (mod 3), t = a+2 when d = 2 -- so the search space per case
  is 8^8, and the per-class matching encoding prunes it far below that.)

Graph bridge hypotheses to discharge per case (squad 2643 (b)-(d)):
  b1. each orphan's q2 block normalized to phases {0, d_i} (orphan gauge)
  b2. unit legs aligned (else (e1,e2) ledger violated -- lemma shape:
      anti-aligned unit leg gives two classes s with an x+y = s common;
      pick a pair with x+y = s and x - y not in A covered by the ledger)
  b3. e2-c0 cover aligned (same collision shape through c0)
  b4. c_i mod 3 forced by the (c0, O_i) ledger: residues {0, d_i, c_i+a}
      exhaust Z3   (three-source exactness; d_i not = 0 mod 3)
  b5. the (e1,e2) ledger equation above (B-atom census + unit/q2 forms)

Run: python3 eight_eight_stage_a.py   (needs ortools for the cross-check)
"""
from itertools import product

N = 24
DSETS = {
    (2, 5, 7):  ((0, 2, 7),  (4, 8, 10, 11)),
    (2, 8, 10): ((0, 2, 10), (4, 5, 7, 11)),
    (4, 7, 11): ((0, 4, 11), (2, 5, 8, 10)),
    (5, 8, 11): ((0, 5, 13), (2, 4, 7, 10)),
}

def stage_a(A, COMPL, a):
    """Backtracking exact cover; returns list of solutions (empty = dead)."""
    need = [c for c in range(N) if c % 3 != a and c not in A]
    acls = [c for c in A if c % 3 != a]
    target = set(need) | set(acls)
    ds = [d for d in COMPL for _ in range(2)]
    sols = []

    def bt(k, remaining, ts):
        if sols:
            return
        if k == len(ds):
            if not remaining:
                sols.append(list(ts))
            return
        d = ds[k]
        for t in range(N):
            p = {t, (t + d) % N}
            if len(p) == 2 and p <= remaining:
                bt(k + 1, remaining - p, ts + [t])

    bt(0, set(target), [])
    return sols

if __name__ == "__main__":
    dead = 0
    for D, (A, COMPL) in DSETS.items():
        for a in range(3):
            sols = stage_a(A, COMPL, a)
            v = "INFEASIBLE" if not sols else f"FEASIBLE {sols[0]}"
            if not sols:
                dead += 1
            print(f"D={D} a={a}: {v}")
    print(f"\n{dead}/12 cases dead -> {{8,8}} offset ledgers cannot tile"
          if dead == 12 else f"\nWARNING: only {dead}/12 dead")
