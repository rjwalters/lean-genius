#!/usr/bin/env python3
"""
Certificate for erdos-131-oq-01-oq-01 — exact small values of F(N) (Erdős #131).

F(N) = maximum size of A ⊆ {1,...,N} that is "non-dividing": no element a ∈ A
divides the sum of any subset S ⊆ A minus {a} with |S| ≥ 2.  (This is exactly the Lean
definition `IsNonDividing` / `F` in Proofs/Erdos131Problem.lean:47,109.)

OQ-01-OQ-01 asks for the *growth rate* of F(N) (is it N^{1/5+o(1)}?).  That is a
hard open asymptotic — the known rigorous window is
    exp(c·sqrt(log N))   ≤   F(N)   ≤   N^{1/4 + o(1)}
(Straus lower bound; Pham–Zakharov 2024 upper bound, which refuted F(N) > N^{1/2-o(1)}).

This script does NOT attempt to answer the exponent question (it cannot be answered
from small N — see the effective-exponent table below).  It provides two things of
honest value:

  (1) EXACT values F(1..M) computed two independent ways that must agree
      (brute-force over all ≥2-subsets  vs.  a residue-class DP), an internal
      cross-validation guarding against an off-by-one in the predicate.
  (2) A quantified demonstration of WHY the exponent is empirically inaccessible:
      the finite-N effective exponent log F(N)/log N is still ≈0.49 at N=54 —
      about double the proven asymptotic ceiling 1/4 and far above the conjectured
      1/5 — and is decreasing only glacially.

Run: python3 verify_Fn.py
"""

from itertools import combinations
import math


# ---- Predicate, method 1: brute force over all >=2 subsets of the others -----
def is_nondividing_brute(A):
    A = list(A)
    for a in A:
        others = [b for b in A if b != a]
        for r in range(2, len(others) + 1):
            for S in combinations(others, r):
                if sum(S) % a == 0:
                    return False
    return True


# ---- Predicate, method 2: residue DP tracking size-1 vs size->=2 reachability -
def is_nondividing_dp(A):
    for a in A:
        if a == 1:
            if len(A) - 1 >= 2:   # 1 divides every sum
                return False
            continue
        reach1, reach2 = set(), set()      # residues mod a by 1-subset / >=2-subset
        for b in A:
            if b == a:
                continue
            x = b % a
            new2 = set(reach2)
            for r in reach1:
                new2.add((r + x) % a)
            for r in reach2:
                new2.add((r + x) % a)
            reach1.add(x)
            reach2 = new2
            if 0 in reach2:                # some >=2 subset of others ≡ 0 (mod a)
                return False
    return True


# ---- F(N) via DFS with a size-based bound; pred = which predicate to use ------
def F(N, pred):
    best = 0

    def dfs(start, cur):
        nonlocal best
        if len(cur) + (N - start + 1) <= best:
            return
        if len(cur) > best:
            best = len(cur)
        for x in range(start, N + 1):
            if len(cur) + (N - x + 1) <= best:
                break
            cur.append(x)
            if pred(cur):
                dfs(x + 1, cur)
            cur.pop()
    dfs(1, [])
    return best


def main():
    # (1) cross-validate the two predicates on F(1..30)
    M_cross = 30
    vb = [F(N, is_nondividing_brute) for N in range(1, M_cross + 1)]
    vd = [F(N, is_nondividing_dp) for N in range(1, M_cross + 1)]
    assert vb == vd, f"predicate mismatch!\nbrute={vb}\ndp   ={vd}"
    print(f"[cross-validation] brute == DP on F(1..{M_cross}): PASS")
    print(f"  F(1..{M_cross}) = {vb}")

    # spot-check a known witness: {2,4,5} is non-dividing, {2,3,4} is not
    assert is_nondividing_brute([2, 4, 5]) and is_nondividing_dp([2, 4, 5])
    assert not is_nondividing_brute([2, 3, 4]) and not is_nondividing_dp([2, 3, 4])
    # 1 can sit in a set of size <=2 only
    assert is_nondividing_dp([1, 7]) and not is_nondividing_dp([1, 3, 5])
    print("[witnesses] {2,4,5} ok, {2,3,4} bad, {1,x} size-2 ok / size-3 bad: PASS")

    # (2) extend with the fast DP and report thresholds + effective exponent
    M = 54
    vals = list(vd) + [F(N, is_nondividing_dp) for N in range(M_cross + 1, M + 1)]
    print(f"\n  F(1..{M}) = {vals}")

    thresholds = {}
    for i, v in enumerate(vals, start=1):
        thresholds.setdefault(v, i)
    print(f"  smallest N with F(N)=k:  {thresholds}")

    print("\n  effective exponent  log F(N)/log N  at each new threshold:")
    for k, N in sorted(thresholds.items()):
        if N > 1:
            print(f"    F={k} first at N={N:>2}:  exp = {math.log(k)/math.log(N):.3f}")
    print("\n  => at N=54 the effective exponent is still ~0.49, ~2x the proven")
    print("     asymptotic ceiling 1/4 and far from the conjectured 1/5 = 0.20.")
    print("     Small-N data cannot resolve the growth exponent.")
    print("\nALL CHECKS PASS.")


if __name__ == "__main__":
    main()
