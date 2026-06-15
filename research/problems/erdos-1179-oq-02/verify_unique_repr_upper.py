#!/usr/bin/env python3
"""
Build-free certificate for the deterministic upper-bound companion of
Erdős #1179 oq-02 (see proofs/Proofs/Erdos1179OQ02Upper.lean).

oq-02 conjectures g_ε(N) ≤ log₂N + O_ε(1). The lower bound g_ε(N) ≥ log₂N is in
Erdos1179OQ02.lean (PR #24551). This certificate confirms the sharpest upper
side on the elementary-abelian-2-group family G = (ZMod 2)^m, N = 2^m:

  A = standard basis  ⟹  reprCount_A(g) = 1 for every g
                      ⟹  A is exactly 0-uniform (|F(g) − 2^|A|/N| = 0)
                      ⟹  |A| = m = log₂N = Nat.clog 2 N  (matches the lower bound)

i.e. g_0(N) = log₂N exactly, deterministically (not just w.h.p.), so the additive
constant in oq-02 is 0 on this family and cannot be forced positive in general.

reprCount_A(g) = #{S ⊆ A : XOR over S = g}.  Pure standard library.
"""

from itertools import combinations, product
from collections import Counter
from math import ceil, log2


def repr_counts_basis(m):
    """reprCount over G=(F2)^m for A = standard basis."""
    cnt = Counter()
    for r in range(m + 1):
        for S in combinations(range(m), r):
            v = 0
            for i in S:
                v ^= (1 << i)
            cnt[v] += 1
    return cnt


def main():
    ok = True
    for m in range(1, 9):
        N = 2 ** m
        cnt = repr_counts_basis(m)
        all_g = range(N)
        unique = all(cnt[g] == 1 for g in all_g)        # reprCount ≡ 1
        total = sum(cnt[g] for g in all_g)               # = 2^|A|
        mu = (2 ** m) / N                                 # expected count = 1
        zero_uniform = all(abs(cnt[g] - mu) <= 0 for g in all_g)
        clogN = ceil(log2(N))
        card_opt = (m == clogN)                          # |A| = ⌈log₂N⌉
        row_ok = unique and total == 2 ** m and zero_uniform and card_opt
        ok = ok and row_ok
        print(f"m={m} N={N}: reprCount≡1 {unique}, Σ=2^|A| {total==2**m}, "
              f"0-uniform {zero_uniform}, |A|=clog₂N {card_opt}  -> {'OK' if row_ok else 'FAIL'}")

    print("\nRESULT:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
