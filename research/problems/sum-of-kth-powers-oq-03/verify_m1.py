#!/usr/bin/env python3
"""
Reproducible, build-free verification of the Milestone-1 (M1) spec for
sum-of-kth-powers-oq-03: the odd-number-partition (telescoping) proof of
Nicomachus's theorem  Sum_{i=1}^n i^3 = (Sum_{i=1}^n i)^2.

This script independently re-derives every arithmetic claim the M1 Lean
lemmas depend on (symbolically via sympy, and by brute force), so the spec's
correctness is machine-checkable without Docker/Mathlib. It is NOT a proof of
the Lean lemmas; it certifies the *mathematics* the lemmas encode, so the
eventual Lean port is a transcription rather than a fresh derivation.

Run:  python3 verify_m1.py   (exits non-zero on any mismatch)

T i := i*(i+1)/2  (i-th triangular number, T 0 = 0).
The odd-partition proof tiles the first T_n odd numbers into n consecutive
blocks; block i (1-indexed) has i terms and sums to i^3.
"""
import sys
import sympy as sp


def check(name, cond):
    print(f"[{'OK' if cond else 'FAIL'}] {name}")
    if not cond:
        check.failed = True


check.failed = False

i, j, m, n = sp.symbols("i j m n", integer=True, nonnegative=True)
Ti = i * (i + 1) / 2          # T i
Tim1 = (i - 1) * i / 2        # T (i-1)

# L1  sum of odds:  Sum_{j=0}^{m-1} (2 j + 1) = m^2
check("L1 sum_odds: sum_{j<m}(2j+1) = m^2",
      sp.simplify(sp.summation(2 * j + 1, (j, 0, m - 1)) - m**2) == 0)

# L2 core: block i = T(i)^2 - T(i-1)^2 = i^3, proved additively to dodge nat-sub:
#          T(i-1)^2 + i^3 = T(i)^2
check("L2 telescope (additive): T(i-1)^2 + i^3 = T(i)^2",
      sp.simplify(Tim1**2 + i**3 - Ti**2) == 0)
check("L2 block = T(i)^2 - T(i-1)^2 = i^3",
      sp.simplify(Ti**2 - Tim1**2 - i**3) == 0)

# Block geometry: block i occupies odd-sequence positions [T(i-1), T(i)),
# i.e. i terms, smallest odd 2 T(i-1)+1, largest 2 T(i)-1.
check("block size T(i)-T(i-1) = i", sp.simplify(Ti - Tim1 - i) == 0)
check("smallest odd 2 T(i-1)+1 = i^2-i+1", sp.simplify(2 * Tim1 + 1 - (i**2 - i + 1)) == 0)
check("largest  odd 2 T(i)-1   = i^2+i-1", sp.simplify(2 * Ti - 1 - (i**2 + i - 1)) == 0)

# nat-subtraction-free reindex (recommended Lean formulation): block index i in
# range n maps to cube (i+1)^3 on positions [T i, T (i+1)); no i-1 anywhere.
Ti0 = i * (i + 1) / 2
Tip1 = (i + 1) * (i + 2) / 2
check("reindex: T(i)^2 + (i+1)^3 = T(i+1)^2 (no nat-sub)",
      sp.simplify(Ti0**2 + (i + 1)**3 - Tip1**2) == 0)

# Gauss: T n = Sum_{i=0}^{n} i  (matches parent RHS base = (sum i)^2)
check("Gauss T(n) = sum_{i<=n} i",
      sp.simplify(sp.summation(i, (i, 0, n)) - n * (n + 1) / 2) == 0)

# --- ℕ-DIVISION HAZARD (L2′ "/2" clearing) -------------------------------------
# In Lean `T i = i*(i+1)/2` is *truncated* Nat division. The only build-fiddly
# step left is clearing it. The clean route is `2 * T k = k*(k+1)` (division-free),
# valid because `k*(k+1)` is always even (Mathlib: `Nat.even_mul_succ_self`).
# Multiplying the additive telescope identities through by 4 then removes every
# `/2`, giving the exact ring identities the Lean proof should `ring`/`omega` on:
#   (2 T(i-1))^2 + 4 i^3     = (2 T(i))^2      with 2 T k = k(k+1)
#   ((i-1) i)^2 + 4 i^3      = (i (i+1))^2
#   (i (i+1))^2 + 4 (i+1)^3  = ((i+1)(i+2))^2  (nat-sub-free reindex form)
check("clear /2: 2 T(i) = i(i+1) (division-free)",
      sp.simplify(2 * Ti - i * (i + 1)) == 0)
check("L2 cleared (x4, no /2): ((i-1)i)^2 + 4 i^3 = (i(i+1))^2",
      sp.simplify(((i - 1) * i)**2 + 4 * i**3 - (i * (i + 1))**2) == 0)
check("reindex cleared (x4, no /2): (i(i+1))^2 + 4 (i+1)^3 = ((i+1)(i+2))^2",
      sp.simplify((i * (i + 1))**2 + 4 * (i + 1)**3 - ((i + 1) * (i + 2))**2) == 0)
# ℕ-division is EXACT here (no truncation): 2*(i*(i+1)//2) == i*(i+1) for all i,
# i.e. i*(i+1) is even — the content of `Nat.even_mul_succ_self`.
check("Nat-division exact: 2*(k*(k+1)//2) == k*(k+1) and k*(k+1) even, k=0..200",
      all(2 * ((k * (k + 1)) // 2) == k * (k + 1) and (k * (k + 1)) % 2 == 0
          for k in range(0, 201)))


def T(k):
    return k * (k + 1) // 2


# Brute-force end-to-end cross-check of the whole chain for n = 0..60:
#   blocks-telescope == sum of cubes == first T_n odds == T_n^2 == (sum i)^2
allok = True
for N in range(0, 61):
    blocks = 0
    for ii in range(1, N + 1):
        lo, hi = T(ii - 1), T(ii)            # positions [lo, hi)
        block = sum(2 * jj + 1 for jj in range(lo, hi))
        if block != ii**3:
            allok = False
        blocks += block
    first_odds = sum(2 * jj + 1 for jj in range(0, T(N)))
    cubes = sum(ii**3 for ii in range(0, N + 1))
    sumsq = sum(ii for ii in range(0, N + 1))**2
    if not (blocks == cubes == first_odds == T(N)**2 == sumsq):
        allok = False
check("numeric n=0..60: blocks==cubes==firstOdds==T_n^2==(sum i)^2", allok)

if check.failed:
    print("VERIFICATION FAILED")
    sys.exit(1)
print("All M1 identities verified.")
