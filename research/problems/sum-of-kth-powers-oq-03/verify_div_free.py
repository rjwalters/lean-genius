#!/usr/bin/env python3
"""Certify the DIVISION-FREE / SUBTRACTION-FREE Lean formulation of OQ-03
(SumOfKthPowersOQ03.lean), where T n := sum_{i<n} i is the Gauss SUM (not the
closed form n(n+1)/2). Exits non-zero on any mismatch.

This complements verify_m1.py (which certifies the older T=k(k+1)/2 spec).
Each assertion mirrors exactly one Lean lemma in the draft file."""
import sys

def T(n):        return sum(range(n))                      # def T
def sum_odds(m): return sum(2 * j + 1 for j in range(m))   # L1 sum_odds
def block(i):    return sum(2 * j + 1 for j in range(T(i), T(i + 1)))

N = 200
fail = 0
for n in range(N):
    if sum_odds(n) != n ** 2:                fail += 1; print("L1 fail", n)
    if T(n + 1) != T(n) + n:                 fail += 1; print("T_succ fail", n)
    if 2 * T(n) + n != n ** 2:               fail += 1; print("two_T_add fail", n)
    if T(n) ** 2 + n ** 3 != T(n + 1) ** 2:  fail += 1; print("block_sq fail", n)
    if block(n) != n ** 3:                   fail += 1; print("block_eq_cube fail", n)
for n in range(N):
    if sum(block(i) for i in range(n)) != sum_odds(T(n)):
        fail += 1; print("tiling fail", n)
    lhs = sum(i ** 3 for i in range(n + 1))
    rhs = sum(i for i in range(n + 1)) ** 2
    if lhs != rhs:           fail += 1; print("main fail", n)
    if T(n + 1) ** 2 != rhs: fail += 1; print("T-def-RHS fail", n)

if fail:
    print(f"FAILED: {fail} mismatches"); sys.exit(1)
print(f"OK: all division-free identities verified for n=0..{N-1}")
