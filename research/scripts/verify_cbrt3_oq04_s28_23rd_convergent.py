#!/usr/bin/env python3
"""Certificate for cube-root-3-irrational-oq-04 S28: the 23rd CF convergent.

Independently re-derives the simple continued fraction of ∛3 to >23 terms at
220-digit precision, computes the convergent recursion, and verifies the
exact-integer cube-side direction for the 23rd convergent (index 22), which is a
LOWER bound on ∛3.

Run: python3 verify_cbrt3_oq04_s28_23rd_convergent.py
"""
from mpmath import mp, mpf, cbrt, floor

mp.dps = 220

# --- Re-derive the CF of ∛3 from scratch (anti-typo: no quoted prior tail) ---
x = cbrt(3)
a = []
y = x
for _ in range(26):
    ai = int(floor(y))
    a.append(ai)
    frac = y - ai
    if frac == 0:
        break
    y = 1 / frac

EXPECTED_PREFIX = [1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, 4, 2, 6, 4, 4, 1, 3, 2]
assert a[:len(EXPECTED_PREFIX)] == EXPECTED_PREFIX, f"CF prefix mismatch: {a[:len(EXPECTED_PREFIX)]}"
assert a[22] == 2, f"a22 expected 2, got {a[22]}"

# --- Convergent recursion p_k = a_k p_{k-1} + p_{k-2}, q_k similarly ---
pm2, pm1 = 1, a[0]
qm2, qm1 = 0, 1
convs = [(a[0], 1)]
for k in range(1, len(a)):
    pk = a[k] * pm1 + pm2
    qk = a[k] * qm1 + qm2
    convs.append((pk, qk))
    pm2, pm1 = pm1, pk
    qm2, qm1 = qm1, qk

p, q = convs[22]
assert (p, q) == (71966106017, 49898510978), f"23rd convergent mismatch: {p}/{q}"

# Sanity: the recursion uses the on-main predecessors (indices 20, 21).
assert convs[20] == (8350315863, 5789785648)
assert convs[21] == (31807895077, 22054362665)
assert p == 2 * convs[21][0] + convs[20][0]
assert q == 2 * convs[21][1] + convs[20][1]

# --- Exact-integer cube-side check: LOWER bound iff p^3 < 3 q^3 ---
lhs = p ** 3
rhs = 3 * q ** 3
assert lhs < rhs, "expected p^3 < 3 q^3 for a lower bound"
diff = rhs - lhs

print(f"CF a0..a25 = {a}")
print(f"a22        = {a[22]}")
print(f"convergent = {p}/{q}  (index 22, the 23rd convergent)")
print(f"p^3        = {lhs}")
print(f"3*q^3      = {rhs}")
print(f"3*q^3 - p^3 = {diff}  (> 0  =>  p/q < cbrt3, a valid LOWER bound)")
rel = (x - mpf(p) / q) / x
print(f"relative gap = {mp.nstr(rel, 6)}")
print("OK: 71966106017/49898510978 < cbrt3 verified (even index 22, lower bound).")
