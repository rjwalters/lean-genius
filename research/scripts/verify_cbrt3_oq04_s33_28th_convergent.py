#!/usr/bin/env python3
"""
Certificate for cube-root-3-irrational-oq-04, Session S33.

Goal: produce and validate the 28th continued-fraction convergent of ∛3 as an
UPPER bound (CF index k = 27, odd ⟹ convergent lies ABOVE ∛3).

Anti-typo discipline: the continued fraction is recomputed FROM SCRATCH here at
high precision (never re-quoted from prior session notes). The decisive validity
check is the EXACT-INTEGER cube sign  p³ − 3·q³ , which is ground truth
regardless of any floating/decimal rounding used to extract CF terms.

Stdlib only (decimal). Build-free.
"""

from decimal import Decimal, getcontext

getcontext().prec = 200

# --- high-precision ∛3 via Newton: x ← x − (x³−3)/(3x²) ---
three = Decimal(3)
x = Decimal("1.44224957030740838232163831078010958839186925349935")
for _ in range(40):
    x = x - (x * x * x - three) / (3 * x * x)
cbrt3 = x
assert abs(cbrt3 ** 3 - three) < Decimal(10) ** (-180), "Newton did not converge"

# --- extract continued fraction terms a0, a1, ... from cbrt3 ---
def cf_terms(val, n):
    terms = []
    v = val
    for _ in range(n):
        a = int(v)            # floor for positive v
        terms.append(a)
        frac = v - a
        if frac == 0:
            break
        v = 1 / frac
    return terms

terms = cf_terms(cbrt3, 32)

# Known prefix of the CF of ∛3 (OEIS A002945): used only as a CROSS-CHECK,
# not as the source of truth.
known_prefix = [1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, 4, 2, 6,
                4, 4, 1, 3, 2, 3, 4, 1, 4]   # a0 .. a26
for i, a in enumerate(known_prefix):
    assert terms[i] == a, f"CF mismatch at index {i}: computed {terms[i]} vs known {a}"
print("CF prefix cross-check OK through a26 =", known_prefix[-1])
print("Computed a27 =", terms[27], " a28 =", terms[28])

# --- convergents p_k/q_k via the standard recursion ---
pm1, qm1 = 1, 0          # p_{-1}, q_{-1}
p0, q0 = terms[0], 1     # p_0,    q_0
P = [pm1, p0]
Q = [qm1, q0]
for k in range(1, 28):
    ak = terms[k]
    P.append(ak * P[-1] + P[-2])
    Q.append(ak * Q[-1] + Q[-2])
# P[i] corresponds to p_{i-1}; reindex to p_k = P[k+1]
def p(k): return P[k + 1]
def q(k): return Q[k + 1]

# --- sanity: reproduce the convergents already on main ---
checks = {
    23: (247706213128, 171749895599),   # 24th convergent, UPPER (S29)
    24: (1062790958529, 736898093374),  # 25th convergent, LOWER (S30)
    25: (1310497171657, 908647988973),  # 26th convergent, UPPER (S31, open PR)
    26: (6304779645157, 4371490049266), # 27th convergent, LOWER (S32)
}
for k, (pe, qe) in checks.items():
    assert (p(k), q(k)) == (pe, qe), f"convergent k={k} mismatch: {(p(k),q(k))} vs {(pe,qe)}"
print("Reproduced main's convergents k=23..26 exactly.")

# --- the NEW rung: 28th convergent, k=27 (odd ⟹ UPPER) ---
k = 27
pk, qk = p(k), q(k)
print(f"\n28th convergent (k=27, a27={terms[27]}):  p/q = {pk}/{qk}")
print(f"  p27 = a27*p26 + p25 = {terms[27]}*{p(26)} + {p(25)} = {pk}")
print(f"  q27 = a27*q26 + q25 = {terms[27]}*{q(26)} + {q(25)} = {qk}")

# Exact-integer cube sign: UPPER bound requires (p/q)³ > 3, i.e. p³ − 3q³ > 0.
cube_diff = pk ** 3 - 3 * qk ** 3
print(f"\n  p27³ − 3·q27³ = {cube_diff}")
assert k % 2 == 1, "k must be odd for an UPPER bound under this CF parity"
assert cube_diff > 0, "FAIL: not a valid UPPER bound (p³ − 3q³ ≤ 0)"
print("  ⟹ (p/q)³ > 3  ⟹  cbrt3 < p/q   [valid UPPER bound]")

# relative gap
gap = (Decimal(pk) / Decimal(qk)) - cbrt3
print(f"  relative gap (p/q − ∛3) ≈ {gap:.3e}")
assert gap > 0, "FAIL: p/q is not above ∛3"

# gcd check (convergents are automatically in lowest terms)
import math
assert math.gcd(pk, qk) == 1, "convergent not in lowest terms"
print("\nALL CHECKS PASS.")
