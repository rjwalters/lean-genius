#!/usr/bin/env python3
"""Certify the S26 twentieth-convergent UPPER bound for ∛3.

Re-derives (does NOT plug in) the continued-fraction prefix of ∛3 to 320 digits,
confirms a₁₉ = 4 and the twentieth convergent p₁₉/q₁₉ = 6756947488/4685005721,
and verifies the exact integer cube inequality that the Lean theorem
`cbrt3_lt_..._over_...` discharges by `norm_num`:

    ∛3 < p/q   ⇔   3 < (p/q)³   ⇔   3·q³ < p³   (for p, q > 0).

Exits non-zero on any mismatch.
"""
import sys

from mpmath import mp, cbrt, floor

mp.dps = 360
x = cbrt(3)

# Re-derive the simple continued fraction prefix a₀..a₁₉.
a = []
y = x
for _ in range(20):
    f = int(floor(y))
    a.append(f)
    y = 1 / (y - f)

expected_prefix = [1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, 4, 2, 6, 4, 4]
assert a == expected_prefix, f"CF prefix mismatch: {a} != {expected_prefix}"
assert a[19] == 4, f"a19 expected 4, got {a[19]}"

# Build convergents p_k/q_k from the a-sequence.
p = [a[0], a[1] * a[0] + 1]
q = [1, a[1]]
for k in range(2, len(a)):
    p.append(a[k] * p[-1] + p[-2])
    q.append(a[k] * q[-1] + q[-2])

# Twentieth convergent = index 19 (0-based). Odd index => UPPER side.
P, Q = p[19], q[19]
assert (P, Q) == (6756947488, 4685005721), f"20th convergent mismatch: {P}/{Q}"

# Sanity: prior rungs match what the Lean file already contains.
assert (p[18], q[18]) == (1593368375, 1104779927)  # 19th, lower, on main
assert (p[17], q[17]) == (383473988, 265886013)    # 18th, upper

# The exact inequality the Lean `norm_num` proves: 3·q³ < p³  (upper bound).
P3 = P ** 3
Q3 = 3 * Q ** 3
assert P3 == 308497487520026079326651318272, P3
assert Q3 == 308497487520026079307507261083, Q3
assert P3 > Q3, "cube inequality failed: not an upper bound"
gap = P3 - Q3
assert gap == 19144057189, gap

# Independent high-precision cross-check (float64 cannot resolve a ~1e-20 gap).
from mpmath import mpf

assert x < mpf(P) / mpf(Q), "high-precision check: bound is not above ∛3"

print("OK: a19 = 4")
print(f"OK: 20th convergent (upper) = {P}/{Q}")
print(f"OK: {P}^3 = {P3}")
print(f"OK: 3*{Q}^3 = {Q3}")
print(f"OK: p^3 > 3 q^3 (upper bound), gap = +{gap}")
sys.exit(0)
