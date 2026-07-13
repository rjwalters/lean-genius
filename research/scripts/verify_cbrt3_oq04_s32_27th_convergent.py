#!/usr/bin/env python3
"""
cube-root-3-irrational-oq-04 — S32 certificate for the 27th CF convergent of ∛3.

Anti-typo discipline (see helpers file): independently RE-DERIVE the partial
quotients aᵢ from a high-precision recomputation of ∛3 (do NOT re-quote a prior
sketch tail), then verify (a) the convergent recursion against the previous two
convergents and (b) the EXACT integer cube-side direction that the Lean proof
relies on.

27th convergent = idx 26 (0-indexed), a₂₆ = 4, a LOWER bound (even index):

    6304779645157 / 4371490049266  <  ∛3      ⟺   p³ < 3 q³.
"""
from mpmath import mp, mpf, floor, cbrt
import math

mp.dps = 400
x = cbrt(3)

# Independent CF re-derivation
a = []
y = x
for _ in range(30):
    ai = int(floor(y))
    a.append(ai)
    y = 1 / (y - ai)

# Convergents via the standard recurrence
H = []; K = []
hm1, hm2 = 1, 0
km1, km2 = 0, 1
for ai in a:
    h = ai * hm1 + hm2
    k = ai * km1 + km2
    H.append(h); K.append(k)
    hm2, hm1 = hm1, h
    km2, km1 = km1, k

idx = 26
p, q = H[idx], K[idx]

assert a[24] == 4, f"a24 expected 4, got {a[24]}"
assert a[25] == 1, f"a25 expected 1, got {a[25]}"
assert a[26] == 4, f"a26 expected 4, got {a[26]}"

# Recursion check against 25th (idx24) and 26th (idx25) convergents
assert p == a[26] * H[25] + H[24]
assert q == a[26] * K[25] + K[24]
assert math.gcd(p, q) == 1, "convergent must be in lowest terms"

# This is a LOWER bound (even convergent index) ⟺ exact p³ < 3 q³
p3 = p**3
tq3 = 3 * q**3
assert p3 < tq3, "cube-side direction wrong for a lower bound"

print(f"a₂₄,a₂₅,a₂₆        = {a[24]}, {a[25]}, {a[26]}")
print(f"25th conv (idx24)  = {H[24]}/{K[24]}")
print(f"26th conv (idx25)  = {H[25]}/{K[25]}")
print(f"27th conv (idx26)  = {p}/{q}")
print(f"  p₂₆ = 4·{H[25]} + {H[24]} = {p}")
print(f"  q₂₆ = 4·{K[25]} + {K[24]} = {q}")
print(f"p³                 = {p3}")
print(f"3·q³               = {tq3}")
print(f"3·q³ − p³          = {tq3 - p3}  (>0 ⟹ lower bound, strict)")
print(f"(p/q)³ vs 3        : {mpf(p)/q < x} (fraction < ∛3)")
print(f"relative gap       ≈ {mp.nstr((x - mpf(p)/q)/x, 4)}")
print("ALL CHECKS PASSED")
