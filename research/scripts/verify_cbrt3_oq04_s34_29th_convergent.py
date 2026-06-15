#!/usr/bin/env python3
"""
cube-root-3-irrational-oq-04 — S34 certificate for the 29th CF convergent of ∛3.

Anti-typo discipline (see helpers file): independently RE-DERIVE the partial
quotients aᵢ from a high-precision recomputation of ∛3 (do NOT re-quote a prior
sketch tail), then verify (a) the convergent recursion against the previous two
convergents and (b) the EXACT integer cube-side direction that the Lean proof
relies on.

29th convergent = idx 28 (0-indexed), a₂₈ = ?, a LOWER bound (even index):

    p / q  <  ∛3      ⟺   p³ < 3 q³.

The 28th convergent (idx 27, a₂₇) is itself only in open PRs #24802/#24809;
this certificate recomputes BOTH the 28th and the 29th convergents from the CF
recurrence so the 29th rung stands on independently re-derived integers, not on
an unmerged sketch.
"""
from mpmath import mp, mpf, floor, cbrt
import math

mp.dps = 500
x = cbrt(3)

# Independent CF re-derivation
a = []
y = x
for _ in range(32):
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

# Sanity-anchor the known merged tail (27th convergent, idx26, a26=4)
assert a[24] == 4, f"a24 expected 4, got {a[24]}"
assert a[25] == 1, f"a25 expected 1, got {a[25]}"
assert a[26] == 4, f"a26 expected 4, got {a[26]}"
assert H[26] == 6304779645157 and K[26] == 4371490049266, \
    f"27th convergent drift: {H[26]}/{K[26]}"

a27 = a[27]
a28 = a[28]
print(f"a₂₇ (28th rung)    = {a27}")
print(f"a₂₈ (29th rung)    = {a28}")

# 28th convergent (idx 27)
p27, q27 = H[27], K[27]
assert p27 == a[27] * H[26] + H[25]
assert q27 == a[27] * K[26] + K[25]
assert math.gcd(p27, q27) == 1

# 29th convergent (idx 28) — the new rung
idx = 28
p, q = H[idx], K[idx]
assert p == a[28] * H[27] + H[26], "29th recursion (p) failed"
assert q == a[28] * K[27] + K[26], "29th recursion (q) failed"
assert math.gcd(p, q) == 1, "convergent must be in lowest terms"

# idx 28 is EVEN ⟹ LOWER bound ⟺ exact p³ < 3 q³
p3 = p**3
tq3 = 3 * q**3
assert p3 < tq3, "cube-side direction wrong for a lower bound"

print(f"27th conv (idx26)  = {H[26]}/{K[26]}")
print(f"28th conv (idx27)  = {p27}/{q27}")
print(f"  p₂₇ = {a27}·{H[26]} + {H[25]} = {p27}")
print(f"  q₂₇ = {a27}·{K[26]} + {K[25]} = {q27}")
print(f"29th conv (idx28)  = {p}/{q}")
print(f"  p₂₈ = {a28}·{p27} + {H[26]} = {p}")
print(f"  q₂₈ = {a28}·{q27} + {K[26]} = {q}")
print(f"p³                 = {p3}")
print(f"3·q³               = {tq3}")
print(f"3·q³ − p³          = {tq3 - p3}  (>0 ⟹ lower bound, strict)")
print(f"(p/q)³ vs 3        : {mpf(p)/q < x} (fraction < ∛3)")
print(f"relative gap       ≈ {mp.nstr((x - mpf(p)/q)/x, 4)}")
print("ALL CHECKS PASSED")
