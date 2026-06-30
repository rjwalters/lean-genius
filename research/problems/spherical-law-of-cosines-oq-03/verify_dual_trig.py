#!/usr/bin/env python3
"""
erdos / spherical-law-of-cosines-oq-03 — EXACT symbolic verification of the
literal trig dual law of cosines (the OQ-03 deliverable), upgrading S1's
"verified by hand + numerics" to a closed symbolic proof, and pinning the exact
`linear_combination` certificate for the Lean drop-in.

Normal-form angle data for a spherical triangle (side cosines ca,cb,cc; side
sines sa,sb,sc):
    cos A = (ca - cb cc)/(sb sc),   cos B = (cb - ca cc)/(sa sc),
    cos C = (cc - ca cb)/(sa sb),
    sin A sin B = tp2/(sa sb sc^2),  tp2 = 1 - ca^2 - cb^2 - cc^2 + 2 ca cb cc.

Claim (dual / polar law of cosines):   cos C = - cos A cos B + sin A sin B cos c.

Result: (LHS - RHS) has numerator (over the common denominator sa sb sc^2)
            (cc - ca cb) * (1 - cc^2 - sc^2),
so it vanishes IDENTICALLY once  sc^2 = 1 - cc^2  (the side-Pythagorean
sin^2 c = 1 - cos^2 c).  Hence the Lean proof, after `field_simp`, closes with
            linear_combination (cc - ca*cb) * hsc2
(up to the denominator-scaling factor field_simp introduces).
"""

import sympy as sp

ca, cb, cc, sa, sb, sc = sp.symbols("ca cb cc sa sb sc", real=True)

cA = (ca - cb * cc) / (sb * sc)
cB = (cb - ca * cc) / (sa * sc)
cC = (cc - ca * cb) / (sa * sb)
tp2 = 1 - ca**2 - cb**2 - cc**2 + 2 * ca * cb * cc
sAsB = tp2 / (sa * sb * sc**2)

lhs = cC
rhs = -cA * cB + sAsB * cc

num, den = sp.fraction(sp.together(lhs - rhs))
num = sp.expand(num)
print("common denominator :", den)
print("numerator (expanded):", num)

# the closed factorization
factored = sp.factor(num)
print("numerator factored :", factored)
expected = (cc - ca * cb) * (sc**2 + cc**2 - 1)
print("matches (cc-ca*cb)*(sc^2+cc^2-1) = (cc-ca*cb)*(sc^2-(1-cc^2))?",
      sp.simplify(num - expected) == 0)

# under sc^2 = 1 - cc^2 the numerator is identically zero
print("numerator | sc^2=1-cc^2  =", sp.simplify(num.subs(sc**2, 1 - cc**2)))

# cross-check: the cleared identity (dual_law_cleared) already in the Lean file
cleared = (cc - ca * cb) * sc**2 - (-(ca - cb * cc) * (cb - ca * cc) + tp2 * cc)
print("dual_law_cleared residual | sc^2=1-cc^2 =",
      sp.simplify(cleared.subs(sc**2, 1 - cc**2)))

assert sp.simplify(num - expected) == 0
assert sp.simplify(num.subs(sc**2, 1 - cc**2)) == 0
assert sp.simplify(cleared.subs(sc**2, 1 - cc**2)) == 0
print("\nALL EXACT CHECKS PASS — dual_law_trig is a symbolic identity mod sc^2=1-cc^2.")
