#!/usr/bin/env python3
"""
Exact (symbolic) certificate for the axiom-discharge witness of
`feuerbachs-theorem-oq-02-murakami` (step S10).

Parent axiom (FeuerbachsTheoremOQ02.lean:581):
    feuerbach_3d_fails_general : ∃ T, dot3(AB,CD) ≠ 0 ∧
        ¬ spheresInternallyTangent N₂₄ I (R/3) r

Witness:  T1 = A(0,0,0), B(1,0,0), C(0,1,0), D(1,1,1)  (non-orthocentric).

This script reproduces, in EXACT arithmetic, every quantity used by the Lean
discharge target `StatementOnly_FeuerbachOQ02_FailsGeneralWitness.lean`, and
checks the final reduction of the non-tangency to the single three-surd
inequality

    72 - 30*sqrt3 - 12*sqrt2 + 12*sqrt6  != 0     (in fact > 0).

All definitions are transcribed verbatim from FeuerbachsTheoremOQ02.lean.
"""
import sympy as sp

s2, s3, s6 = sp.sqrt(2), sp.sqrt(3), sp.sqrt(6)

A = sp.Matrix([0, 0, 0])
B = sp.Matrix([1, 0, 0])
C = sp.Matrix([0, 1, 0])
D = sp.Matrix([1, 1, 1])

def vec3(P, Q):
    return Q - P

def dot3(u, v):
    return u.dot(v)

def cross3(u, v):
    return u.cross(v)

results = []
def check(name, cond):
    results.append((name, bool(cond)))
    print(f"  [{'PASS' if cond else 'FAIL'}] {name}")

# --- nondegeneracy / non-orthocentricity ---
u, v, w = vec3(A, B), vec3(A, C), vec3(A, D)
sv6 = dot3(u, cross3(v, w))
check("signedVolume6 = 1 (nondegenerate)", sv6 == 1)
AB, CD = vec3(A, B), vec3(C, D)
check("dot3(AB,CD) = 1 != 0 (non-orthocentric)", dot3(AB, CD) == 1 and dot3(AB, CD) != 0)

V = sp.Abs(sv6) / 6
check("volume V = 1/6", V == sp.Rational(1, 6))

# --- circumcenter via Cramer (verbatim formula) ---
det = sv6
P = (dot3(u, u) * cross3(v, w) + dot3(v, v) * cross3(w, u) + dot3(w, w) * cross3(u, v)) / (2 * det)
O = A + P
check("circumcenter O = (1/2,1/2,1/2)", O == sp.Matrix([sp.Rational(1, 2)] * 3))
R = sp.sqrt(dot3(O - A, O - A))
check("circumradius R = sqrt(3)/2", sp.simplify(R - s3 / 2) == 0)
R24 = sp.simplify(R / 3)
check("twentyFourPointRadius R/3 = sqrt(3)/6", sp.simplify(R24 - s3 / 6) == 0)

# --- centroid, monge, N24 ---
G = (A + B + C + D) / 4
check("centroid G = (1/2,1/2,1/4)", G == sp.Matrix([sp.Rational(1, 2), sp.Rational(1, 2), sp.Rational(1, 4)]))
M = 4 * G - 3 * O
check("mongePoint M = 4G-3O = (1/2,1/2,-1/2)", M == sp.Matrix([sp.Rational(1, 2), sp.Rational(1, 2), sp.Rational(-1, 2)]))
N24 = (O + M) / 2
check("N24 = midpoint(O,M) = (1/2,1/2,0)  [RATIONAL]",
      N24 == sp.Matrix([sp.Rational(1, 2), sp.Rational(1, 2), 0]))

# --- face areas, surface area, inradius, incenter (verbatim) ---
def area(p, q, r):
    n = cross3(q - p, r - p)
    return sp.sqrt(dot3(n, n)) / 2

sA, sB, sC, sD = area(B, C, D), area(A, C, D), area(A, B, D), area(A, B, C)
check("faceAreas = (sqrt3/2, sqrt2/2, sqrt2/2, 1/2)",
      sp.simplify(sA - s3/2) == 0 and sp.simplify(sB - s2/2) == 0
      and sp.simplify(sC - s2/2) == 0 and sD == sp.Rational(1, 2))
S = sp.simplify(sA + sB + sC + sD)
Delta = 1 + s3 + 2 * s2
check("surfaceArea S = (1+sqrt3+2sqrt2)/2 = Delta/2", sp.simplify(S - Delta / 2) == 0)
r = sp.simplify(3 * V / S)
check("inradius r = 1/(1+sqrt3+2sqrt2) = 1/Delta", sp.simplify(r - 1 / Delta) == 0)

tot = S
I = sp.Matrix([
    sp.simplify((sA*A[k] + sB*B[k] + sC*C[k] + sD*D[k]) / tot) for k in range(3)
])
check("incenter I = ((1+sqrt2)/Delta, (1+sqrt2)/Delta, 1/Delta)",
      sp.simplify(I[0] - (1 + s2)/Delta) == 0 and sp.simplify(I[1] - (1 + s2)/Delta) == 0
      and sp.simplify(I[2] - 1/Delta) == 0)

# --- the non-tangency: dist(N24,I) != |R/3 - r| ---
d2 = sp.simplify(dot3(N24 - I, N24 - I))           # dist3_sq
check("dist(N24,I)^2 = (3 - sqrt3)/Delta^2",
      sp.simplify(d2 - (3 - s3) / Delta**2) == 0)
rhs2 = sp.simplify((R24 - r)**2)
check("(R/3 - r)^2 = (-3+sqrt3+2sqrt6)^2/(36 Delta^2)",
      sp.simplify(rhs2 - (-3 + s3 + 2*s6)**2 / (36 * Delta**2)) == 0)

# squared separation, cleared by the positive factor 36*Delta^2
sep = sp.expand(36 * (3 - s3) - (-3 + s3 + 2*s6)**2)
target = 72 - 30*s3 - 12*s2 + 12*s6
check("36*Delta^2*(dist^2 - (R/3-r)^2) = 72 - 30sqrt3 - 12sqrt2 + 12sqrt6",
      sp.simplify(sep - target) == 0)
check("three-surd numerator != 0 (in fact > 0)", sp.simplify(target) != 0 and float(target) > 0)
check("Delta = 1+sqrt3+2sqrt2 > 0 (separating factor positive)", float(Delta) > 0)

# direct (un-squared) sanity
dist = sp.sqrt(d2)
rhs = sp.Abs(R24 - r)
check("DIRECT: dist(N24,I) != |R/3 - r| (gap ~ %.6f)" % float(dist - rhs),
      sp.simplify(dist - rhs) != 0)

# --- two orthocentric controls must NOT witness (dot3(AB,CD)=0) ---
for name, (a, b, c, d) in {
    "T0 trirectangular (2,0,0),(0,3,0),(0,0,6),0": (sp.Matrix([2,0,0]), sp.Matrix([0,3,0]), sp.Matrix([0,0,6]), sp.Matrix([0,0,0])),
    "unit corner (0,0,0),(1,0,0),(0,1,0),(0,0,1)": (sp.Matrix([0,0,0]), sp.Matrix([1,0,0]), sp.Matrix([0,1,0]), sp.Matrix([0,0,1])),
}.items():
    AB2, CD2 = b - a, d - c
    check(f"control {name}: dot3(AB,CD)=0 (orthocentric, NOT a witness)", dot3(AB2, CD2) == 0)

# ============================================================
# S11 EXTENSION: exact intermediate forms for the Lean discharge
# of `witnessT1_fails` (transcribed tactic targets).
# ============================================================
print()
print("=== S11: Lean-shaped intermediate identities ===")
a, b = sp.symbols('a b', positive=True)   # a = sqrt2, b = sqrt3
Dl = 1 + b + 2*a                            # Delta

# hd: dist3_sq(N24,I) with I=((1+a)/Δ,(1+a)/Δ,1/Δ), N24=(1/2,1/2,0)
lhs_hd = ((1+a)/Dl - sp.Rational(1,2))**2 * 2 + (1/Dl - 0)**2
print("[%s] hd: dist3_sq = ((1-b)^2+2)/(2*Delta^2)" %
      ("PASS" if sp.simplify(lhs_hd - ((1-b)**2+2)/(2*Dl**2))==0 else "FAIL"))

# he: (R24-r)^2 = (b*Δ-6)^2/(36 Δ^2),  R24=b/6, r=1/Δ
lhs_he = (b/6 - 1/Dl)**2
print("[%s] he: (R24-r)^2 = (b*Delta-6)^2/(36*Delta^2)" %
      ("PASS" if sp.simplify(lhs_he - (b*Dl-6)**2/(36*Dl**2))==0 else "FAIL"))

# hid linear_combination check:  L - R - (ca*(a^2-2)+cb*(b^2-3)) == 0  (ring identity)
L = 18*((1-b)**2+2) - (b*Dl-6)**2
R = 72 - 30*b - 12*a + 12*(a*b)
ca = -4*b**2
cb = -4*a*b - 4*a - b**2 - 2*b + 18
print("[%s] hid linear_combination (-4*b^2)*ha2 + (-4*a*b-4*a-b^2-2*b+18)*hb2" %
      ("PASS" if sp.expand(L - R - (ca*(a**2-2) + cb*(b**2-3)))==0 else "FAIL"))

# final cleared inequality direction: (b*Δ-6)^2*(2Δ^2) < ((1-b)^2+2)*(36 Δ^2)  <=> (b*Δ-6)^2 < 18((1-b)^2+2)
import math
av, bv = math.sqrt(2), math.sqrt(3)
print("[%s] numeric: (b*Δ-6)^2=%.4f < 18((1-b)^2+2)=%.4f" % (
    "PASS" if (bv*(1+bv+2*av)-6)**2 < 18*((1-bv)**2+2) else "FAIL",
    (bv*(1+bv+2*av)-6)**2, 18*((1-bv)**2+2)))
print("S11 intermediate identities: done")

print()
ok = all(p for _, p in results)
print("CERTIFICATE: " + ("ALL CHECKS PASS" if ok else "FAILURES PRESENT"))
raise SystemExit(0 if ok else 1)
