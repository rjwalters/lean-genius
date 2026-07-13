#!/usr/bin/env python3
"""Reproducible verification of the S7 Grace/Feuerbach result for the
trirectangular tetrahedron (feuerbachs-theorem-oq-02-murakami).

Trirectangular tetrahedron:
    D = (0,0,0), A = (a,0,0), B = (0,b,0), C = (0,0,c),  a,b,c > 0.

Claimed closed forms (S7):
    sigma = a+b+c
    P     = a*b + b*c + c*a
    q     = sqrt(a^2 b^2 + b^2 c^2 + c^2 a^2)          (the surd)
    rho_in  = (P - q) / (2 sigma)        insphere radius
    rho_Dex = (P + q) / (2 sigma)        D-exsphere radius
    Theta = ((a+b)(a+c), (a+b)(b+c), (a+c)(b+c)) / (2 sigma)   Grace centre
    R     = (a^2 + b^2 + c^2 + a b + b c + c a) / (2 sigma)    Grace radius
    G_pencil = a b c / sigma                    pencil constant
Tangency identities (both internal):
    |Theta - I| = R - rho_in  = (a^2+b^2+c^2 + q)/(2 sigma)
    |Theta - E| = R - rho_Dex = (a^2+b^2+c^2 - q)/(2 sigma)
and Grace sphere passes through A,B,C.

Run: python3 verify_grace_trirectangular.py
Requires sympy. Exits 0 iff every identity checks symbolically.
"""
import sympy as sp

a, b, c = sp.symbols('a b c', positive=True)
sigma = a + b + c
P = a*b + b*c + c*a
q = sp.sqrt(a**2*b**2 + b**2*c**2 + c**2*a**2)

D = sp.Matrix([0, 0, 0])
A = sp.Matrix([a, 0, 0])
B = sp.Matrix([0, b, 0])
C = sp.Matrix([0, 0, c])

ok = True
def check(name, expr_zero):
    global ok
    val = sp.simplify(expr_zero)
    if isinstance(val, sp.MatrixBase):
        passed = all(sp.simplify(e) == 0 for e in val)
        shown = "Matrix(0)" if passed else val
    else:
        passed = val == 0
        shown = val
    ok = ok and passed
    print(f"  [{'OK ' if passed else 'FAIL'}] {name}  -> {shown}")

# --- Incenter / insphere from first principles -------------------------------
# Faces: x=0, y=0, z=0, and the slanted face through A,B,C: x/a+y/b+z/c = 1,
# i.e. (b c) x + (a c) y + (a b) z = a b c, with normal length sqrt(P_sq) where
# P_sq = (bc)^2+(ac)^2+(ab)^2 = q^2.
# Interior tangent-sphere centre on (+,+,+) ray = rho*(1,1,1); the three
# coordinate-plane distances equal rho; distance to slanted plane:
#   |bc*rho + ac*rho + ab*rho - abc| / q = rho.
rho = sp.symbols('rho', positive=True)
slant = sp.Abs(P*rho - a*b*c) / q  # interior branch P*rho < abc
slant_in = (a*b*c - P*rho) / q
sol = sp.solve(sp.Eq(slant_in, rho), rho)
rho_in_derived = sp.simplify(sol[0])
rho_in_claim = (P - q) / (2*sigma)
print("Insphere radius:")
check("rho_in derived == claimed", sp.radsimp(rho_in_derived - rho_in_claim))

# D-exsphere: exterior branch P*rho - abc = q*rho  -> rho_Dex
sol2 = sp.solve(sp.Eq((P*rho - a*b*c)/q, rho), rho)
rho_Dex_derived = sp.simplify(sol2[0])
rho_Dex_claim = (P + q) / (2*sigma)
print("D-exsphere radius:")
check("rho_Dex derived == claimed", sp.radsimp(rho_Dex_derived - rho_Dex_claim))

I = rho_in_claim * sp.Matrix([1, 1, 1])
E = rho_Dex_claim * sp.Matrix([1, 1, 1])

# --- Grace sphere ------------------------------------------------------------
Theta = sp.Matrix([(a+b)*(a+c), (a+b)*(b+c), (a+c)*(b+c)]) / (2*sigma)
R = (a**2 + b**2 + c**2 + a*b + b*c + c*a) / (2*sigma)

print("Grace sphere passes through A, B, C:")
check("|Theta-A|^2 == R^2", sp.expand((Theta-A).dot(Theta-A) - R**2))
check("|Theta-B|^2 == R^2", sp.expand((Theta-B).dot(Theta-B) - R**2))
check("|Theta-C|^2 == R^2", sp.expand((Theta-C).dot(Theta-C) - R**2))

print("Internal tangency to insphere and D-exsphere:")
ti = (a**2 + b**2 + c**2 + q) / (2*sigma)   # R - rho_in
te = (a**2 + b**2 + c**2 - q) / (2*sigma)   # R - rho_Dex
check("R - rho_in == (a^2+b^2+c^2+q)/(2sigma)", sp.radsimp(R - rho_in_claim - ti))
check("R - rho_Dex == (a^2+b^2+c^2-q)/(2sigma)", sp.radsimp(R - rho_Dex_claim - te))
# Compare SQUARED distances (avoids nested-radical simplification); both sides
# are positive, so equality of squares implies |Theta-I| = R - rho_in etc.
dist_TI_sq = sp.expand((Theta - I).dot(Theta - I))   # q**2 auto-reduces to radicand
check("|Theta-I|^2 == (R - rho_in)^2", sp.expand(dist_TI_sq - ti**2))
dist_TE_sq = sp.expand((Theta - E).dot(Theta - E))
check("|Theta-E|^2 == (R - rho_Dex)^2", sp.expand(dist_TE_sq - te**2))
# Both tangencies internal: numerators a^2+b^2+c^2 +/- q are positive, since
# (a^2+b^2+c^2)^2 - q^2 = a^4+b^4+c^4 + (a^2b^2+b^2c^2+c^2a^2) >= 0.
check("(a^2+b^2+c^2)^2 - q^2 >= 0 (so both tangencies internal)",
      sp.expand((a**2+b**2+c**2)**2 - q**2
                - (a**4+b**4+c**4 + a**2*b**2+b**2*c**2+c**2*a**2)))

# --- Pencil constant G = abc/sigma & odd-in-n cancellation -------------------
# Sphere through A,B,C: x^2+y^2+z^2 + Dx+Ey+Fz+G = 0 with
#   D=-(a^2+G)/a, E=-(b^2+G)/b, F=-(c^2+G)/c. Centre = -(D,E,F)/2.
G = sp.symbols('G')
Dc = -(a**2 + G)/a
Ec = -(b**2 + G)/b
Fc = -(c**2 + G)/c
centre = sp.Matrix([-Dc, -Ec, -Fc]) / 2
G_claim = a*b*c / sigma
print("Pencil centre at G=abc/sigma equals Theta:")
check("centre(G=abc/sigma) == Theta",
      sp.simplify((centre.subs(G, G_claim) - Theta)))

# --- T0 = (2,3,6) numeric sanity --------------------------------------------
print("T0=(2,3,6) specialization:")
sub = {a: 2, b: 3, c: 6}
Theta0 = Theta.subs(sub)
R0 = R.subs(sub)
check("Theta(T0) == (40/22,45/22,72/22)",
      sp.Matrix(Theta0) - sp.Matrix([sp.Rational(40,22), sp.Rational(45,22), sp.Rational(72,22)]))
check("R(T0) == 85/22", R0 - sp.Rational(85,22))
check("rho_in(T0) == (18-3sqrt14)/11",
      sp.radsimp(rho_in_claim.subs(sub) - (18 - 3*sp.sqrt(14))/11))
check("rho_Dex(T0) == (18+3sqrt14)/11",
      sp.radsimp(rho_Dex_claim.subs(sub) - (18 + 3*sp.sqrt(14))/11))

# --- Numeric check on an irrational triple (1.5, 2.7, 4.1) -------------------
print("Generic numeric triple (1.5,2.7,4.1):")
subn = {a: sp.Rational(3,2), b: sp.Rational(27,10), c: sp.Rational(41,10)}
TI_n = float(sp.sqrt(dist_TI_sq).subs(subn))
ti_n = float(ti.subs(subn))
TE_n = float(sp.sqrt(dist_TE_sq).subs(subn))
te_n = float(te.subs(subn))
print(f"  |Theta-I|={TI_n:.12f}  R-rho_in={ti_n:.12f}  diff={abs(TI_n-ti_n):.2e}")
print(f"  |Theta-E|={TE_n:.12f}  R-rho_Dex={te_n:.12f}  diff={abs(TE_n-te_n):.2e}")
ok = ok and abs(TI_n-ti_n) < 1e-12 and abs(TE_n-te_n) < 1e-12

print()
print("ALL IDENTITIES VERIFIED" if ok else "VERIFICATION FAILED")
raise SystemExit(0 if ok else 1)
