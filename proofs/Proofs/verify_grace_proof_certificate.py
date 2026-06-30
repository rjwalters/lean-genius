#!/usr/bin/env python3
"""
Proof certificate for `grace_feuerbach_trirectangular`
(feuerbachs-theorem-oq-02-murakami, step S9).

This is NOT a re-verification of the closed FORM (that is done in
`research/.../verify_grace_trirectangular.py`, PR #24122). It certifies the
exact Lean *tactic* that discharges the `sorry` in
`StatementOnly_FeuerbachOQ02Murakami_GraceTrirectangular.lean`, so the proof can
be dropped in verbatim once Docker/Aristotle return.

Trirectangular tetrahedron: D=(0,0,0), A=(a,0,0), B=(0,b,0), C=(0,0,c), a,b,c>0.
Grace sphere through A,B,C, internally tangent to insphere and D-exsphere:
    Θ = ((a+b)(a+c), (a+b)(b+c), (a+c)(b+c)) / (2σ),  σ = a+b+c
    R = (a²+b²+c²+ab+bc+ca) / (2σ)
    ρin/ρex = (ab+bc+ca ∓ t) / (2σ),   t = √(a²b²+b²c²+c²a²)

What is certified here (each is exactly the obligation Lean's tactic must meet):

  Incidence (3 goals, Lean: `field_simp; ring`):
    The residual `‖Θ−A‖² − R²` (etc.) is the ZERO rational function — but it is
    NOT a formal identity in u=(a+b+c)⁻¹ (it carries u⁰,u¹,u² terms), so a bare
    `ring` cannot close it; `field_simp` (using σ≠0) is required first.

  Tangency (2 goals, Lean: `linear_combination (1/(2σ²)) * ht`):
    Eₜ − (1/(2σ²))·(t² − K) ≡ 0 as a FORMAL field identity (pure u² — every term
    carries u²), where K=a²b²+b²c²+c²a² and ht : t² = K. Hence `linear_combination
    (1/(2*(a+b+c)^2)) * ht` closes it WITHOUT field_simp, with the SAME coefficient
    for both insphere and D-exsphere (the odd-in-t part of Eₜ is identically 0).
"""
import sympy as sp

a, b, c, t, u = sp.symbols('a b c t u', positive=True)
sig = a + b + c
qx = (a + b) * (a + c) / (2 * sig)
qy = (a + b) * (b + c) / (2 * sig)
qz = (a + c) * (b + c) / (2 * sig)
R = (a**2 + b**2 + c**2 + a*b + b*c + c*a) / (2 * sig)
P = a*b + b*c + c*a
rin = (P - t) / (2 * sig)
rex = (P + t) / (2 * sig)
K = a**2*b**2 + b**2*c**2 + c**2*a**2          # t² = K
C = 1 / (2 * sig**2)                            # the linear_combination coefficient

ok = True


def check(name, cond):
    global ok
    status = "PASS" if cond else "FAIL"
    if not cond:
        ok = False
    print(f"  [{status}] {name}")
    return cond


print("== Incidence (Lean: field_simp; ring) ==")
inc = {
    "‖Θ−A‖² = R²": (qx - a)**2 + qy**2 + qz**2 - R**2,
    "‖Θ−B‖² = R²": qx**2 + (qy - b)**2 + qz**2 - R**2,
    "‖Θ−C‖² = R²": qx**2 + qy**2 + (qz - c)**2 - R**2,
}
for nm, e in inc.items():
    check(f"{nm}: residual ≡ 0 (rational identity)", sp.simplify(e) == 0)

# Incidence is NOT a formal u-identity. Rebuild with u (= σ⁻¹) as a FREE symbol
# (qx = (a+b)(a+c)·u/2, …) and show the residual, as a polynomial in u, has a
# nonzero coefficient at some u^k with k<2 — so a bare `ring` (which treats u as
# an opaque atom with no relation u·σ=1) cannot close it; `field_simp` is needed.
qxu = (a + b) * (a + c) * u / 2
qyu = (a + b) * (b + c) * u / 2
qzu = (a + c) * (b + c) * u / 2
Ru = (a**2 + b**2 + c**2 + a*b + b*c + c*a) * u / 2
eA_u = sp.Poly(sp.expand((qxu - a)**2 + qyu**2 + qzu**2 - Ru**2), u)
nonhom = any(eA_u.coeff_monomial(u**k) != 0 for k in (0, 1))
check("incidence carries u⁰/u¹ terms (so bare `ring` fails; field_simp needed)", nonhom)

print("== Tangency (Lean: linear_combination (1/(2σ²)) * ht) ==")
Ein = (qx - rin)**2 + (qy - rin)**2 + (qz - rin)**2 - (R - rin)**2
Eex = (qx - rex)**2 + (qy - rex)**2 + (qz - rex)**2 - (R - rex)**2
check("insphere:  Eₜ − C·(t²−K) ≡ 0  (linear_combination closes)",
      sp.simplify(Ein - C * (t**2 - K)) == 0)
check("D-exsphere: Eₜ − C·(t²−K) ≡ 0  (same coefficient C=1/(2σ²))",
      sp.simplify(Eex - C * (t**2 - K)) == 0)

# Odd-in-t (surd) part of each Eₜ numerator is identically zero — this is WHY one
# sphere is tangent to BOTH members of the homothety pair and Θ,R stay rational.
for nm, E in (("insphere", Ein), ("D-exsphere", Eex)):
    num = sp.together(E).as_numer_denom()[0]
    pol = sp.Poly(num, t)
    coeff_t1 = pol.coeff_monomial(t)
    check(f"{nm}: coefficient of t¹ ≡ 0 (surd cancellation)", sp.simplify(coeff_t1) == 0)

# Tangency residual IS a pure u² identity (no field_simp needed): rebuild with u
# (= σ⁻¹) free and Cu = u²/2, then confirm Ein − Cu·(t²−K) is the ZERO polynomial
# in a,b,c,t,u — exactly what ring1 inside `linear_combination` verifies.
rinu = (P - t) * u / 2
Cu = u**2 / 2
Ein_u = (qxu - rinu)**2 + (qyu - rinu)**2 + (qzu - rinu)**2 - (Ru - rinu)**2
res_u = sp.expand(Ein_u - Cu * (t**2 - K))
check("tangency residual ≡ 0 as a FORMAL identity in u=(a+b+c)⁻¹ (no field_simp)",
      res_u == 0)

print("== Numeric spot-checks (T0 and generic triples) ==")
for (av, bv, cv) in [(2, 3, 6), (sp.Rational(3, 2), sp.Rational(27, 10), sp.Rational(41, 10)), (5, 7, 11)]:
    tv = sp.sqrt(av**2*bv**2 + bv**2*cv**2 + cv**2*av**2)
    subs = {a: av, b: bv, c: cv, t: tv}
    vals = [sp.nsimplify(e.subs(subs)) for e in
            [inc["‖Θ−A‖² = R²"], inc["‖Θ−B‖² = R²"], inc["‖Θ−C‖² = R²"],
             Ein, Eex]]
    allz = all(sp.simplify(v) == 0 for v in vals)
    check(f"(a,b,c)=({av},{bv},{cv}): all 5 identities hold", allz)
    if (av, bv, cv) == (2, 3, 6):
        check("T0 centre Θ = (40,45,72)/22",
              [sp.nsimplify(q.subs(subs)) for q in (qx, qy, qz)] ==
              [sp.Rational(40, 22), sp.Rational(45, 22), sp.Rational(72, 22)])
        check("T0 radius R = 85/22", sp.nsimplify(R.subs(subs)) == sp.Rational(85, 22))

print()
print("CERTIFICATE:", "ALL CHECKS PASS" if ok else "FAILURES PRESENT")
import sys
sys.exit(0 if ok else 1)
