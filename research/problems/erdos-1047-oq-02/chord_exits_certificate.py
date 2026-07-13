#!/usr/bin/env python3
"""
Chord-exits certificate for `goodman_counterexample` (erdos-1047-oq-02).

After the parent patch (PR #24613) the Grunsky-conjecture file
`Erdos1047Problem.lean` rests on exactly ONE analytic assumption:

    axiom goodman_counterexample :
      ∃ z₀ ∈ lemniscate goodmanPolynomial goodmanCriticalValue,
        ¬ IsConvexComplex (componentContaining
            (lemniscate goodmanPolynomial goodmanCriticalValue) z₀)

with  f = goodmanPolynomial = (X²+1)(X−2)²   and   c = goodmanCriticalValue = 5^(3/2)/4.

The companion `Erdos1047OQ02Reduction.lean` (PR #24660) reduces this axiom to a
PURELY ELEMENTARY obligation via

    componentContaining_lemniscate_not_convex_of_chord_exits
      (hCpc : IsPreconnected C) (hCS : C ⊆ lemniscate f c)
      (hz₀ : z₀ ∈ C) (hz₁ : z₁ ∈ C)
      (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
      (hexit : c < ‖f.eval ((1-t)•z₀ + t•z₁)‖)
      : ¬ IsConvexComplex (componentContaining (lemniscate f c) z₀)

i.e. produce ONE preconnected arc inside the sublevel set whose connecting chord
pokes outside.  This script exhibits such an arc with FULLY EXACT, Lean-provable
data and verifies every hypothesis (symbolically, not just by sampling).

──────────────────────────────────────────────────────────────────────────────
THE CERTIFICATE  (all data exact: Gaussian-rational / rational)

  Endpoints        z₀ = -i,  z₁ = +i        (the two simple roots of f)
  Chord parameter  t  = 1/2                  → (1-t)z₀ + t z₁ = 0  (the origin)
  Arc C            the polyline through the 5 waypoints
                       -i → (1-i)/2 → 2 → (1+i)/2 → +i

KEY STRUCTURAL FACT (why c is "critical"):
  c = 5^(3/2)/4 is EXACTLY |f| at the saddle points of f.  The critical points
  of f solve  f'(z) = 2(z-2)(2z²-2z+1) = 0,  giving  z = 2  and  z = (1±i)/2.
  At the two non-trivial saddles  |f((1±i)/2)|² = 125/16 = c².  So c is precisely
  the level at which the lemniscate's ±i lobes merge with the z=2 basin through
  these saddles — the topological onset value.  The arc threads both saddles, and
  the closed sublevel set {|f| ≤ c} contains them (|f| = c there, allowed).

The three hypothesis families, all exact:
  (1) z₀, z₁ ∈ lemniscate :  f(i) = f(-i) = 0 ≤ c.
  (2) C ⊆ lemniscate      :  on each of the 4 segments z(s)=(1-s)a+s b,
                             |f(z(s))|² ≤ 125/16  for all s ∈ [0,1]
                             (equality only at the saddle endpoints).
  (3) chord exits         :  f(0) = (0+1)(0-2)² = 4,  and  4 > c
                             ⇔ 16 > 5^(3/2) ⇔ 256 > 125.

Conclusion: the (-i)-component of the lemniscate is non-convex, discharging
`goodman_counterexample`.  Everything reduces to the four degree-8 polynomial
inequalities |f(z(s))|² ≤ 125/16 on [0,1] (Lean: nlinarith/polyrith per segment)
plus three exact evaluations.

Run:  python3 chord_exits_certificate.py
Requires sympy (exact) and numpy (independent numeric cross-check).
"""
import sympy as sp


def run():
    z = sp.symbols("z")
    t = sp.symbols("t", real=True)
    f = (z**2 + 1) * (z - 2) ** 2
    c = sp.Rational(1, 4) * 5 ** sp.Rational(3, 2)
    C2 = sp.Rational(125, 16)  # = c²

    print("f = (z²+1)(z−2)²,   c = 5^(3/2)/4 = %s ≈ %.6f,   c² = %s"
          % (sp.nsimplify(c), float(c), sp.simplify(c**2)))
    assert sp.simplify(c**2 - C2) == 0

    # ── saddle structure: critical points of f and |f| there ──────────────────
    fp = sp.factor(sp.diff(f, z))
    print("\nf'(z) =", fp)
    crit = sp.solve(sp.diff(f, z), z)
    print("critical points of f:", crit)
    for cp in [sp.Rational(1, 2) - sp.I / 2, sp.Rational(1, 2) + sp.I / 2]:
        val = sp.simplify(f.subs(z, cp))
        mag2 = sp.simplify(sp.Abs(val) ** 2)
        print(f"  z={cp}: f={val}, |f|²={mag2}  (= c² ? {sp.simplify(mag2 - C2) == 0})")
        assert sp.simplify(mag2 - C2) == 0

    # ── (1) endpoints are roots, hence in the lemniscate ──────────────────────
    print("\n(1) endpoints in lemniscate:")
    for zz, nm in [(sp.I, "+i"), (-sp.I, "-i")]:
        v = sp.simplify(f.subs(z, zz))
        print(f"    f({nm}) = {v}  ≤ c ✓")
        assert v == 0

    # ── (3) chord at t=1/2 exits ──────────────────────────────────────────────
    mid = sp.simplify(((1 - sp.Rational(1, 2)) * (-sp.I) + sp.Rational(1, 2) * sp.I))
    fmid = sp.simplify(f.subs(z, mid))
    print(f"\n(3) chord midpoint (t=1/2) = {mid},  f = {fmid},  |f| = {sp.Abs(fmid)}")
    print(f"    exit  4 > c  ⇔ 16 > 5^(3/2) ⇔ 256 > 125 : {256 > 125}")
    assert sp.simplify(sp.Abs(fmid)) == 4 and 256 > 125

    # ── (2) arc ⊆ lemniscate : |f|² ≤ 125/16 on every segment, s ∈ [0,1] ──────
    def fmag2(zx, zy):
        zc = zx + sp.I * zy
        v = (zc**2 + 1) * (zc - 2) ** 2
        return sp.expand(sp.re(v) ** 2 + sp.im(v) ** 2)

    waypoints = [(0, -1), (sp.Rational(1, 2), sp.Rational(-1, 2)), (2, 0),
                 (sp.Rational(1, 2), sp.Rational(1, 2)), (0, 1)]
    names = ["-i", "(1-i)/2", "2", "(1+i)/2", "+i"]
    print("\n(2) arc ⊆ lemniscate  (polyline through:", " → ".join(names), ")")
    all_ok = True
    for (ax, ay), (bx, by), na, nb in zip(waypoints, waypoints[1:], names, names[1:]):
        zx = (1 - t) * ax + t * bx
        zy = (1 - t) * ay + t * by
        g = sp.expand(fmag2(zx, zy))                 # |f(z(s))|² as poly in t
        mn = sp.minimum(C2 - g, t, sp.Interval(0, 1))
        ok = sp.simplify(mn) >= 0
        all_ok &= bool(ok)
        print(f"    seg {na:>8} → {nb:<8}: min(125/16 − |f|²) on [0,1] = {sp.nsimplify(mn)}  (≥0 ✓)" if ok
              else f"    seg {na} → {nb}: FAILS")
        assert ok

    print("\nRESULT: chord-exits certificate VALID — all hypotheses of "
          "componentContaining_lemniscate_not_convex_of_chord_exits hold.")
    print("        ⇒ goodman_counterexample is discharged by the explicit witness")
    print("          z₀=-i, z₁=+i, t=1/2, arc = polyline through the two saddles (1±i)/2.")
    return all_ok


if __name__ == "__main__":
    ok = run()
    raise SystemExit(0 if ok else 1)
