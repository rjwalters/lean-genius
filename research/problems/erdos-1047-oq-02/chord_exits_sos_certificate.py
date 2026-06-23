#!/usr/bin/env python3
"""
SOS / Bernstein nonnegativity certificate for the four arc-segment inequalities
that discharge `goodman_counterexample` (erdos-1047-oq-02).

This is the *nlinarith-ready* refinement of the existence-only certificate in
`chord_exits_certificate.py`.  That earlier script proved each segment bound
`|f(z(s))|^2 <= 125/16` holds on [0,1] by `sympy.minimum(... ) >= 0`, but a
`minimum`-based proof is opaque to Lean — `nlinarith`/`polyrith` need an explicit
sum-of-nonnegatives witness.  This script produces exactly that witness.

────────────────────────────────────────────────────────────────────────────────
THE DECOMPOSITION

  f = (X^2+1)(X-2)^2,   c = 5^(3/2)/4,   c^2 = 125/16.
  Arc = polyline through  -i -> (1-i)/2 -> 2 -> (1+i)/2 -> +i  (threads the two
  saddles (1±i)/2 where |f| = c exactly).

For each segment a -> b, parametrize z(s) = (1-s)*a + s*b, s in [0,1], and let
  D(s) := 125/16 - |f(z(s))|^2   (a degree-8 real polynomial in s).

Every D(s) factors as

       D(s) = (k/16) * SQ(s) * P(s)

where
  * SQ(s) ∈ { s^2 , (1-s)^2 } is a perfect square vanishing (to order 2) exactly
    at the saddle endpoint of the segment — this captures the *tangency* of |f|
    to the level c (why c is the critical value), and
  * P(s) is a degree-6 cofactor that is STRICTLY POSITIVE on [0,1], certified by
    having ALL-NONNEGATIVE BERNSTEIN COEFFICIENTS:

       P(s) = Σ_{j=0}^{6} b_j * C(6,j) * s^j * (1-s)^(6-j),   every b_j >= 0.

  On [0,1] each Bernstein term s^j (1-s)^(6-j) >= 0, so P(s) >= 0 termwise, hence
  D(s) >= 0 termwise.  This is a *manifest* nonnegativity certificate: in Lean it
  is `nlinarith` fed the products `mul_nonneg (pow_nonneg hs j) (pow_nonneg h1s (6-j))`
  (or `positivity` after rewriting in Bernstein form), with zero search.

SYMMETRY CHECK: the conjugation z -> z̄ swaps the upper/lower lobes, mapping
segment 1 <-> segment 4 and segment 2 <-> segment 3.  Accordingly the Bernstein
coefficient lists of seg1/seg4 and seg2/seg3 are reverses of each other.

────────────────────────────────────────────────────────────────────────────────
LEAN DISCHARGE RECIPE (consumes the registered reduction lemma
`componentContaining_lemniscate_not_convex_of_chord_exits`, PR #24660 / now in
`proofs/Proofs/Erdos1047OQ02Reduction.lean`, build-verified + registered):

  z₀ = -I, z₁ = +I, t = 1/2  (midpoint 0, f(0)=4 > c, the chord exit).
  C  = the 4-segment polyline; IsPreconnected C by `IsPreconnected.union` of the
       four affine-image segments `(fun s => (1-s)•a + s•b) '' Icc 0 1`
       (`isPreconnected_Icc.image`), glued at the shared waypoints.
  C ⊆ lemniscate f c: the 4 segment lemmas below.

  Per-segment lemma shape (s : ℝ) (hs : 0 ≤ s) (h1s : s ≤ 1):
      ‖goodmanPolynomial.eval ((1-s)•a + s•b)‖ ≤ goodmanCriticalValue
    ⟸ square both sides (both ≥0): ‖·‖^2 ≤ 125/16
    ⟸ Complex.normSq expansion: write eval as (Re) + (Im)·I, normSq = Re^2+Im^2,
       both Re,Im degree-4 real polynomials in s (this script prints them),
    ⟸ 125/16 - (Re^2+Im^2) = (k/16)*SQ*P  (the printed polynomial identity, `ring`),
    ⟸ (k/16)*SQ*P ≥ 0  from `sq_nonneg`, `P ≥ 0`,
    ⟸ P ≥ 0 on [0,1]  via the printed Bernstein hint list.

  goodmanCriticalValue = 5^(3/2)/4: handle the rpow once via
    `goodmanCriticalValue^2 = 125/16` (Real.rpow: (5^(3/2))^2 = 5^3 = 125), so all
    segment work stays in ℚ-coefficient polynomial land.

Run:  python3 chord_exits_sos_certificate.py
Requires sympy.  Exit 0 iff every identity + every Bernstein coefficient checks.
"""
import sympy as sp
from math import comb


def bernstein_coeffs(P, t, n):
    """Bernstein coefficients b_j on [0,1] for a degree-<=n poly P(t):
       P = Σ_j b_j C(n,j) t^j (1-t)^(n-j).
       b_j = Σ_{k=0}^{j} C(j,k)/C(n,k) * a_k  where a_k = coeff of t^k."""
    a = [P.coeff_monomial(t**k) for k in range(n + 1)]
    return [sp.nsimplify(sum(sp.Rational(comb(j, k), comb(n, k)) * a[k]
                             for k in range(j + 1))) for j in range(n + 1)]


def run():
    t = sp.symbols("t", real=True)
    C2 = sp.Rational(125, 16)  # = c^2

    # f(x+iy) split into real / imaginary parts (each degree-4 in s once x,y are
    # affine in s); used both to build D(s) and to print the Lean Re/Im targets.
    def re_im(zx, zy):
        zc = zx + sp.I * zy
        v = sp.expand((zc**2 + 1) * (zc - 2) ** 2)
        return sp.expand(sp.re(v)), sp.expand(sp.im(v))

    waypoints = [(0, -1), (sp.Rational(1, 2), sp.Rational(-1, 2)), (2, 0),
                 (sp.Rational(1, 2), sp.Rational(1, 2)), (0, 1)]
    names = ["-i", "(1-i)/2", "2", "(1+i)/2", "+i"]

    # square factor SQ and scalar k for each segment, from the factorization
    #   D(s) = (k/16) * SQ * P(s):
    seg_sq = [(1 - t) ** 2, t**2, (1 - t) ** 2, t**2]
    seg_sq_str = ["(1-t)**2", "t**2", "(1-t)**2", "t**2"]
    seg_k = [1, 125, 125, 1]

    print("f = (z^2+1)(z-2)^2,  c = 5^(3/2)/4,  c^2 = 125/16")
    print("Arc polyline:", " -> ".join(names))
    print("=" * 78)

    all_ok = True
    for idx, ((ax, ay), (bx, by), na, nb) in enumerate(
            zip(waypoints, waypoints[1:], names, names[1:])):
        zx = (1 - t) * ax + t * bx
        zy = (1 - t) * ay + t * by
        Re, Im = re_im(zx, zy)
        D = sp.expand(C2 - (Re**2 + Im**2))            # 125/16 - |f|^2, degree 8

        sq = seg_sq[idx]
        k = seg_k[idx]
        # cofactor P = D / ((k/16) * SQ); must be an exact degree-6 polynomial
        Pexpr = sp.cancel(D / (sp.Rational(k, 16) * sq))
        assert Pexpr.is_polynomial(t), f"division not exact for {na}->{nb}: {Pexpr}"
        P = sp.Poly(sp.expand(Pexpr), t)

        # (a) exact identity check: D == (k/16)*SQ*P
        ident_ok = sp.simplify(D - sp.Rational(k, 16) * sq * P.as_expr()) == 0

        # (b) Bernstein nonnegativity of the degree-6 cofactor on [0,1]
        bc = bernstein_coeffs(P, t, 6)
        bern_ok = all(sp.simplify(x) >= 0 for x in bc)

        # (c) no real roots of P inside [0,1] (strict positivity sanity)
        roots_in = [r for r in P.real_roots() if r.is_real and 0 <= r <= 1]

        ok = ident_ok and bern_ok and not roots_in
        all_ok &= ok
        print(f"\nseg {na:>8} -> {nb:<8}   D(s) = ({k}/16)*{seg_sq_str[idx]}*P(s)")
        print(f"  Re f(z(s)) = {Re}")
        print(f"  Im f(z(s)) = {Im}")
        print(f"  cofactor P(s) = {P.as_expr()}")
        print(f"  identity  D == (k/16)*SQ*P : {ident_ok}")
        print(f"  Bernstein coeffs (n=6, all >=0): {[str(x) for x in bc]}  -> {bern_ok}")
        print(f"  real roots of P in [0,1]: {roots_in}  (empty => strictly positive)")
        assert ok, f"segment {na}->{nb} certificate FAILED"

    # endpoints and chord exit (exact), echoing chord_exits_certificate.py
    z = sp.symbols("z")
    f = (z**2 + 1) * (z - 2) ** 2
    assert sp.simplify(f.subs(z, sp.I)) == 0 and sp.simplify(f.subs(z, -sp.I)) == 0
    assert sp.simplify(f.subs(z, 0)) == 4 and 256 > 125  # 4 > c  <=>  16 > 5^(3/2)

    print("\n" + "=" * 78)
    print("RESULT: SOS/Bernstein certificate VALID for all 4 segments.")
    print("  Each segment inequality |f(z(s))|^2 <= 125/16 on [0,1] now has an")
    print("  explicit nlinarith-ready witness:  125/16 - |f|^2 = (k/16)*square*P,")
    print("  P >= 0 by all-nonnegative Bernstein coefficients.  Combined with the")
    print("  exact endpoints (f(±i)=0) and chord exit (f(0)=4>c), this discharges")
    print("  goodman_counterexample via the registered reduction lemma.")
    return all_ok


if __name__ == "__main__":
    raise SystemExit(0 if run() else 1)
