#!/usr/bin/env python3
"""
sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-01  (researcher-1) — the EXPLICIT
degree-16 minimal polynomial of α = √2+√3+√5+√7.

The OQ and prior sessions establish, abstractly, that α is a degree-16 algebraic
integer whose minimal polynomial is "the degree-16 product over the 16 sign
conjugates ±√2±√3±√5±√7". No session has actually PRODUCED that polynomial. This
script computes it (two independent ways), certifies it, and records it as a
concrete artifact — both the sharp structural statement (explicit monic integer
minpoly, irreducible, degree 16) and a witness for an eventual Lean proof
(`Polynomial.aeval α p = 0` + integer coefficients + 8 < α < 9 ⇒ not an integer).

Method 1: `sympy.minimal_polynomial` (algebraic-number machinery).
Method 2: the explicit product  ∏_{s∈{±1}^4} (X − (s₁√2+s₂√3+s₃√5+s₄√7))
          expanded symbolically; its coefficients must be integers (the surds
          cancel) and it must equal Method 1's result (up to monic normalization).

Cross-check on the PARENT α₃ = √2+√3+√5 (degree 8) against the known
X⁸ − 40X⁶ + 352X⁴ − 960X² + 576.

Docker-independent.  Requires sympy.
"""
import sympy as sp

x = sp.symbols("x")
s2, s3, s5, s7 = sp.sqrt(2), sp.sqrt(3), sp.sqrt(5), sp.sqrt(7)


def product_minpoly(radicals):
    """∏ over all sign patterns of (x - Σ ±√rᵢ); expand to a polynomial in x."""
    from itertools import product
    poly = sp.Integer(1)
    for signs in product([1, -1], repeat=len(radicals)):
        root = sum(sg * r for sg, r in zip(signs, radicals))
        poly *= (x - root)
    return sp.expand(poly)


def as_int_coeffs(poly):
    p = sp.Poly(sp.nsimplify(sp.expand(poly)), x)
    return [sp.nsimplify(c) for c in p.all_coeffs()]


def check(name, alpha, radicals, expected=None):
    print(f"\n### {name}   α = {alpha}")
    mp1 = sp.minimal_polynomial(alpha, x)
    mp1 = sp.Poly(mp1, x)
    print(f"  sympy.minimal_polynomial degree = {mp1.degree()}")
    # Method 2: explicit product over sign conjugates
    prod = product_minpoly(radicals)
    prodP = sp.Poly(sp.expand(prod), x)
    # coefficients must all be integers (surds cancel)
    coeffs = prodP.all_coeffs()
    all_int = all(c == sp.nsimplify(c) and sp.nsimplify(c).is_integer for c in coeffs)
    print(f"  ∏ sign-conjugates degree = {prodP.degree()},  integer coeffs: {all_int}")
    # the two must agree (product is monic; minimal_polynomial is primitive integer)
    # product is monic and irreducible-or-power; for distinct conjugates it IS the minpoly
    same = sp.simplify(prodP.as_expr() - mp1.as_expr()) == 0 or \
        sp.simplify(prodP.as_expr() - mp1.as_expr() / mp1.LC()) == 0
    # robust comparison: monic-normalize both
    a = sp.Poly(prodP.as_expr() / prodP.LC(), x)
    b = sp.Poly(mp1.as_expr() / mp1.LC(), x)
    agree = sp.simplify((a.as_expr() - b.as_expr())) == 0
    print(f"  Method1 == Method2 (monic-normalized): {agree}")
    # α is a root (high-precision numeric check)
    val = mp1.as_expr().subs(x, alpha)
    root_ok = sp.simplify(val) == 0
    print(f"  aeval_α(minpoly) = 0 : {root_ok}")
    # irreducible over Q
    irred = mp1.as_expr().as_poly(x).is_irreducible
    print(f"  irreducible over ℚ : {irred}")
    # print the explicit polynomial
    print(f"  minimal polynomial: {sp.expand(mp1.as_expr())}")
    if expected is not None:
        match_exp = sp.simplify(sp.expand(mp1.as_expr()) - expected) == 0 or \
            sp.simplify(sp.expand(prodP.as_expr()) - expected) == 0
        print(f"  matches known closed form: {match_exp}")
    return mp1, prodP, (all_int and agree and root_ok and irred)


if __name__ == "__main__":
    print("sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-01 :: explicit minimal polynomials")
    print("=" * 74)

    # PARENT cross-check: √2+√3+√5, degree 8
    expected8 = x**8 - 40*x**6 + 352*x**4 - 960*x**2 + 576
    _, _, ok3 = check("parent  √2+√3+√5 (deg 8)", s2 + s3 + s5, [s2, s3, s5], expected8)

    # TARGET: √2+√3+√5+√7, degree 16
    mp16, prod16, ok4 = check("target  √2+√3+√5+√7 (deg 16)", s2 + s3 + s5 + s7,
                              [s2, s3, s5, s7])

    # bound witness for the integral-closure / rational-root finish
    aval = float(2**0.5 + 3**0.5 + 5**0.5 + 7**0.5)
    print(f"\n  numeric α ≈ {aval:.10f}  (8 < α < 9 ⇒ α not an integer ⇒ irrational)")

    # constant term of the degree-16 minpoly = ∏ of the 16 conjugates = N(α) (norm)
    const = sp.expand(mp16.as_expr()).subs(x, 0)
    print(f"  constant term (= norm N_{{ℚ(α)/ℚ}}(α), up to sign) = {const}")

    print("\n" + "=" * 74)
    print("RESULT:", "PASS — explicit deg-8 and deg-16 minimal polynomials certified"
          if (ok3 and ok4) else "FAIL")
