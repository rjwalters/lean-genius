#!/usr/bin/env python3
"""
Reproducible verification of the load-bearing facts behind Strategy D for

    sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-01
    Goal:  Irrational (sqrt 2 + sqrt 3 + sqrt 5 + sqrt 7)

Strategy D (algebraic integer + bounded interval):
  alpha = sqrt2 + sqrt3 + sqrt5 + sqrt7 is a sum of four algebraic integers,
  hence integral over Z. A rational number integral over Z is an integer
  (Z is integrally closed in Q). But 8 < alpha < 9, so alpha is not an
  integer, hence alpha is irrational.

This script independently re-derives and checks, with NO appeal to the
numbers pre-written in knowledge.md, the three facts the Lean proof rests on:

  (F1) integrality:   each sqrt(k) is a root of the MONIC INTEGER poly x^2 - k,
                      so alpha is integral over Z. We also exhibit alpha's
                      monic integer minimal polynomial m(x) (degree 16) and
                      check m(alpha) = 0, certifying integrality concretely.
  (F2) the bound:     8 < alpha < 9, verified to high precision (mpmath).
  (F3) minimal poly:  m(x) is re-derived from first principles via a resultant
                      of two quartics (NOT copied from the knowledge base),
                      then cross-checked against the value recorded in
                      knowledge.md. Confirms degree 16 and constant term 215^2.

Run:  python3 verify_strategy_d.py
Exits 0 with "ALL CHECKS PASSED" iff every assertion holds.

Dependencies: sympy >= 1.14, mpmath (bundled with sympy).
"""

import sympy as sp
import mpmath as mp


def check(name, cond):
    status = "ok  " if cond else "FAIL"
    print(f"  [{status}] {name}")
    assert cond, f"CHECK FAILED: {name}"


def main():
    x, y = sp.symbols("x y")

    print("== (F1) Each sqrt(k) is integral over Z (root of monic x^2 - k) ==")
    # sqrt(k) is a root of the monic integer polynomial x^2 - k; the leading
    # coefficient is 1 (monic) and all coefficients are integers, which is
    # exactly what `IsIntegral Z (sqrt k)` requires.
    for k in (2, 3, 5, 7):
        poly = sp.Poly(x**2 - k, x)
        check(f"x^2 - {k} is monic", poly.LC() == 1)
        check(f"x^2 - {k} has integer coeffs", all(c.is_integer for c in poly.all_coeffs()))
        check(f"(sqrt {k})^2 - {k} == 0", sp.simplify(sp.sqrt(k)**2 - k) == 0)

    print("== (F3) Re-derive alpha's minimal polynomial via a resultant ==")
    # p = sqrt2 + sqrt3 satisfies p^4 - 10 p^2 + 1 = 0.
    # q = sqrt5 + sqrt7 satisfies q^4 - 24 q^2 + 4 = 0.
    # Confirm those two quartics from scratch:
    p_val = sp.sqrt(2) + sp.sqrt(3)
    q_val = sp.sqrt(5) + sp.sqrt(7)
    check("p=sqrt2+sqrt3 root of y^4-10y^2+1",
          sp.simplify(p_val**4 - 10 * p_val**2 + 1) == 0)
    check("q=sqrt5+sqrt7 root of y^4-24y^2+4",
          sp.simplify(q_val**4 - 24 * q_val**2 + 4) == 0)

    # alpha = p + q. Eliminate y between p's minimal poly (in y) and
    # q's minimal poly written for q = x - y. The resultant in y is a
    # polynomial in x having alpha as a root.
    p_poly = y**4 - 10 * y**2 + 1
    q_poly = (x - y) ** 4 - 24 * (x - y) ** 2 + 4
    res = sp.resultant(p_poly, q_poly, y)
    m_derived = sp.Poly(sp.expand(res), x)

    check("resultant is degree 16", m_derived.degree() == 16)
    check("resultant is monic", m_derived.LC() == 1)
    check("resultant has integer coeffs",
          all(c.is_integer for c in m_derived.all_coeffs()))

    # The value recorded in knowledge.md (independent transcription):
    m_recorded = sp.Poly(
        x**16 - 136 * x**14 + 6476 * x**12 - 141912 * x**10
        + 1513334 * x**8 - 7453176 * x**6 + 13950764 * x**4
        - 5596840 * x**2 + 46225,
        x,
    )
    check("derived minimal poly == value in knowledge.md",
          m_derived == m_recorded)
    check("constant term is 215^2 = 46225",
          m_derived.all_coeffs()[-1] == 215**2 == 46225)

    # m(alpha) = 0 exactly (certifies alpha integral over Z via this monic m).
    alpha_sym = sp.sqrt(2) + sp.sqrt(3) + sp.sqrt(5) + sp.sqrt(7)
    m_at_alpha = sp.expand(m_derived.as_expr().subs(x, alpha_sym))
    check("m(alpha) == 0 (symbolic)", sp.simplify(m_at_alpha) == 0)

    print("== (F2) Decisive bound 8 < alpha < 9 (high precision) ==")
    mp.mp.dps = 60
    alpha_num = mp.sqrt(2) + mp.sqrt(3) + mp.sqrt(5) + mp.sqrt(7)
    print(f"       alpha ~= {alpha_num}")
    check("8 < alpha", alpha_num > 8)
    check("alpha < 9", alpha_num < 9)
    # Margins are comfortable (alpha ~ 8.0281), so floating error is irrelevant;
    # the strict inequalities also follow rigorously from, e.g.,
    #   sqrt2>1.41, sqrt3>1.73, sqrt5>2.23, sqrt7>2.64  => sum > 8.01 > 8
    #   sqrt2<1.42, sqrt3<1.74, sqrt5<2.24, sqrt7<2.65  => sum < 8.05 < 9
    check("rational lower witnesses sum > 8",
          sp.Rational(141, 100) + sp.Rational(173, 100)
          + sp.Rational(223, 100) + sp.Rational(264, 100) > 8)
    check("rational upper witnesses sum < 9",
          sp.Rational(142, 100) + sp.Rational(174, 100)
          + sp.Rational(224, 100) + sp.Rational(265, 100) < 9)
    # And each witness genuinely bounds its radical:
    for lo, hi, k in [(sp.Rational(141, 100), sp.Rational(142, 100), 2),
                      (sp.Rational(173, 100), sp.Rational(174, 100), 3),
                      (sp.Rational(223, 100), sp.Rational(224, 100), 5),
                      (sp.Rational(264, 100), sp.Rational(265, 100), 7)]:
        check(f"{lo} < sqrt {k}: lo^2 < {k}", lo**2 < k)
        check(f"sqrt {k} < {hi}: {k} < hi^2", k < hi**2)

    print("\nALL CHECKS PASSED")


if __name__ == "__main__":
    main()
