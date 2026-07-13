#!/usr/bin/env python3
"""
S1 ORIENT (researcher-2) for descartes-rule-of-signs-oq-02-oq-03:
"Close the `budan_parity` axiom".

The axiom (DescartesRuleOfSignsOQ02.lean:244) states, for p ≠ 0 and a < b:
    Even (budanCount p a - budanCount p b - rootsInInterval p a b)   [ℕ-subtraction]
where budanCount p x = #sign-changes in [p(x), p'(x), …, p⁽ⁿ⁾(x)]
and   rootsInInterval p a b = #real roots in (a,b] with multiplicity.

The seeker named this "close via Mathlib's FTA / complex-conjugate pairs".
That intuition is for the GLOBAL Descartes count; the LOCAL interval parity has a
cleaner route, which this script certifies (verify-before-assert) before any Lean:

  (A) budanCount p x = signVariations(taylor x p)   [the Mathlib bridge:
      taylor coeffs are p⁽ᵏ⁾(x)/k!, same signs as p⁽ᵏ⁾(x)].
  (B) PARITY of a sign-variation count = (sign of leading coeff ≠ sign of the
      lowest-degree nonzero coeff).  For Q = taylor x p: leadingCoeff Q =
      leadingCoeff p (shift-invariant) and constant term Q.coeff 0 = p(x).
      ⇒ parity(budanCount p x) = [sign(p(x)) ≠ sign(leadingCoeff p)].
  (C) ⇒ parity(budanCount p a) ⊕ parity(budanCount p b) = [sign p(a) ≠ sign p(b)].
  (D) [sign p(a) ≠ sign p(b)] ⟺ Odd(rootsInInterval p a b)   [the FTA content:
      real factorization p = lead·∏(x−rᵢ)·(pos. quadratics); each real root in
      (a,b) flips the sign, complex pairs and even multiplicities don't change parity].
  ⇒ (A–D) give  V_p(a) − V_p(b) ≡ N (mod 2), i.e. the axiom.

Requires numpy (uses numpy.polynomial). Pure-deterministic seeds (no RNG state
leakage). Exits non-zero on any mismatch.
Run:  python3 verify_budan_parity.py
"""

import itertools
import numpy as np
from numpy.polynomial import polynomial as P


def sign(x, tol=1e-9):
    if x > tol:
        return 1
    if x < -tol:
        return -1
    return 0


def sign_changes(vals, tol=1e-9):
    s = [sign(v, tol) for v in vals if abs(v) > tol]
    return sum(1 for i in range(len(s) - 1) if s[i] != s[i + 1])


def coeffs_low_to_high(roots, lead, extra_complex_pairs):
    """Build a real polynomial from given real roots (with multiplicity), a
    leading coefficient sign, and some conjugate complex pairs (irreducible
    positive-definite quadratics x^2 - 2*Re*x + |z|^2 with no real root)."""
    # start from lead
    c = np.array([float(lead)])
    for r in roots:
        c = P.polymul(c, [-r, 1.0])  # (x - r)
    for (re, im) in extra_complex_pairs:
        # (x-(re+i*im))(x-(re-i*im)) = x^2 - 2 re x + (re^2+im^2)
        c = P.polymul(c, [re * re + im * im, -2 * re, 1.0])
    return c  # low-to-high


def iter_deriv_evals(c_low_high, x):
    """[p(x), p'(x), ..., p^(n)(x)] via repeated polyder."""
    out = []
    c = c_low_high.copy()
    while len(c) >= 1 and not (len(c) == 1 and abs(c[0]) == 0):
        out.append(float(P.polyval(x, c)))
        if len(c) == 1:
            break
        c = P.polyder(c)
    # ensure we include the final constant derivative even if loop ended early
    return out


def budan_count(c_low_high, x):
    n = len(c_low_high) - 1
    vals = [float(P.polyval(x, P.polyder(c_low_high, k))) for k in range(n + 1)]
    return sign_changes(vals)


def taylor_shift(c_low_high, x):
    """coeffs (low->high) of p(X + x)."""
    n = len(c_low_high) - 1
    # taylor coeff k = p^(k)(x)/k!
    out = []
    fk = 1.0
    for k in range(n + 1):
        if k > 0:
            fk *= k
        out.append(float(P.polyval(x, P.polyder(c_low_high, k))) / fk)
    return np.array(out)


def signVariations(c_low_high):
    # Mathlib's signVariations = sign changes in the coefficient list (zeros dropped)
    return sign_changes(list(c_low_high))


def roots_in_interval(real_roots, a, b):
    # half-open (a, b], with multiplicity
    return sum(1 for r in real_roots if a < r <= b)


def main():
    checks = 0
    # deterministic catalogue of real-root multisets + complex pairs + leads
    real_root_sets = [
        [], [0.5], [-1.0, 2.0], [1.0, 1.0], [0.3, 0.3, 0.3],
        [-2.0, -0.5, 1.5, 3.0], [0.7, 0.7, 2.2], [-1.5, -1.5, -1.5, 4.0],
        [0.1, 0.9, 1.1, 2.5, 2.5], [-3.0, -1.0, 0.0, 2.0, 4.0],
    ]
    complex_sets = [[], [(0.5, 1.0)], [(-1.0, 0.7), (2.0, 0.3)]]
    leads = [1.0, -2.5]
    # endpoints chosen to avoid sitting on roots
    endpoints = [(-2.7, 0.45), (-0.6, 1.05), (0.05, 2.45), (-4.0, 4.0), (0.65, 2.15)]

    for rr, cs, lead in itertools.product(real_root_sets, complex_sets, leads):
        c = coeffs_low_to_high(rr, lead, cs)
        for (a, b) in endpoints:
            pa, pb = float(P.polyval(a, c)), float(P.polyval(b, c))
            if abs(pa) < 1e-7 or abs(pb) < 1e-7:
                continue  # endpoint on a root: classical Budan excludes this
            Va, Vb = budan_count(c, a), budan_count(c, b)
            N = roots_in_interval(rr, a, b)

            # (A) budanCount = signVariations(taylor)
            assert Va == signVariations(taylor_shift(c, a)), f"(A) fail a: {rr},{cs},{lead},{a}"
            assert Vb == signVariations(taylor_shift(c, b)), f"(A) fail b"

            # (B) parity(budanCount p x) = [sign p(x) != sign lead]
            lead_sign = sign(c[-1])
            assert (Va % 2 == 1) == (sign(pa) != lead_sign), f"(B) fail a: {rr},{cs},{lead},{a}"
            assert (Vb % 2 == 1) == (sign(pb) != lead_sign), f"(B) fail b"

            # (C) parity(Va) xor parity(Vb) = [sign pa != sign pb]
            assert ((Va % 2) ^ (Vb % 2) == 1) == (sign(pa) != sign(pb)), "(C) fail"

            # (D) [sign pa != sign pb] <-> Odd(N)
            assert (sign(pa) != sign(pb)) == (N % 2 == 1), f"(D) fail: {rr},{a},{b},N={N}"

            # MAIN: the axiom itself — Even(Va - Vb - N) with TRUNCATED nat subtraction,
            # matching the Lean statement (and the proven upper bound Va >= Vb,
            # rootsInInterval <= Va - Vb).
            nat_sub = max(Va - Vb, 0)
            nat_sub2 = max(nat_sub - N, 0)
            # the upper bound guarantees N <= Va - Vb, so nat-sub == true difference here:
            assert Vb <= Va, f"upper-bound violated?! Va={Va} Vb={Vb}"
            assert N <= Va - Vb, f"bound violated N={N} Va-Vb={Va-Vb}"
            assert nat_sub2 % 2 == 0, f"AXIOM fail Even(Va-Vb-N): Va={Va},Vb={Vb},N={N}"
            checks += 1

    print(f"All {checks} checks passed.")
    print("Certified the budan_parity decomposition (verify-before-assert):")
    print("  (A) budanCount p x = signVariations(taylor x p)   [Mathlib bridge via Polynomial.taylor]")
    print("  (B) parity(budanCount p x) = [sign p(x) != sign(leadingCoeff p)]")
    print("  (C) parity(V_a) xor parity(V_b) = [sign p(a) != sign p(b)]")
    print("  (D) [sign p(a) != sign p(b)] <-> Odd(rootsInInterval p a b)   [real-factorization/FTA]")
    print("  => Even(V_a - V_b - N): the budan_parity axiom. Also reconfirmed N <= V_a - V_b.")
    print("Mathlib has signVariations + roots_countP_pos_le_signVariations (the BOUND) but NOT parity.")


if __name__ == "__main__":
    main()
