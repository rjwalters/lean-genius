#!/usr/bin/env python3
"""
verify_real_subfield_degree.py
================================

Verify-before-assert certification for the *exact degree* of the maximal real
subfield generator of a cyclotomic field, i.e. the genuinely-open follow-up of
`nth-root-irrational-oq-01-oq-01`:

        [ Q(zeta_n + zeta_n^{-1}) : Q ]  =  phi(n) / 2          (n >= 3)

equivalently, the minimal polynomial over Q of

        alpha_n := zeta_n + zeta_n^{-1} = 2*cos(2*pi/n)

has degree exactly phi(n)/2 for n >= 3 (and degree 1 for n in {1,2}).

The sibling Lean files in this problem already establish:
  - NthRootIrrationalOQ01OQ01Real.lean : deg(minpoly Q zeta) <= 2 forces the
    *irrational direction* phi(n) >= 3 => alpha_n irrational  (a degree-bound
    contradiction, NOT the exact degree).
  - NthRootIrrationalOQ01OQ01Cos / CosRational : the full Niven classification
    alpha_n rational <=> n in {1,2,3,4,6}.

What is still open (Docker-gated, ~150 LOC of IntermediateField tower machinery
that is partly absent from Mathlib) is the EXACT degree phi(n)/2.  This script
certifies the three numerical/symbolic facts that the eventual Lean proof rests
on, so the build-up session can paste with confidence:

  (A) The quadratic relation        zeta^2 - alpha*zeta + 1 = 0   (identity, zeta != 0)
      => zeta has degree <= 2 over K := Q(alpha).
  (B) The degree tower              phi(n) = 2 * deg(minpoly_Q(alpha_n))   (n >= 3)
      i.e. [Q(zeta):Q] = [Q(zeta):K] * [K:Q] with [Q(zeta):K] = 2 exactly
      (the lower bound [Q(zeta):K] >= 2 holds because zeta is non-real for
      n >= 3 while K = Q(alpha) subset R).
  (C) The exact degree              deg(minpoly_Q(alpha_n)) = phi(n)/2   (n >= 3),
      and = 1 (rational) exactly for n in {1,2,3,4,6} -- matching Niven.

Pure standard-library + sympy; deterministic; all asserts must pass.
Run:  python3 verify_real_subfield_degree.py
"""

from __future__ import annotations

import sympy as sp
from sympy import I, Symbol, cos, exp, expand, minimal_polynomial, pi, simplify, totient

N_MAX = 30  # certify for 1 <= n <= N_MAX

x = Symbol("x")

# Niven's rational set: alpha_n = 2*cos(2*pi/n) is rational exactly here.
NIVEN_RATIONAL = {1, 2, 3, 4, 6}


def alpha(n: int):
    """The real subfield generator alpha_n = 2*cos(2*pi/n)."""
    return 2 * cos(2 * pi / n)


def deg_minpoly_alpha(n: int) -> int:
    return int(sp.degree(minimal_polynomial(alpha(n), x), x))


def deg_minpoly_zeta(n: int) -> int:
    return int(sp.degree(minimal_polynomial(exp(2 * pi * I / n), x), x))


def check_quadratic_relation() -> None:
    """(A) zeta^2 - (zeta + 1/zeta)*zeta + 1 = 0 as an algebraic identity."""
    z = Symbol("z", nonzero=True)
    expr = expand(z**2 - (z + 1 / z) * z + 1)
    assert simplify(expr) == 0, f"quadratic relation failed symbolically: {expr}"
    # Concrete sanity on a spread of n.
    for n in (3, 5, 7, 12, 17, 24):
        zeta = exp(2 * pi * I / n)
        rel = simplify(zeta**2 - (zeta + 1 / zeta) * zeta + 1)
        assert rel == 0, f"n={n}: quadratic relation != 0, got {rel}"
    print("[A] quadratic relation  zeta^2 - alpha*zeta + 1 = 0  ........ OK")


def check_tower_and_exact_degree() -> None:
    """(B) tower phi(n) = 2*deg(alpha) for n>=3, and (C) exact degree phi(n)/2."""
    rows = []
    for n in range(1, N_MAX + 1):
        phi = int(totient(n))
        da = deg_minpoly_alpha(n)

        # (C) exact degree.
        expected = max(phi // 2, 1)
        assert da == expected, (
            f"n={n}: deg(minpoly alpha)={da} != max(phi//2,1)={expected}"
        )

        # Niven cross-check: degree 1 (rational) <=> n in {1,2,3,4,6}.
        is_rational = da == 1
        assert is_rational == (n in NIVEN_RATIONAL), (
            f"n={n}: rationality mismatch (deg1={is_rational}, niven={n in NIVEN_RATIONAL})"
        )

        # (B) tower, meaningful for n>=3 where zeta is non-real and [Q(zeta):K]=2.
        if n >= 3:
            dz = deg_minpoly_zeta(n)
            assert dz == phi, f"n={n}: deg(minpoly zeta)={dz} != phi(n)={phi}"
            assert phi == 2 * da, f"n={n}: tower phi={phi} != 2*deg(alpha)={2*da}"

        rows.append((n, phi, da, expected, is_rational))

    print("[B] tower  phi(n) = 2 * deg(minpoly alpha)  (n>=3) ........... OK")
    print("[C] exact degree  deg(minpoly alpha_n) = phi(n)/2  ........... OK")
    print()
    print("    n  phi(n)  deg(minpoly 2cos(2pi/n))  phi/2|1  rational?")
    print("    -  ------  ------------------------  -------  --------")
    for n, phi, da, expected, isr in rows:
        print(f"   {n:2d}  {phi:5d}   {da:21d}   {expected:6d}   {'yes' if isr else 'no'}")


def check_niven_values() -> None:
    """Spot-check the five rational values of alpha_n (Niven)."""
    expected = {1: 2, 2: -2, 3: -1, 4: 0, 6: 1}
    for n, val in expected.items():
        got = simplify(alpha(n))
        assert got == val, f"n={n}: alpha_n={got} != {val}"
    print("[D] Niven rational values  alpha_n in {2,-2,-1,0,1}  ........ OK")


def main() -> None:
    print("Certifying the exact degree of the real cyclotomic subfield generator")
    print(f"  alpha_n = zeta_n + zeta_n^-1 = 2*cos(2*pi/n),  for 1 <= n <= {N_MAX}")
    print()
    check_quadratic_relation()
    check_niven_values()
    check_tower_and_exact_degree()
    print()
    print(f"ALL CHECKS PASSED (n = 1 .. {N_MAX}).")
    print("Open Lean target (Docker-gated): [Q(alpha_n):Q] = phi(n)/2 via the")
    print("IntermediateField tower  [Q(zeta):Q] = [Q(zeta):Q(alpha)] * [Q(alpha):Q]")
    print("with [Q(zeta):Q(alpha)] = 2 exactly (relation (A) + zeta non-real, n>=3).")


if __name__ == "__main__":
    main()
