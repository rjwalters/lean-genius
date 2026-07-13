#!/usr/bin/env python3
"""
Durable (Docker-free) numerical certification for mean-value-theorem-oq-02-oq-04
(OQ-04 of Taylor's theorem: a *uniform* analytic Taylor-remainder bound).

The mathematics of this slug lives in the child file
`proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean`, which is currently
**build-pending** (the 2026-06-13/14 Docker/`lake build` outage). This script
verifies the three independent subtleties that file formalizes, using only
exact/dense numerics — no Lean build required. It edits none of the Lean files.

Setup. For `f` analytic at `a` with Taylor coefficients `a_k = f^{(k)}(a)/k!`,
`partialSum m (x) = Σ_{k=0}^{m-1} a_k (x-a)^k`  (Mathlib convention: truncates at
degree m-1). The remainder for `partialSum m` is `Σ_{k≥m} a_k (x-a)^k`.

A function holomorphic on the complex disk `|z-a|<R` with `sup|f| ≤ M` there has
the Cauchy coefficient bound `|a_k| ≤ M / R^k`.

What is certified:

  (1) REFUTATION (real disk) — `oq04_axiom_is_false`.
      The S1 axiom used a *real* sup bound `M` on `(a-R,a+R) ⊂ ℝ`. The Runge
      function `1/(1+x²)` (uniformly bounded by 1 on all of ℝ) violates the
      claimed bound `|f(x)-T_n(x)| ≤ M·r^{n+1}/(R-r)` at (M,r,R,n,x)=(1,1,100,0,1):
      |f(1)-f(0)| = 1/2 ≰ 1/99. Root cause: `1/(1+z²)` has complex poles at ±i,
      so its complex disk of analyticity has radius 1, not 100.

  (2) The `R^n` factor is NECESSARY — the complex form *without* it,
      `M·r^{n+1}/(R-r)`, is FALSE for R<1.  Over an adversarial geometric family
      it is violated by large factors; only `M·r^{n+1}/(R^n·(R-r))` holds.

  (3) The `partialSum` OFF-BY-ONE — `originalRemainderForm_is_false`.
      Pairing `partialSum n` (degree ≤ n-1) with RHS `M·r^{n+1}/(R^n·(R-r))` is
      false (constant-1 witness at n=0: LHS=1, RHS=r/(R-r)<1). The fix shifts to
      `partialSum (n+1)`, after which the bound holds (verified on a test suite).

Run:  python3 verify_runge_and_cauchy.py   (exit 0 ⇔ all pass)
"""

from __future__ import annotations
import cmath
import math


# ---------------------------------------------------------------------------
# Analytic test functions: (name, coeff a_k, complex radius rho, sup M on |z|=R)
# Each `coeff(k)` returns the Taylor coefficient at a=0; `M(R)` the sup of |f|
# on the closed disk of radius R (R < rho).
# ---------------------------------------------------------------------------

def f_geometric(rho):
    """1/(1 - z/rho): coeffs rho^-k, pole at rho, M on |z|=R is 1/(1-R/rho)."""
    return (
        f"1/(1 - z/{rho})",
        lambda k: rho ** (-k),
        rho,
        lambda R: 1.0 / (1.0 - R / rho),
        lambda x: 1.0 / (1.0 - x / rho),
    )


def f_runge():
    """1/(1+z^2): poles at ±i (rho=1); a_{2k}=(-1)^k, a_odd=0; M=1/(1-R^2)."""
    return (
        "1/(1+z^2)",
        lambda k: ((-1) ** (k // 2)) if k % 2 == 0 else 0.0,
        1.0,
        lambda R: 1.0 / (1.0 - R * R),
        lambda x: 1.0 / (1.0 + x * x),
    )


def f_exp():
    """exp(z): entire (rho=inf); a_k=1/k!; M on |z|=R is e^R."""
    return (
        "exp(z)",
        lambda k: 1.0 / math.factorial(k),
        math.inf,
        lambda R: math.exp(R),
        lambda x: math.exp(x),
    )


def f_const():
    """constant 1: a_0=1, rest 0; entire; M=1. The off-by-one witness."""
    return (
        "1 (constant)",
        lambda k: 1.0 if k == 0 else 0.0,
        math.inf,
        lambda R: 1.0,
        lambda x: 1.0,
    )


def partial_sum(coeff, m, x):
    """Σ_{k=0}^{m-1} a_k x^k  (Mathlib partialSum convention)."""
    return sum(coeff(k) * x ** k for k in range(m))


def true_value(fval, x):
    return fval(x)


# ---------------------------------------------------------------------------
# (1) Runge real-disk refutation.
# ---------------------------------------------------------------------------

def part1():
    print("== (1) REFUTATION: real-disk axiom is false (Runge phenomenon) ==")
    _, _, _, _, runge = f_runge()
    M, r, R, n, x = 1.0, 1.0, 100.0, 0, 1.0
    lhs = abs(runge(x) - runge(0.0))           # |f(x) - T_0(x)|, T_0 = f(a)
    rhs = M * r ** (n + 1) / (R - r)
    assert lhs > rhs, "expected Runge violation"
    print(f"   f=1/(1+x²), (M,r,R,n,x)=({M},{r},{R},{n},{x}): "
          f"|f(1)-f(0)|={lhs} ≰ M·r^(n+1)/(R-r)={rhs:.4g}  ⇒ FALSE  ✓")
    # sweep: the real sup R=100 buys nothing; the relevant radius is 1.
    viol = 0
    for xx in [0.5, 0.8, 1.0, 1.5, 2.0]:
        lhs = abs(runge(xx) - runge(0.0))
        rhs = 1.0 * xx / (100.0 - xx)           # n=0, M=1, r=xx, R=100
        if lhs > rhs:
            viol += 1
    print(f"   {viol}/5 swept x∈[0.5,2] also violate the real-disk n=0 bound")
    print("   ⇒ a real sup bound does NOT control Cauchy coefficients; the complex\n"
          "     disk of analyticity (radius 1, poles ±i) is what matters.\n")


# ---------------------------------------------------------------------------
# (2) The R^n factor is necessary: M·r^{n+1}/(R-r) is false for R<1.
# ---------------------------------------------------------------------------

def remainder_geometric(rho, m, r):
    """Exact remainder Σ_{k≥m} (r/rho)^k of the geometric family at real x=r."""
    q = r / rho
    return q ** m / (1.0 - q)


def part2():
    print("== (2) the R^n factor is NECESSARY: M·r^{n+1}/(R-r) (no R^n) is false for R<1 ==")
    worst_stated = 0.0
    worst_cauchy = 0.0
    n_checks = 0
    for R in (0.3, 0.5, 0.8, 0.95, 1.0, 1.5, 3.0):
        for rfrac in (0.1, 0.3, 0.6, 0.9):
            r = rfrac * R
            for n in range(0, 8):
                for rho in (R * 1.001, R * 1.05, R * 1.5, R * 5.0):
                    M = 1.0 / (1.0 - R / rho)
                    # corrected form pairs partialSum(n+1) ⇒ remainder starts at n+1
                    rem = M * remainder_geometric(rho, n + 1, r)
                    b_stated = M * r ** (n + 1) / (R - r)                 # WRONG (no R^n)
                    b_cauchy = M * r ** (n + 1) / (R ** n * (R - r))      # CORRECT
                    worst_stated = max(worst_stated, rem / b_stated)
                    worst_cauchy = max(worst_cauchy, rem / b_cauchy)
                    n_checks += 1
    print(f"   swept {n_checks} (R,r,n,ρ) configs on the geometric family:")
    print(f"   max(actual / [M·r^(n+1)/(R-r)])         = {worst_stated:.2f}  "
          f"⇒ the no-R^n form is VIOLATED (ratio > 1)")
    print(f"   max(actual / [M·r^(n+1)/(R^n·(R-r))])   = {worst_cauchy:.3f}  "
          f"⇒ the R^n form HOLDS (ratio ≤ 1)")
    assert worst_stated > 1.0, "expected the no-R^n form to be violated"
    assert worst_cauchy <= 1.0 + 1e-9, "Cauchy form must hold"
    print()


# ---------------------------------------------------------------------------
# (3) partialSum off-by-one + validity of the corrected (n+1)-shifted bound.
# ---------------------------------------------------------------------------

def part3():
    print("== (3) partialSum off-by-one: partialSum n is FALSE, partialSum (n+1) is CORRECT ==")
    # (3a) constant-1 witness refuting the partialSum n pairing.
    name, coeff, rho, Mf, fval = f_const()
    R, r, n = 1.0, 0.25, 0  # 0<r<R/2
    M = Mf(R)
    lhs = abs(true_value(fval, r) - partial_sum(coeff, n, r))  # partialSum 0 = 0
    rhs = M * r ** (n + 1) / (R ** n * (R - r))
    assert lhs > rhs, "expected constant-1 off-by-one violation"
    print(f"   [partialSum n] f≡1, (R,r,n)=({R},{r},{n}): "
          f"|f-partialSum_0|={lhs} ≰ {rhs:.4g}  ⇒ FALSE (off-by-one)  ✓")

    # (3b) corrected (n+1)-shifted bound holds across the analytic test suite.
    suite = [f_geometric(2.0), f_geometric(1.3), f_runge(), f_exp(), f_const()]
    n_ok = 0
    worst = 0.0
    for name, coeff, rho, Mf, fval in suite:
        for R in (0.4, 0.7, 0.9):
            if R >= rho:
                continue
            M = Mf(R)
            for rfrac in (0.2, 0.5, 0.85):
                r = rfrac * R
                for n in range(0, 7):
                    # remainder of partialSum (n+1) at the worst real point x=r
                    rem = abs(true_value(fval, r) - partial_sum(coeff, n + 1, r))
                    bound = M * r ** (n + 1) / (R ** n * (R - r))
                    ratio = rem / bound if bound > 0 else 0.0
                    worst = max(worst, ratio)
                    assert rem <= bound * (1 + 1e-9), \
                        f"corrected bound violated: {name} R={R} r={r} n={n} {rem}>{bound}"
                    n_ok += 1
    print(f"   [partialSum (n+1)] corrected bound M·r^(n+1)/(R^n·(R-r)) holds on "
          f"{n_ok} cases (5 fns × R,r,n)")
    print(f"   tightest observed actual/bound ratio = {worst:.3f} (≤ 1)\n")


def main():
    print("mean-value-theorem-oq-02-oq-04 — Runge refutation & Cauchy-remainder cert (Docker-free)\n")
    part1()
    part2()
    part3()
    print("ALL CHECKS PASSED.")


if __name__ == "__main__":
    main()
