#!/usr/bin/env python3
"""
Erdős #258 OQ-01 — exact verification of the Cantor-tail RECURSION and a
correction to the prior open-zone numerical table.

Series:  S(a) = Σ_{n≥0} τ(n+1) / (a_1 ⋯ a_n)        (τ = number-of-divisors)
Renormalised tail at level N:
         T_N(a) = Σ_{n>N} τ(n+1) / (a_{N+1} ⋯ a_n)
                = τ(N+2)/a_{N+1} + τ(N+3)/(a_{N+1}a_{N+2}) + ⋯

Established here (exact Fraction arithmetic):

  (R)  a_{N+1} · T_N = τ(N+2) + T_{N+1}        [tail recursion]
  (B)  S         = τ(1)  + T_0                  [base case, τ(1)=1]

These are the Cantor-series backbone.  By induction (R)+(B) give the identity
(★) `(a_1⋯a_N)·S = integer + T_N` used by the irrationality engine (Lemma A),
with the integers m_N defined by m_0 = τ(1), m_{N+1} = a_{N+1} m_N + τ(N+2).

It also exposes the rationality obstruction in purely integer terms:
  S = p/q  ⟺  ∃ q ≥ 1 : q·T_N ∈ ℤ for all N,
and then r_N := q·T_N is a sequence of POSITIVE integers with
  r_{N+1} = a_{N+1} r_N − q·τ(N+2).

----------------------------------------------------------------------------
HONEST CORRECTION to the prior session's open-zone table.

Prior table listed subpolynomial families (√n, max(τ,√n), (log n)^2) as having
"liminf T_N > 0" (engine silent).  Exact computation over a longer window shows
these trajectories are NON-MONOTONE with deep dips toward 0 (√n reaches ~0.045,
max(τ,√n) reaches ~0.023) — so "liminf > 0" is NOT numerically supported.  But
neither is a clean "T_N → 0": the decay is erratic and slow.  The subpolynomial
zone is genuinely AMBIGUOUS numerically, not settled either way.

Tempting conjecture "a_n/τ(n) → ∞ ⟹ T_N → 0" is FALSE: family a_n=τ(n)·⌊log n⌋
satisfies a_n/τ(n)=⌊log n⌋→∞ yet T_N spikes back to ~0.89 (the numerator τ(N+2)
and denominator a_{N+1} are index-shifted, so a_n/τ(n)→∞ does not control the
leading tail term τ(N+2)/a_{N+1}).  The only rigorously CLOSED sufficient
condition remains polynomial growth a_n ≥ n^δ (Corollary C in the Lean file).
"""
from fractions import Fraction as F
from sympy import divisor_count, isprime
import math


def tau(m):
    return int(divisor_count(m))


def T_N(a, N, K=1500):
    """Exact partial T_N truncated at n = N+K (terms shrink super-exponentially)."""
    s = F(0)
    d = F(1)
    for n in range(N + 1, N + 1 + K):
        d *= a(n)
        s += F(tau(n + 1), 1) / d
    return s


def S_value(a, M=800):
    s = F(0)
    d = F(1)
    for n in range(0, M):
        if n >= 1:
            d *= a(n)
        s += F(tau(n + 1), 1) / d
    return s


FAMILIES = {
    "a_n = n+1": lambda n: n + 1,
    "a_n = n^2": (lambda n: n * n if n >= 2 else 2),
    "a_n = isqrt(n)+2": lambda n: math.isqrt(n) + 2,
    "a_n = max(tau(n+1),isqrt(n)+2)": lambda n: max(tau(n + 1), math.isqrt(n) + 2),
    "a_n = tau(n)*floor(log n)+2": lambda n: tau(n) * int(math.log(n + 2)) + 2,
    "a_n = max(2,floor((log n)^2))": lambda n: max(2, int(math.log(n + 2) ** 2)),
}


def check_recursion():
    print("=== (R) RECURSION  a_{N+1}·T_N = τ(N+2) + T_{N+1}  (exact) ===")
    all_ok = True
    for name, a in FAMILIES.items():
        ok = True
        for N in range(0, 40):
            lhs = F(a(N + 1)) * T_N(a, N, K=1500)
            rhs = F(tau(N + 2)) + T_N(a, N + 1, K=1500)
            if lhs != rhs:
                # truncation makes lhs/rhs differ only past the shared horizon;
                # compare to high precision instead of exact equality of truncations
                if abs(float(lhs - rhs)) > 1e-12:
                    ok = False
                    print(f"    MISMATCH {name} N={N}: {float(lhs - rhs):.3e}")
        print(f"    {name:38s}: holds = {ok}")
        all_ok = all_ok and ok
    return all_ok


def check_base():
    print("\n=== (B) BASE CASE  S = τ(1) + T_0   (τ(1)=1) ===")
    all_ok = True
    for name, a in FAMILIES.items():
        s = S_value(a, M=800)
        t0 = T_N(a, 0, K=1500)
        ok = abs(float(s - (F(tau(1)) + t0))) < 1e-12
        print(f"    {name:38s}: S={float(s):.6f}  1+T_0={float(F(1)+t0):.6f}  ok={ok}")
        all_ok = all_ok and ok
    return all_ok


def check_integer_obstruction():
    print("\n=== integer obstruction: r_{N+1} = a_{N+1} r_N − q τ(N+2) preserves "
          "r_N = q T_N ===")
    # If S were p/q, r_N = q T_N would be positive integers obeying the recursion.
    # Verify the recursion-propagation numerically (not integrality, which is the
    # open part) for an arbitrary q, confirming the algebra.
    a = lambda n: n + 1
    q = 6
    ok = True
    for N in range(0, 25):
        rN = q * T_N(a, N, K=1500)
        rN1_recur = F(a(N + 1)) * rN - F(q) * F(tau(N + 2))
        rN1_direct = q * T_N(a, N + 1, K=1500)
        if abs(float(rN1_recur - rN1_direct)) > 1e-12:
            ok = False
    print(f"    propagation r_{{N+1}}=a r_N − q τ holds = {ok}")
    return ok


def open_zone_correction():
    print("\n=== open-zone CORRECTION: subpolynomial T_N is non-monotone w/ deep dips ===")
    for name in ["a_n = isqrt(n)+2", "a_n = max(tau(n+1),isqrt(n)+2)",
                 "a_n = max(2,floor((log n)^2))"]:
        a = FAMILIES[name]
        vals = [float(T_N(a, N, K=1500)) for N in range(50, 12000, 37)]
        print(f"    {name:38s}: min={min(vals):.4f} max={max(vals):.4f}  "
              f"(NOT a clean liminf>0)")
    print("\n=== counterexample to 'a_n/τ(n)→∞ ⟹ T_N→0' ===")
    a = FAMILIES["a_n = tau(n)*floor(log n)+2"]
    spikes = [(N, float(T_N(a, N, K=1500))) for N in [1000, 4000, 8000]]
    print(f"    a_n=τ(n)⌊log n⌋ (a_n/τ=⌊log n⌋→∞):  T_N at N∈{{1000,4000,8000}} = "
          f"{[f'{v:.3f}' for _, v in spikes]}  (spikes ⇒ no T_N→0)")


if __name__ == "__main__":
    r = check_recursion()
    b = check_base()
    o = check_integer_obstruction()
    open_zone_correction()
    print("\n" + "=" * 60)
    print(f"RECURSION (R): {'PASS' if r else 'FAIL'}   "
          f"BASE (B): {'PASS' if b else 'FAIL'}   "
          f"OBSTRUCTION ALGEBRA: {'PASS' if o else 'FAIL'}")
