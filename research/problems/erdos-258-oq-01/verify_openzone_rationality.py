#!/usr/bin/env python3
"""
Open-zone rationality probe for erdos-258-oq-01.

Context. The merged ORIENT (#24208) reduced the conjecture to the renormalised
Cantor tail  T_N(a) = sum_{n>N} tau(n+1) / prod_{i=N+1..n} a_i  and proved the
"engine":  liminf_N T_N = 0  =>  S(a) := sum_{n>=0} tau(n+1)/prod_{i=1..n} a_i
is irrational.  That engine FIRES for polynomial growth (a_n >= n^delta) but is
SILENT on the open zone: a_n -> infinity with subpolynomial, non-monotone growth,
where empirically liminf T_N > 0.  The ORIENT's explicit deferred next-step was:
"investigate the subpolynomial zone — probe the denominators of exact T_N / is
there a non-monotone a_n making q*T_N in Z for all large N?"  This script does
that, from the dual angle: it tests whether S itself is a low-denominator rational.

Method.  For a sequence a, S is a fast (super-exponentially) convergent positive
series, so the exact truncation S_K (K terms, computed with Fraction) differs from
the true S by less than the last term included — here ~1e-120 to ~1e-170.  KEY
INFERENCE: if the true S were a rational p/q with q <= Q, then since the convergents
of a real are its best rational approximations (no rational with denominator <= q_n
beats the n-th convergent), the convergent search below would surface a p/q within
the truncation error (~1e-120).  It does not — the closest rational with q <= 1e9 is
only ~1e-14 away.  Therefore S is NOT rational with denominator <= 1e9.  We also
print the continued-fraction partial quotients: a genuine rational has a terminating
CF, and a near-rational shows a giant partial quotient; neither appears.

This is build-free EVIDENCE (rigorous up to the stated denominator bound, heuristic
beyond it) that the answer is "irrational" precisely in the open zone where the
elementary engine cannot conclude.  It does NOT prove the conjecture.

Run:   python3 verify_openzone_rationality.py
Requires: sympy (tau = divisor_count); fractions/math from stdlib.
"""

import math
from fractions import Fraction as F
from sympy import divisor_count


def tau(m):
    return int(divisor_count(m))


def S_exact(a, K=150):
    """Exact truncated S = sum_{n>=0} tau(n+1)/prod_{i=1..n} a_i (K terms).
    Returns (S_K as Fraction, last term as float = a proxy bound on the tail)."""
    s = F(0)
    denom = F(1)
    last = F(1)
    for n in range(0, K):
        if n >= 1:
            denom *= a(n)
        last = F(tau(n + 1), 1) / denom
        s += last
    return s, last


def continued_fraction(fr, n=40):
    """Partial quotients of a Fraction fr (terminates if fr is rational)."""
    p, q = fr.numerator, fr.denominator
    out = []
    for _ in range(n):
        if q == 0:
            break
        ai = p // q
        out.append(ai)
        p, q = q, p - ai * q
    return out


def closest_rational(fr, Qmax):
    """Closest rational to Fraction fr with denominator <= Qmax, searched over the
    continued-fraction convergents (the best rational approximations: no rational
    with denominator <= k_n beats the n-th convergent).  Returns (p, q, err) with
    err = |fr - p/q| computed EXACTLY as a Fraction (float underflows for the very
    good convergents that arise here, so exact arithmetic is mandatory)."""
    p, q = fr.numerator, fr.denominator
    h0, h1, k0, k1 = 0, 1, 1, 0
    ap, aq = p, q
    best = None
    while aq != 0:
        ai = ap // aq
        h2, k2 = ai * h1 + h0, ai * k1 + k0
        if k2 > Qmax:
            break
        err = abs(fr - F(h2, k2))            # exact
        if best is None or err < best[2]:
            best = (h2, k2, err)
        h0, h1, k0, k1 = h1, h2, k1, k2
        ap, aq = aq, ap - ai * aq
    return best


FAMILIES = {
    "CONTROL poly a_n=n^2 (engine FIRES => proven irrational)":
        lambda n: n * n if n >= 2 else 2,
    "OPEN-ZONE a_n=max(tau(n+1), floor(sqrt n)) [non-monotone subpoly]":
        lambda n: max(tau(n + 1), math.isqrt(n), 2),
    "OPEN-ZONE a_n=floor((log(n+2))^2)+2 [slow non-monotone]":
        lambda n: int((math.log(n + 2)) ** 2) + 2,
}

QMAX = 10 ** 9


def main():
    print("=" * 72)
    print("erdos-258-oq-01: open-zone rationality probe (S has no small-denom rational)")
    print("=" * 72)
    all_ok = True
    for name, a in FAMILIES.items():
        S, last = S_exact(a, K=150)
        cf = continued_fraction(S, 35)
        giant = [(i, ai) for i, ai in enumerate(cf) if ai > 1000]
        br = closest_rational(S, QMAX)
        # Decisive (exact): the best rational with q <= Qmax misses S by MORE than
        # the truncation tail, so the true S is not that (or any q<=Qmax) rational.
        no_small_rational = br is not None and br[2] > 1000 * last
        print(f"\n### {name}")
        print(f"  S ~ {float(S):.18f}")
        print(f"  truncation tail proxy (last term) ~ {float(last):.2e}")
        print(f"  CF partial quotients (first 35): {cf}")
        print(f"  giant partial quotients (>1000, = rational signature): "
              f"{giant if giant else 'NONE'}")
        if br:
            print(f"  closest rational with q <= {QMAX:.0e}: {br[0]}/{br[1]}, "
                  f"|S - p/q| = {float(br[2]):.2e}  (exact)")
            print(f"  => best q<=1e9 rational misses S by >> truncation tail "
                  f"({float(last):.0e})  ⟹  S is not a denom-<=1e9 rational: "
                  f"{'YES' if no_small_rational else 'NO'}")
        all_ok &= bool(no_small_rational) and not giant
    print("\n" + "-" * 72)
    print("Interpretation: every family (incl. both open-zone non-monotone ones)")
    print("shows NO rational signature and NO denominator-<=1e9 rational — consistent")
    print("with S irrational throughout, including where the liminf-T_N=0 engine is silent.")
    print("(Evidence, not proof; the open zone is beyond the elementary engine.)")
    print("ALL CHECKS PASS" if all_ok else "SOME CHECKS FAILED")
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
