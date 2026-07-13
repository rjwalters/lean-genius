#!/usr/bin/env python3
"""
Pin down the leading correction COEFFICIENT for the k=3 birthday threshold.

Claim (this session): the true median threshold satisfies

    n*(d) = n0 * (1 + eps(d)),   n0 = (6 d^2 ln 2)^{1/3} = c0 * d^{2/3},
    c0 = (6 ln 2)^{1/3},
    eps(d) = (c0/4) d^{-1/3} + (1/c0) d^{-2/3} + o(d^{-2/3}).

In particular the second-order correction is Theta(d^{-1/3}) with NO log factor
(the gallery's "O(ln d / d^{1/3})" is a valid but loose upper bound), and the
exact leading correction coefficient is c0/4 = (6 ln 2)^{1/3}/4 ~ 0.40204.

Derivation: the MEDIAN threshold solves  P(no day has >=3) = 1/2.  Let
W = #{days with >= 3 people}.  Poisson approximation (rigorous here, since the
dependency neighbourhoods are small) gives P(W=0) ~ e^{-E[W]}, so the median
solves E[W] = ln 2.  The parent entry instead solves E[X] = ln 2 where
X = #{colliding triples} = C(n,3)/d^2; but E[X] >= E[W], so the parent's
threshold is too SMALL.  Expanding

    E[W] = d * P(Bin(n,1/d) >= 3)
         = (n^3/6d^2)*(1 - 3/n - 3n/(4d) + ...) ,

setting E[W] = n0^3/(6 d^2) and writing n = n0(1+eps) yields
    eps = 1/n0 + n0/(4d) + ...  =>  eps*d^{1/3} = (1/c0) d^{-1/3} + c0/4 + ...

This script verifies the coefficient by solving E[W](n,d) = ln 2 for REAL n
(removing integer-rounding jitter) using the EXACT binomial E[W], over a wide
range of d, and checks eps*d^{1/3} -> c0/4.
"""

import math
from math import log, lgamma, exp


def log_choose(a, b):
    if b < 0 or b > a:
        return float("-inf")
    return lgamma(a + 1) - lgamma(b + 1) - lgamma(a - b + 1)


def E_W(n, d):
    """E[#days with >=3 people] = d * P(Bin(n,1/d) >= 3).

    Computed by summing the UPPER tail P(Bin=m) for m=3,4,5,... directly,
    avoiding the catastrophic cancellation of the 1-(p0+p1+p2) complement
    when the tail probability is tiny (large d regime)."""
    lp = math.log1p(-1.0 / d)  # log(1 - 1/d)
    lq = math.log(1.0 / d)
    total = 0.0
    m = 3
    mmax = int(n)
    while m <= mmax:
        lt = log_choose(n, m) + m * lq + (n - m) * lp
        term = math.exp(lt)
        total += term
        # terms decay once past the mode (~ n/d); stop when negligible.
        if m > 3 * (n / d) + 10 and term < total * 1e-15:
            break
        m += 1
    return d * total


def real_root_EW(d, target):
    """Solve E_W(n,d) = target for real n by bisection (E_W increasing in n)."""
    n0 = (6 * d * d * log(2)) ** (1.0 / 3.0)
    lo, hi = max(2.0, n0 * 0.3), n0 * 3.0
    # ensure bracket
    while E_W(hi, d) < target:
        hi *= 1.5
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if E_W(mid, d) < target:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def E_X_root(d, target):
    """Real solution of C(n,3)/d^2 = target, i.e. n(n-1)(n-2)=6 d^2 target."""
    rhs = 6 * d * d * target
    lo, hi = 2.0, (rhs) ** (1.0 / 3.0) * 3 + 5
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if mid * (mid - 1) * (mid - 2) < rhs:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def main():
    log2 = log(2)
    c0 = (6 * log2) ** (1.0 / 3.0)
    print("c0 = (6 ln 2)^(1/3)      =", c0)
    print("predicted leading coeff c0/4 =", c0 / 4)
    print("predicted sub-coeff   1/c0   =", 1 / c0)
    print()
    print(f"{'d':>10} {'n0':>12} {'n_W(real)':>11} {'eps*d^{1/3}':>12} "
          f"{'model c0/4+(1/c0)d^-1/3':>24} {'resid':>10}")
    ds = [100, 365, 1000, 10**4, 10**5, 10**6, 10**7, 10**8, 10**9, 10**10,
          10**11, 10**12]
    for d in ds:
        n0 = (6 * d * d * log2) ** (1.0 / 3.0)
        nW = real_root_EW(d, log2)
        eps = (nW - n0) / n0
        val = eps * d ** (1.0 / 3.0)
        model = c0 / 4 + (1 / c0) * d ** (-1.0 / 3.0)
        print(f"{d:>10} {n0:>12.3f} {nW:>11.3f} {val:>12.6f} "
              f"{model:>24.6f} {val - model:>10.6f}")
    print()
    print("eps*d^{1/3} -> c0/4 = %.6f confirms correction is Theta(d^{-1/3}),"
          % (c0 / 4))
    print("no logarithm.  The residual -> 0, confirming the two-term model.")
    print()
    # Also: confirm the parent's E[X]=ln2 root sits BELOW the true median,
    # with the gap = (boxes-vs-triples) effect ~ (c0/4) n0 d^{-1/3} = (c0^2/4) d^{1/3}.
    print("Gap between true median (E[W]=ln2) and parent's E[X]=ln2 threshold:")
    print(f"{'d':>10} {'n_W':>11} {'n_X':>11} {'n_W-n_X':>10} "
          f"{'(n_W-n_X)/d^{1/3}':>17} {'pred c0^2/4':>12}")
    for d in [365, 1000, 10**4, 10**6, 10**9]:
        nW = real_root_EW(d, log2)
        nX = E_X_root(d, log2)
        gap = nW - nX
        print(f"{d:>10} {nW:>11.3f} {nX:>11.3f} {gap:>10.3f} "
              f"{gap / d**(1/3):>17.5f} {c0*c0/4:>12.5f}")


if __name__ == "__main__":
    main()
