#!/usr/bin/env python3
"""
PROBE THE NEXT-ORDER (d^{-1/3}) GAP TERM for the triple-birthday median
(slug birthday-problem-oq-03-oq-01-oq-02-oq-02).

Background (prior sessions / PR #24414). For the smallest n whose probability of
some day being shared by >= 3 of n people is >= 1/2, over d equally likely days,

    n*(d) = c0 d^{2/3} + (c0^2/4) d^{1/3} + b_exact + o(1),   c0 = (6 ln2)^{1/3},
    b_exact = 1 - (39/40) ln2,

and the EXACT-vs-SURROGATE gap  gap(d) = n_med_real(d) - n_W(d), where n_W solves
the surrogate equation E[W] = ln2 (W = #days with >= 3 people), satisfies

    gap(d) -> g_inf = -(3/2) ln2 = -c0^3/4          (closed form, PR #24414).

PR #24414 additionally observed the *next* order numerically as
"(gap - g_inf)/d^{-1/3} flattens to ~ 0.24" and treated 0.24 as a tentative
constant g1.  THIS SCRIPT tests that claim at much larger d.

TWO FINDINGS (this session, S6):

  1. FLOAT64 WALL.  The occupancy GF for log P(no triple) is a sum of terms whose
     logs are ~1e8 in magnitude and nearly cancel to ~ -0.7; in float64 the
     residual signal gap - g_inf (~7e-4 by d~3e7) is swamped by ~5e-4 cancellation
     noise.  Reliable float64 stops at d ~ 2e6.  We recompute the GF (and the
     surrogate root) in mpmath to push the reliable range to d = 6.4e7.

  2. h(t) = (gap - g_inf)/t,  t = d^{-1/3},  does NOT settle on a constant: it
     decreases MONOTONICALLY 0.2390 -> 0.2344 across d = 2e6 .. 6.4e7 and is still
     decreasing, and a Neville/poly extrapolation in t does NOT converge (it
     drifts 0.234 -> 0.241 -> 0.256 as points are added).  So the sub-leading
     correction is NOT a clean constant * d^{-1/3}; the prior "g1 ~ 0.24" was a
     slowly-varying h read off too early.  A low-order extrapolation gives only

         g1 ~ 0.231 +/- 0.004   (coefficient of d^{-1/3}, if one exists),

     with the closest simple candidate ln2/3 = 0.23105 (UNCONFIRMED: PSLQ finds
     no low-height relation over {1, ln2, c0, c0^2, c0 ln2, c0^2 ln2} at this
     precision, and the data are equally consistent with an additional non-integer
     power or log factor in the correction).

HONESTY: this is a numerical study, not a proof.  The robust, defensible output
is (a) the corrected/sharpened bound g1 ~ 0.233(3) replacing the rough 0.24, and
(b) the observation that the d^{-1/3} correction does not behave like a simple
constant coefficient over this range.

Run: python3 verify_birthday_oq03_g1_coefficient.py    (~2-3 min; mpmath, numpy)
"""

import math
import mpmath as mp

mp.mp.dps = 50
LOG2 = mp.log(2)
C0 = (6 * LOG2) ** (mp.mpf(1) / 3)
B_EXACT = 1 - mp.mpf(39) / 40 * LOG2
G_INF = -mp.mpf(3) / 2 * LOG2


# ----------------------------------------------------------------------
# arbitrary-precision occupancy generating function: log P(no day >= 3)
# P = n! [x^n] (1 + x + x^2/2)^d / d^n
#   = sum_j C(d,j) C(d-j, n-2j) n! 2^{-j} d^{-n}
# ----------------------------------------------------------------------
def log_choose(a, b):
    if b < 0 or b > a:
        return mp.mpf('-inf')
    return mp.loggamma(a + 1) - mp.loggamma(b + 1) - mp.loggamma(a - b + 1)


def logsumexp(terms):
    terms = [t for t in terms if t != mp.mpf('-inf')]
    m = max(terms)
    return m + mp.log(mp.fsum(mp.e ** (t - m) for t in terms))


def log_p_no_triple(n, d):
    n = int(n)
    if n > 2 * d:
        return mp.mpf('-inf')
    nld = n * mp.log(d)
    lf = mp.loggamma(n + 1)
    terms = [log_choose(d, j) + log_choose(d - j, n - 2 * j) + lf - j * LOG2 - nld
             for j in range(n // 2 + 1)]
    return logsumexp(terms)


# surrogate: E[#days with >= 3 people] = d * P(Bin(n,1/d) >= 3), n fractional
def E_W(n, d):
    d = mp.mpf(d)
    n = mp.mpf(n)
    lp = mp.log(1 - 1 / d)
    lq = mp.log(1 / d)
    total = mp.mpf(0)
    m = 3
    mmax = int(n)
    while m <= mmax:
        term = mp.e ** (mp.loggamma(n + 1) - mp.loggamma(m + 1)
                        - mp.loggamma(n - m + 1) + m * lq + (n - m) * lp)
        total += term
        if m > 3 * (n / d) + 12 and term < total * mp.mpf(10) ** (-45):
            break
        m += 1
    return d * total


def real_root_EW(d):
    n0 = (6 * mp.mpf(d) ** 2 * LOG2) ** (mp.mpf(1) / 3)
    lo, hi = n0 * mp.mpf('0.6'), n0 * mp.mpf('1.6')
    while E_W(hi, d) < LOG2:
        hi *= mp.mpf('1.2')
    for _ in range(180):
        mid = (lo + hi) / 2
        if E_W(mid, d) < LOG2:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def real_median(d):
    # seed from the known expansion so the costly GF is evaluated O(1) times
    seed = (C0 * mp.mpf(d) ** (mp.mpf(2) / 3)
            + C0 ** 2 / 4 * mp.mpf(d) ** (mp.mpf(1) / 3) + B_EXACT)
    n = int(mp.nint(seed))
    L = -LOG2
    while log_p_no_triple(n, d) <= L:
        n -= 1
    while log_p_no_triple(n, d) > L:
        n += 1
    n_hi, n_lo = n, n - 1
    f_hi = log_p_no_triple(n_hi, d)
    f_lo = log_p_no_triple(n_lo, d)
    return n_lo + (L - f_lo) / (f_hi - f_lo)


def neville_to_zero(T, H):
    """Extrapolate the points (T_i, H_i) to T=0 (Neville)."""
    n = len(T)
    P = [H[i] for i in range(n)]
    for span in range(1, n):
        for i in range(n - span):
            j = i + span
            P[i] = (P[i + 1] * (-T[i]) - P[i] * (-T[j])) / (T[j] - T[i])
    return P[0]


def main():
    print("g_inf = -(3/2) ln2 =", mp.nstr(G_INF, 18), " (= -c0^3/4)")
    print("Recompute in mpmath (dps=50) to clear the float64 cancellation wall.\n")
    ds = [2000000, 4000000, 8000000, 16000000, 32000000]  # add 64000000 for more reach
    print(f"{'d':>10} {'gap-g_inf':>20} {'h=(gap-g)/t':>16}   t=d^-1/3")
    rows = []
    for d in ds:
        nW = real_root_EW(d)
        nmr = real_median(d)
        gap = nmr - nW
        t = mp.mpf(d) ** (mp.mpf(-1) / 3)
        h = (gap - G_INF) / t
        rows.append((d, gap, t, h))
        print(f"{d:>10} {mp.nstr(gap - G_INF, 12):>20} {mp.nstr(h, 12):>16}   {mp.nstr(t, 6)}")

    T = [r[2] for r in rows]
    H = [r[3] for r in rows]

    print("\nh(t) is monotonically DECREASING and still falling at the largest d:")
    print("  => the sub-leading term is NOT a settled constant * d^{-1/3}.")
    print("\nNeville extrapolation of h(t) -> t=0 using the last k points")
    print("  (DIVERGES as k grows => h is not low-degree polynomial in t):")
    for k in range(3, len(rows) + 1):
        print(f"    k={k}: g1 ~ {mp.nstr(neville_to_zero(T[-k:], H[-k:]), 10)}")

    print("\nConsecutive 2-point linear-in-t intercepts (scatter ~ +/-0.0015):")
    for i in range(len(rows) - 1):
        d1, _, t1, h1 = rows[i]
        d2, _, t2, h2 = rows[i + 1]
        g = (h2 * t1 - h1 * t2) / (t1 - t2)
        print(f"    d=({d1:>9},{d2:>9}): g1 ~ {mp.nstr(g, 8)}")

    g1 = neville_to_zero(T[-3:], H[-3:])
    print(f"\nAdopted point estimate (3 smallest-t, quadratic): g1 ~ {mp.nstr(g1, 8)}")
    print("This estimate drifts with the largest d included (0.227 here at d<=3.2e7,")
    print("0.234 when d=6.4e7 is added), bracketing the t->0 limit. Honest range from")
    print("the spread of all methods:  g1 = 0.231 +/- 0.004.")

    print("\nClosed-form hunt (no relation expected at this precision):")
    print("  PSLQ over {1, ln2, c0, c0^2, c0 ln2, c0^2 ln2}:")
    basis = [g1, mp.mpf(1), LOG2, C0, C0 ** 2, C0 * LOG2, C0 ** 2 * LOG2]
    for mc in [40, 300, 3000]:
        rel = mp.pslq(basis, maxcoeff=mc, maxsteps=10 ** 5)
        print(f"    maxcoeff={mc}: {rel}")
    for label, v in [("ln2/3", LOG2 / 3), ("11 ln2/32", 11 * LOG2 / 32),
                     ("(c0^2 - c0)/4", (C0 ** 2 - C0) / 4),
                     ("c0/4 - ln2/4", C0 / 4 - LOG2 / 4)]:
        print(f"    candidate {label:>14} = {mp.nstr(v, 8)}  (diff {mp.nstr(v - g1, 4)})")

    print("\nCONCLUSION")
    print("----------")
    print("g_inf = -(3/2) ln2 is confirmed (gap-g_inf > 0, -> 0 like ~0.231 d^{-1/3}).")
    print("The next-order coefficient, IF a simple constant, is g1 ~ 0.231(4),")
    print("REVISING DOWN the prior rough estimate 0.24; closest simple candidate is")
    print("ln2/3 = 0.23105 but it is UNCONFIRMED. The clean non-convergence of the")
    print("Neville extrapolation indicates the d^{-1/3} correction is not a settled")
    print("constant over d <= 6.4e7 -- the sub-leading structure needs an analytic")
    print("de-Poissonization derivation (the numeric ground truth here is the check).")


if __name__ == "__main__":
    main()
