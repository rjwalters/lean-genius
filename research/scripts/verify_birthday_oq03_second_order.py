#!/usr/bin/env python3
"""
Second-order correction for the k=3 (triple) birthday threshold.

Parent gallery entry (birthday-problem-oq-03-oq-01-oq-02) proves the LEADING
order of the threshold:

    asympThreshold(d) = (6 d^2 ln 2)^{1/3}   ~  (6 ln 2)^{1/3} d^{2/3}

obtained by solving the *expected-triple-count* equation E(n,d) = C(n,3)/d^2 = ln 2.

OPEN QUESTION (this slug, ...-oq-02): compute the SECOND-ORDER correction, i.e.
the true median threshold

    n*(d) = min { n : P(some day has >=3 people) >= 1/2 }
          = min { n : P_no_triple(n,d) <= 1/2 }

and the claimed form  n*(d) = (6 d^2 ln 2)^{1/3} (1 + O(ln d / d^{1/3})).

This script computes n*(d) EXACTLY (in log-space, no approximation of the
combinatorics) and compares against three candidate models for the leading
term, to (a) confirm the leading constant and (b) empirically pin down the
true size/sign of the correction term.

P_no_triple(n,d) = (# functions [n]->[d] with every fiber <= 2) / d^n
                 = n! * [x^n] (1 + x + x^2/2)^d  / d^n
                 = sum_{j=0}^{floor(n/2)} C(d,j) C(d-j, n-2j) n! / (2^j) / d^n.

Everything done in log space with lgamma + logsumexp for numerical stability.
"""

import math
from math import lgamma, log, exp


def log_choose(a, b):
    if b < 0 or b > a:
        return float("-inf")
    return lgamma(a + 1) - lgamma(b + 1) - lgamma(a - b + 1)


def logsumexp(terms):
    terms = [t for t in terms if t != float("-inf")]
    if not terms:
        return float("-inf")
    m = max(terms)
    return m + log(sum(exp(t - m) for t in terms))


def log_p_no_triple(n, d):
    """log P(no day has >=3 people) for n people, d equally likely days."""
    if n > 2 * d:  # pigeonhole: impossible to keep all fibers <= 2
        return float("-inf")
    n_log_d = n * log(d)
    lfact_n = lgamma(n + 1)
    terms = []
    for j in range(0, n // 2 + 1):
        # C(d,j) doubleton boxes, C(d-j, n-2j) singleton boxes,
        # n!/2^j assignments of labelled balls; divide by d^n.
        t = (log_choose(d, j)
             + log_choose(d - j, n - 2 * j)
             + lfact_n
             - j * log(2.0)
             - n_log_d)
        terms.append(t)
    return logsumexp(terms)


def p_no_triple(n, d):
    return exp(log_p_no_triple(n, d))


def exact_median_threshold(d):
    """Smallest n with P_no_triple(n,d) <= 1/2."""
    n0 = (6 * d * d * math.log(2)) ** (1.0 / 3.0)
    lo = max(1, int(n0) - 40)
    # ensure lo is below threshold (P > 1/2); walk down if needed
    while lo > 1 and log_p_no_triple(lo, d) <= math.log(0.5):
        lo -= 20
    n = lo
    while log_p_no_triple(n, d) > math.log(0.5):
        n += 1
        if n > 2 * d:
            break
    return n


def expected_count_threshold(d):
    """Smallest n with E(n,d) = C(n,3)/d^2 >= ln 2 (the parent's definition)."""
    target = math.log(2)
    n = 1
    while math.comb(n, 3) / (d * d) < target:
        n += 1
    return n


def main():
    log2 = math.log(2)
    c0 = (6 * log2) ** (1.0 / 3.0)  # leading constant of n0/d^{2/3}
    print("Leading constant (6 ln2)^{1/3} =", c0)
    print()
    print(f"{'d':>8} {'n0=asymp':>10} {'n*_med':>7} {'n*_E':>6} "
          f"{'rel=(n*-n0)/n0':>15} {'rel*d^{1/3}':>12} {'rel*d^{1/3}/lnd':>16}")
    ds = [50, 100, 200, 365, 500, 1000, 2000, 5000, 10000, 20000, 50000, 100000]
    rows = []
    for d in ds:
        n0 = (6 * d * d * log2) ** (1.0 / 3.0)
        nmed = exact_median_threshold(d)
        nE = expected_count_threshold(d)
        rel = (nmed - n0) / n0
        d13 = d ** (1.0 / 3.0)
        scaled = rel * d13
        scaled_log = scaled / math.log(d)
        rows.append((d, n0, nmed, nE, rel, scaled, scaled_log))
        print(f"{d:>8} {n0:>10.3f} {nmed:>7} {nE:>6} {rel:>15.6f} "
              f"{scaled:>12.4f} {scaled_log:>16.5f}")
    print()
    print("Interpretation:")
    print(" - If rel ~ C/d^{1/3}, the column rel*d^{1/3} is ~constant.")
    print(" - If rel ~ C ln d /d^{1/3}, then rel*d^{1/3}/lnd is ~constant.")
    print(" - n*_med (true median) vs n*_E (expected-count) shows whether the")
    print("   parent's E=ln2 definition already captures the median threshold.")
    print()
    # Direct check: is the absolute correction n* - n0 growing, constant, or shrinking?
    print("Absolute correction n*_med - n0:")
    for (d, n0, nmed, nE, rel, scaled, scaled_log) in rows:
        print(f"  d={d:>7}:  n*-n0 = {nmed - n0:>8.3f}   "
              f"(n*-n0)/d^{{1/3}} = {(nmed - n0)/(d**(1/3)):>8.4f}")


if __name__ == "__main__":
    main()
