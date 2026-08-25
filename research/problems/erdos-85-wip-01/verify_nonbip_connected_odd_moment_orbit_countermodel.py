#!/usr/bin/env python3
"""Uniform real spectral countermodel to an odd-moment trace terminal.

This is deliberately an abstract spectral ledger, not a graph.  It shows
that the exact degree/trace/square-trace data for a connected defect spectrum,
the square-root relation, trace(A)=0, and nonnegativity of every odd closed-
walk trace do not bound the designated trace dimension from above.
"""

import argparse
import math

import sympy as sp


def symbolic_checks():
    q = sp.symbols("q", positive=True)
    count = q**2 - q - 2
    fixed_sum = 6 - q**2
    fixed_square_sum = q**2 + 8*q - 26
    variance_numerator = sp.factor(
        fixed_square_sum * count - fixed_sum**2
    )
    assert variance_numerator == 7*q**3 - 24*q**2 + 10*q + 16

    # Defect eigenvalues: q-1 once, q-2 with multiplicity q, q-5 once,
    # and `count` further roots with the displayed first two power sums.
    assert sp.expand(
        (q - 1) + q*(q - 2) + (q - 5) + fixed_sum
    ) == 0
    assert sp.expand(
        (q - 1)**2 + q*(q - 2)**2 + (q - 5)**2
        + fixed_square_sum - q**2*(q - 1)
    ) == 0

    # Adjacency signs: q; q roots over mu=q-2 with imbalance 2-q;
    # and one root -2 over mu=q-5.  All residual roots are sign-paired.
    assert sp.expand(q + (2 - q) - 2) == 0
    return variance_numerator


def check(q):
    assert q >= 8 and q % 4 == 0
    count = q*q - q - 2
    left_count = 2
    right_count = count - left_count
    total = 6 - q*q
    square_total = q*q + 8*q - 26
    mean = total / count
    variance = square_total / count - mean*mean
    assert variance > 0
    left = mean + math.sqrt(variance * right_count / left_count)
    right = mean - math.sqrt(variance * left_count / right_count)
    assert abs(left_count*left + right_count*right - total) < 1e-8
    assert abs(
        left_count*left*left + right_count*right*right - square_total
    ) < 1e-7
    assert -(q - 1) < right <= left < q - 1

    defect = [(q - 1, 1), (q - 2, q), (q - 5, 1),
              (left, left_count), (right, right_count)]
    assert sum(mult for _, mult in defect) == q*q
    assert abs(sum(mu*mult for mu, mult in defect)) < 1e-8
    assert abs(
        sum(mu*mu*mult for mu, mult in defect) - q*q*(q - 1)
    ) < 1e-7

    # The last two defect sectors have even multiplicity, so their adjacency
    # square roots can be paired with equal signs and vanish in every odd
    # moment.  The remaining odd trace is the exact closed form below.
    odd = {}
    for power in range(1, 18, 2):
        value = q**power + (2 - q) - 2**power
        odd[power] = value
        if power == 1:
            assert value == 0
        else:
            assert value > 0

    print(
        f"q={q} residual_counts=({left_count},{right_count}) "
        f"residual_mu=({left:.9f},{right:.9f}) "
        f"odd_traces={odd}"
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--q", type=int, nargs="*", default=[8, 16, 32])
    args = parser.parse_args()
    variance_numerator = symbolic_checks()
    print(f"symbolic_variance_numerator={variance_numerator}")
    for q in args.q:
        check(q)
    print("verified: uniform odd-moment spectral ledger survives")


if __name__ == "__main__":
    main()
