#!/usr/bin/env python3
"""Durable verification for arithmetic-series-oq-02-oq-02-oq-02.

OQ: Connect the project's *rising* (parallel) Vandermonde convolution

    parallel_vandermonde:  sum_{i+j=n} C(i+a, a) * C(j+b, b) = C(n+a+b+1, a+b+1)
    (proved by induction in proofs/Proofs/ArithmeticSeriesOQ02OQ02.lean:61)

to the *standard* Vandermonde convolution

    Nat.add_choose_eq:     C(m+n, k) = sum_{i+j=k} C(m, i) * C(n, j)
    (Mathlib, Mathlib/Data/Nat/Choose/Vandermonde.lean, theorem Nat.add_choose_eq,
     confirmed present at repo pin v4.26.0 / 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67)

The connection is the UPPER-NEGATION duality. Over the integers,

    C(i+a, a) = C(i+a, i) = (-1)^i * C(-a-1, i)            (upper negation)

so the rising convolution equals the standard convolution evaluated at the
NEGATIVE upper indices -a-1, -b-1, sandwiched by two upper negations:

    sum_{i+j=n} C(i+a,a) C(j+b,b)
      = (-1)^n sum_{i+j=n} C(-a-1, i) C(-b-1, j)           (upper negation, twice)
      = (-1)^n C(-a-b-2, n)                                 (standard Vandermonde, integer upper index)
      = (-1)^n (-1)^n C(n+a+b+1, n)                         (upper negation, back to N)
      = C(n+a+b+1, a+b+1).

This script verifies, by exact integer arithmetic over a sweep:
  (1) the standard Vandermonde (the Mathlib Nat.add_choose_eq form),
  (2) the project's rising parallel_vandermonde,
  (3) the upper-negation identity C(i+a,a) = (-1)^i C(-a-1, i),
  (4) the integer-upper-index Vandermonde sum_{i+j=n} C(-a-1,i)C(-b-1,j) = C(-a-b-2,n),
  (5) the full bridge chain (1)->(2) via (3)+(4),
  (6) a generating-function cross-check: [x^n] (1-x)^{-(a+1)} (1-x)^{-(b+1)} = C(n+a+b+1, n).

All assertions use exact arithmetic; no floating point.  sympy.binomial
implements the generalized binomial for negative/integer upper index.
"""

from sympy import binomial, symbols, series, Rational, simplify
from sympy.abc import x


def C(top, bot):
    """Exact (generalized) binomial coefficient, integer arguments."""
    return binomial(top, bot)


def check_standard_vandermonde(MAX=14):
    """(1) C(m+n,k) = sum_{i=0..k} C(m,i) C(n,k-i)  -- the Mathlib form."""
    for m in range(MAX):
        for n in range(MAX):
            for k in range(m + n + 1):
                lhs = C(m + n, k)
                rhs = sum(C(m, i) * C(n, k - i) for i in range(k + 1))
                assert lhs == rhs, (m, n, k, lhs, rhs)
    print(f"(1) standard Vandermonde (Nat.add_choose_eq form): PASS  [m,n<{MAX}]")


def check_rising_vandermonde(MAX=12):
    """(2) sum_{i+j=n} C(i+a,a) C(j+b,b) = C(n+a+b+1, a+b+1)  -- parallel_vandermonde."""
    for a in range(MAX):
        for b in range(MAX):
            for n in range(MAX):
                lhs = sum(C(i + a, a) * C((n - i) + b, b) for i in range(n + 1))
                rhs = C(n + a + b + 1, a + b + 1)
                assert lhs == rhs, (a, b, n, lhs, rhs)
    print(f"(2) rising parallel_vandermonde: PASS  [a,b,n<{MAX}]")


def check_upper_negation(MAX=20):
    """(3) C(i+a, a) = (-1)^i C(-a-1, i)  (upper negation over the integers)."""
    for a in range(MAX):
        for i in range(MAX):
            lhs = C(i + a, a)                      # = C(i+a, i)
            rhs = (-1) ** i * C(-a - 1, i)
            assert lhs == rhs, (a, i, lhs, rhs)
    print(f"(3) upper-negation C(i+a,a)=(-1)^i C(-a-1,i): PASS  [a,i<{MAX}]")


def check_integer_upper_vandermonde(MAX=12):
    """(4) sum_{i+j=n} C(-a-1,i) C(-b-1,j) = C(-a-b-2, n).

    Standard Vandermonde extended to negative (integer) upper indices.
    Equivalent to the generating-function product (1+x)^{-a-1}(1+x)^{-b-1}.
    """
    for a in range(MAX):
        for b in range(MAX):
            for n in range(MAX):
                lhs = sum(C(-a - 1, i) * C(-b - 1, n - i) for i in range(n + 1))
                rhs = C(-a - b - 2, n)
                assert lhs == rhs, (a, b, n, lhs, rhs)
    print(f"(4) integer-upper Vandermonde C(-a-1,*)*C(-b-1,*)=C(-a-b-2,n): PASS  [a,b,n<{MAX}]")


def check_bridge_chain(MAX=12):
    """(5) The full chain rewriting rising -> standard via (3)+(4), term by term.

        sum_{i+j=n} C(i+a,a) C(j+b,b)
          ==(3)==  (-1)^n sum_{i+j=n} C(-a-1,i) C(-b-1,j)
          ==(4)==  (-1)^n C(-a-b-2, n)
          ==(3)==  C(n+a+b+1, n)  =  C(n+a+b+1, a+b+1).
    """
    for a in range(MAX):
        for b in range(MAX):
            for n in range(MAX):
                rising = sum(C(i + a, a) * C((n - i) + b, b) for i in range(n + 1))
                # step (3): pull each C(.,.) to negative upper index
                neg = sum(((-1) ** i * C(-a - 1, i)) * ((-1) ** (n - i) * C(-b - 1, n - i))
                          for i in range(n + 1))
                assert rising == neg, ("3", a, b, n)
                # step (4): integer-upper Vandermonde
                folded = (-1) ** n * C(-a - b - 2, n)
                assert neg == folded, ("4", a, b, n)
                # step (3) back to N: (-1)^n C(-a-b-2,n) = C(n+a+b+1, n)
                final = C(n + a + b + 1, n)
                assert folded == final, ("3back", a, b, n)
                assert final == C(n + a + b + 1, a + b + 1), ("sym", a, b, n)
    print(f"(5) full bridge chain rising<->standard: PASS  [a,b,n<{MAX}]")


def check_generating_function(AMAX=6, NMAX=10):
    """(6) [x^n] (1-x)^{-(a+1)} (1-x)^{-(b+1)} = C(n+a+b+1, n).

    The generating-function origin of the rising convolution:
    (1-x)^{-(a+1)} = sum_n C(n+a, a) x^n, and the product collapses the
    exponents to (a+b+2).  This is the (1+x) <-> (1-x)^{-1} dual of (4).
    """
    for a in range(AMAX):
        for b in range(AMAX):
            f = (1 - x) ** (-(a + 1)) * (1 - x) ** (-(b + 1))
            s = series(f, x, 0, NMAX + 1).removeO()
            for n in range(NMAX + 1):
                coeff = s.coeff(x, n)
                assert coeff == C(n + a + b + 1, n), (a, b, n, coeff)
    print(f"(6) generating-function cross-check: PASS  [a,b<{AMAX}, n<={NMAX}]")


if __name__ == "__main__":
    check_standard_vandermonde()
    check_rising_vandermonde()
    check_upper_negation()
    check_integer_upper_vandermonde()
    check_bridge_chain()
    check_generating_function()
    print("\nALL CHECKS PASSED — the rising parallel_vandermonde is the standard")
    print("Vandermonde (Nat.add_choose_eq) under upper-negation duality.")
