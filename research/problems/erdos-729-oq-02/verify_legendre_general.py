#!/usr/bin/env python3
"""
Independent numerical certificate for the general textbook Legendre identity
proved in proofs/Proofs/Erdos729LegendreGeneral.lean:

    v_p(n!) = (n - s_p(n)) / (p - 1)         (s_p(n) = base-p digit sum)

This is the division form of Mathlib's `sub_one_mul_padicValNat_factorial`
    (p - 1) * v_p(n!) = n - s_p(n).

We verify, for all primes p < 50 and all 0 <= n < 500:
  (a) p_adic_valuation(n!) equals the divided digit-sum expression (Nat division),
  (b) the multiplied form (p-1)*v = n - s_p(n) holds exactly,
  (c) (p-1) divides (n - s_p(n)) exactly (so Nat division is faithful).

Exits non-zero on any mismatch.
"""

import sys
from sympy import primerange


def digit_sum(p: int, n: int) -> int:
    s = 0
    while n > 0:
        s += n % p
        n //= p
    return s


def padic_val_factorial(p: int, n: int) -> int:
    # Legendre: sum_{i>=1} floor(n / p^i)
    v = 0
    pk = p
    while pk <= n:
        v += n // pk
        pk *= p
    return v


def main() -> int:
    mismatches = 0
    checks = 0
    for p in primerange(2, 50):
        for n in range(0, 500):
            v = padic_val_factorial(p, n)
            s = digit_sum(p, n)
            num = n - s  # >= 0 always (digit sum <= n)
            # (b) multiplied form
            if (p - 1) * v != num:
                print(f"MULT MISMATCH p={p} n={n}: (p-1)*v={ (p-1)*v } != n-s={num}")
                mismatches += 1
            # (c) divisibility
            if num % (p - 1) != 0:
                print(f"DIVISIBILITY FAIL p={p} n={n}: (n-s)={num} not divisible by p-1={p-1}")
                mismatches += 1
            # (a) division form (Nat division), matching the Lean statement
            if v != num // (p - 1):
                print(f"DIV-FORM MISMATCH p={p} n={n}: v={v} != (n-s)/(p-1)={num // (p-1)}")
                mismatches += 1
            checks += 1

    if mismatches:
        print(f"FAILED: {mismatches} mismatches over {checks} (p,n) pairs")
        return 1
    print(f"OK: general Legendre identity verified for {checks} (p,n) pairs "
          f"(primes p<50, n<500); 0 mismatches")
    return 0


if __name__ == "__main__":
    sys.exit(main())
