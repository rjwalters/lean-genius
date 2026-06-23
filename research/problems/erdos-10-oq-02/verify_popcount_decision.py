#!/usr/bin/env python3
"""
Certificate for Erdos10OQ02Popcount.lean (S5).

Validates the popcount characterization that the Lean file proves and the
concrete `native_decide` witnesses it asserts (the file is build-pending under
a Docker blackout, so this cert stands in for the machine check).

The Lean statement is:
    RepWithAtMost k n  <->  (Nat.bitIndices n).length <= k

`Nat.bitIndices n` is the sorted list of positions of set bits of n, so
`(Nat.bitIndices n).length` is exactly the binary popcount of n.  We check:

  D1  (Nat.bitIndices n).length == popcount(n)              (definition match)
  D2  RepWithAtMost k n  <->  popcount(n) <= k              (the characterization)
  D3  the exact Lean witnesses:
        RepWithAtMost 1 8,  RepWithAtMost 0 0,  not RepWithAtMost 2 7
        not IsPrimePlusKPowers 2 906,  IsPrimePlusKPowers 3 906

Pure stdlib (sympy only for primality); exact arithmetic.
"""

from itertools import combinations_with_replacement
from sympy import isprime


def popcount(m: int) -> int:
    return bin(m).count("1")


def bitindices_length(m: int) -> int:
    # mirror Nat.bitIndices: positions of set bits, in increasing order
    return len([i for i in range(m.bit_length()) if (m >> i) & 1])


def rep_naive(k: int, n: int) -> bool:
    """True iff n is a sum of at most k powers of two (exponents may repeat)."""
    if n == 0:
        return True
    # exponents are < n (since 2^a <= n forces a < n); search multisets of size <= k
    max_exp = max(n.bit_length(), 1)
    exps = list(range(max_exp + 1))
    for j in range(0, k + 1):
        for combo in combinations_with_replacement(exps, j):
            if sum(2 ** a for a in combo) == n:
                return True
    return False


def is_prime_plus_k_powers(k: int, n: int) -> bool:
    for p in range(2, n + 1):
        if isprime(p) and popcount(n - p) <= k:
            return True
    return False


def main() -> None:
    ok = True

    # D1: bitIndices length == popcount
    for n in range(0, 5000):
        if bitindices_length(n) != popcount(n):
            print(f"D1 FAIL at n={n}")
            ok = False
            break
    else:
        print("D1 OK: (Nat.bitIndices n).length == popcount(n)  (n<5000)")

    # D2: RepWithAtMost k n  <->  popcount(n) <= k
    bad = None
    for n in range(0, 260):
        for k in range(0, 6):
            if rep_naive(k, n) != (popcount(n) <= k):
                bad = (k, n)
                break
        if bad:
            break
    if bad:
        print(f"D2 FAIL at (k,n)={bad}")
        ok = False
    else:
        print("D2 OK: RepWithAtMost k n <-> popcount(n) <= k  (n<260, k<6)")

    # D3: exact Lean witnesses
    checks = [
        ("RepWithAtMost 1 8", popcount(8) <= 1, True),
        ("RepWithAtMost 0 0", popcount(0) <= 0, True),
        ("not RepWithAtMost 2 7", popcount(7) <= 2, False),
        ("not IsPrimePlusKPowers 2 906", is_prime_plus_k_powers(2, 906), False),
        ("IsPrimePlusKPowers 3 906", is_prime_plus_k_powers(3, 906), True),
    ]
    for name, got, want in checks:
        if got != want:
            print(f"D3 FAIL: {name} (got {got}, want {want})")
            ok = False
    if ok:
        print("D3 OK: all five Lean witnesses match")

    print("\nALL CERTS PASS" if ok else "\nCERT FAILURE")


if __name__ == "__main__":
    main()
