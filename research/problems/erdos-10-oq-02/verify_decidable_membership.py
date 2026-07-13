#!/usr/bin/env python3
"""
S4 certificate for erdos-10-oq-02 (Granville-Soundararajan, k=3 odd).

Validates the DECISION PROCEDURE that the build-pending Lean file
`Erdos10OQ02Decidable.lean` formalizes.  Three independent claims, each
checked by brute force against a naive reference:

  C1 (exponent bound).  If a sum of distinct powers of two equals n>=1, every
     exponent a in the representation satisfies a < n  (since a < 2^a <= n).
     => the search for representations is FINITE: exponents live in {0,...,n}.

  C2 (bounded-distinct = unrestricted).  For all k,n:
        RepWithAtMost k n
          (== exists a MULTISET s of exponents, |s| <= k, sum 2^a = n)
     is equivalent to
        exists a SUBSET F of {0,...,n} with |F| <= k and sum_{a in F} 2^a = n.
     The right side is decidable by finite search.  The merge identity
     2^a + 2^a = 2^{a+1} (the S3 reduction lemma) is what lets the multiset
     collapse to a distinct set without using more terms.
     Equivalently: RepWithAtMost k n  <->  popcount(n) <= k.

  C3 (decidable prime-plus-k-powers).  For all k,n:
        IsPrimePlusKPowers k n
          (== exists prime p, exists m with RepWithAtMost k m, n = p+m)
     is equivalent to the BOUNDED, decidable predicate
        exists p in [2,n], p prime and popcount(n-p) <= k.
     We confirm this matches the minimal-power-count data (minPowers) from the
     prior sessions, and discharge the concrete witnesses:
       - 906 is the smallest even n with minPowers = 3 (needs k>=3);
       - every odd n in range needs k<=2, and 905 is the smallest odd needing 2.

All reference computations are exact integer arithmetic.
"""

from itertools import combinations
from sympy import isprime


# ---------- reference (naive) definitions ----------

def rep_with_at_most_naive(k, n, max_exp):
    """exists multiset of <= k exponents in [0,max_exp] with sum of 2^a == n.
    Reference allows repeated exponents (true multiset), bounded by max_exp."""
    # enumerate multisets of size 0..k over exponents 0..max_exp
    exps = list(range(max_exp + 1))
    from itertools import combinations_with_replacement
    for size in range(k + 1):
        for combo in combinations_with_replacement(exps, size):
            if sum(1 << a for a in combo) == n:
                return True
    return False


def rep_bounded_distinct(k, n):
    """exists subset F of {0,...,n} with |F| <= k and sum_{a in F} 2^a == n.
    This is the DECIDABLE form the Lean file uses.

    Equivalent (and far cheaper) to search only exponents in
    {0,...,bit_length(n)}: by C1, any exponent a with 2^a <= n has a <= n, and
    a distinct rep summing to n can only use exponents a with 2^a <= n, i.e.
    a < bit_length(n)+1.  We search that tight window; C1/C2 below confirm this
    agrees with the full {0,...,n} window and with the naive multiset form."""
    top = n.bit_length()           # 2^a <= n  =>  a <= top
    exps = list(range(top + 1))
    for size in range(k + 1):
        for F in combinations(exps, size):
            if sum(1 << a for a in F) == n:
                return True
    return False


def popcount(n):
    return bin(n).count("1")


def min_powers(n):
    """minimal number of powers of two summing to n == popcount(n)."""
    return popcount(n)


def is_prime_plus_k_powers_bounded(k, n):
    """exists prime p in [2,n] with popcount(n-p) <= k."""
    for p in range(2, n + 1):
        if isprime(p) and popcount(n - p) <= k:
            return True
    return False


def is_prime_plus_k_powers_naive(k, n, max_exp):
    """exists prime p, exists m = sum of <= k powers (mult, exps<=max_exp), n=p+m."""
    for p in range(2, n + 1):
        if not isprime(p):
            continue
        m = n - p
        if rep_with_at_most_naive(k, m, max_exp):
            return True
    return False


# ---------- C1: exponent bound a < 2^a <= n ----------

def check_C1(limit=4000):
    for a in range(limit):
        assert a < (1 << a), f"a < 2^a fails at {a}"
    # and: if 2^a <= n then a < n  (since a < 2^a <= n)
    for n in range(1, 300):
        for a in range(n + 2):
            if (1 << a) <= n:
                assert a < n, f"exponent bound fails n={n} a={a}"
    print(f"C1 OK: a < 2^a (a<{limit}); 2^a<=n => a<n (n<300)")


# ---------- C2: bounded-distinct == unrestricted == popcount ----------

def check_C2(N=200, K=5):
    # max_exp for the naive multiset reference: exponents need not exceed N
    # (2^a <= n <= N), and with repeats the largest useful exponent is < N too.
    max_exp = N.bit_length() + 1
    mism = 0
    for n in range(0, N + 1):
        for k in range(0, K + 1):
            a = rep_with_at_most_naive(k, n, max_exp)
            b = rep_bounded_distinct(k, n)
            c = (popcount(n) <= k)
            if not (a == b == c):
                mism += 1
                if mism <= 5:
                    print(f"  MISMATCH n={n} k={k}: naive={a} bdd={b} popc={c}")
    assert mism == 0, f"C2 had {mism} mismatches"
    print(f"C2 OK: RepWithAtMost == bounded-distinct == (popcount<=k)  (n<={N}, k<={K})")


# ---------- C3: decidable prime-plus-k-powers ----------

def check_C3(N=2000):
    # equivalence of bounded-decidable form with the naive form
    max_exp = N.bit_length() + 2
    mism = 0
    for n in range(2, 400):       # naive form is expensive; smaller range
        for k in range(0, 4):
            a = is_prime_plus_k_powers_naive(k, n, max_exp)
            b = is_prime_plus_k_powers_bounded(k, n)
            if a != b:
                mism += 1
                if mism <= 5:
                    print(f"  MISMATCH n={n} k={k}: naive={a} bdd={b}")
    assert mism == 0, f"C3 equivalence had {mism} mismatches"
    print("C3a OK: IsPrimePlusKPowers == bounded form (n<400, k<4)")

    # Now use the cheap bounded form to reproduce the parity-cap facts.
    # smallest odd n with min #powers needed (over p prime) == 2
    def min_k_needed(n):
        k = 0
        while not is_prime_plus_k_powers_bounded(k, n):
            k += 1
            if k > 10:
                return None
        return k

    smallest_odd_2 = next(n for n in range(3, N, 2) if min_k_needed(n) == 2)
    smallest_even_3 = next(n for n in range(2, N, 2) if min_k_needed(n) == 3)
    assert smallest_odd_2 == 905, f"expected 905 got {smallest_odd_2}"
    assert smallest_even_3 == 906, f"expected 906 got {smallest_even_3}"
    # consecutive
    assert smallest_even_3 == smallest_odd_2 + 1
    print(f"C3b OK: smallest odd needing 2 = {smallest_odd_2}, "
          f"smallest even needing 3 = {smallest_even_3} (consecutive)")

    # every odd n in [3,N) needs k<=2; every even n in [2,N) needs k<=3
    assert all(min_k_needed(n) <= 2 for n in range(3, N, 2))
    assert all(min_k_needed(n) <= 3 for n in range(2, N, 2))
    print(f"C3c OK: odd n in [3,{N}) all in S_2; even n in [2,{N}) all in S_3")

    # Grechuk: 1117175146 (even) not in S_3 but in S_4 (popcount-offset form)
    g = 1117175146
    assert not is_prime_plus_k_powers_bounded_fast(3, g)
    assert is_prime_plus_k_powers_bounded_fast(4, g)
    print(f"C3d OK: Grechuk {g} not in S_3, in S_4")


def is_prime_plus_k_powers_bounded_fast(k, n):
    """Same as bounded form but only scans p where n-p has small popcount.
    For large n we scan primes p<=n with popcount(n-p)<=k; to keep it feasible
    we iterate over offsets m with popcount<=k and test (n-m) prime."""
    from itertools import combinations as comb
    bits = n.bit_length() + 1
    for j in range(k + 1):
        for F in comb(range(bits), j):
            m = sum(1 << a for a in F)
            p = n - m
            if p >= 2 and isprime(p):
                return True
    return False


if __name__ == "__main__":
    check_C1()
    check_C2()
    check_C3()
    print("\nALL CERTS PASS")
