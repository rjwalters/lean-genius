#!/usr/bin/env python3
"""
Certificate for `not_epsUniform_zero_of_not_pow_two` (Erdos1179OQ02Extremal.lean).

Claim (the dichotomy completed this session):
    For a finite abelian group G with |G| = N, an EXACTLY 0-uniform subset-sum
    set A (i.e. F_A(g) = 2^|A|/N for ALL g) exists  <=>  N is a power of two.

This script brute-forces the cyclic groups Z/N for small N and confirms:
  * N a power of two  -> at least one subset A of Z/N is exactly 0-uniform;
  * N NOT a power of two -> NO subset A of Z/N (any size) is exactly 0-uniform.

F_A(g) = #{ S subset of A : sum(S) = g  (mod N) }.
0-uniform means all N values of F_A are equal. Since they sum to 2^|A|, this
forces N | 2^|A|, i.e. N a power of two -- exactly the Lean lemma's content.

Build-free (stdlib only). Confirms the math; the Lean proof reuses the parent
`total_reprCount` + `Nat.dvd_prime_pow` and is independent of this check.
"""
from itertools import combinations


def is_pow_two(n: int) -> bool:
    return n > 0 and (n & (n - 1)) == 0


def repr_counts(A, N):
    """F_A(g) for all g in Z/N, over all 2^|A| subsets of A."""
    counts = [0] * N
    A = list(A)
    for r in range(len(A) + 1):
        for S in combinations(A, r):
            counts[sum(S) % N] += 1
    return counts


def has_zero_uniform_set(N):
    """True iff some subset A of Z/N is exactly 0-uniform."""
    elems = list(range(N))
    for k in range(0, N + 1):
        for A in combinations(elems, k):
            c = repr_counts(A, N)
            if len(set(c)) == 1:  # all F_A(g) equal => exactly 0-uniform
                return True, A, c[0]
    return False, None, None


def main():
    ok = True
    for N in range(2, 13):
        found, A, val = has_zero_uniform_set(N)
        expect = is_pow_two(N)
        status = "OK" if found == expect else "FAIL"
        if found != expect:
            ok = False
        wit = f" witness A={A}, F=={val}" if found else " (none, any size)"
        print(f"N={N:2d}  pow2={expect!s:5}  zero_uniform_exists={found!s:5}  "
              f"[{status}]{wit}")
    print()
    print("PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
