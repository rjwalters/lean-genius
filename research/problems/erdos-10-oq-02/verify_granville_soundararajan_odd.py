#!/usr/bin/env python3
"""
Erdős Problem #10, open question oq-02:
    Is the Granville–Soundararajan conjecture (k = 3 for odd integers) true?

Granville–Soundararajan (1998) conjectured that every odd integer n > 1 can be
written as a prime plus AT MOST 3 powers of 2:

        n = p + 2^{a_1} + ... + 2^{a_j},   p prime,   0 <= j <= 3.            (GS-odd)

The companion (even) conjecture asserts every even n >= 2 needs at most 4.
Both are OPEN. This script does NOT prove anything; it gathers reproducible
numerical evidence and pins down the precise combinatorial structure.

------------------------------------------------------------------------------
Reduction lemma (used throughout, and the cleanest formalizable fact here)
------------------------------------------------------------------------------
A nonnegative integer m is a sum of AT MOST k powers of 2 (a multiset of
exponents of size <= k, repetitions allowed) IF AND ONLY IF popcount(m) <= k.

  (=>) Merging 2^a + 2^a = 2^{a+1} only shrinks the multiset, so any size-<=k
       multiset collapses to <= k DISTINCT powers, i.e. popcount(m) <= k.
  (<=) If popcount(m) = t <= k then m is the sum of its t distinct set bits.

Hence, with S_k = { n : n = p + (<= k powers of 2), p prime },

        n in S_k  <=>  exists m >= 0 with popcount(m) <= k,
                       n - m >= 2, and (n - m) is prime.                       (*)

The empty multiset m = 0 handles "n is itself prime". (*) makes membership and
the MINIMAL number of powers cheap to compute.

------------------------------------------------------------------------------
What the evidence does and does NOT show (honest summary)
------------------------------------------------------------------------------
  * ODD side: in every range we can brute-force (here up to 3*10^6), every odd
    n is already in S_2 -- only <= 2 powers are ever needed.  So a direct sweep
    "confirms" GS-odd only trivially; it never even exercises the third power.
    The reason the conjecture is stated with k = 3 and not k = 2 is Crocker
    (1971): there are infinitely many odd n NOT in S_2 -- but those witnesses
    arise from covering systems and are astronomically large, far beyond any
    brute-force bound.  So small-N data is genuine but WEAK evidence for GS-odd.

  * EVEN side: brute force DOES exercise S_3.  A positive proportion (~5.6%) of
    even n genuinely need exactly 3 powers; the smallest is n = 906.  Every even
    n up to 10^6 is in S_3, and the first known even failure is Grechuk's
    1117175146 (in S_4, not S_3) -- the true k=3 boundary, on the even side.

Experiments
-----------
  E1. ODD sweep: every odd n in [3, N_ODD] is in S_3, with the minimal-#powers
      distribution (exposes that <=2 always suffices in range).
  E2. EVEN sweep: minimal-#powers distribution for even n in [2, N_EVEN],
      the smallest even n needing exactly 3, and that all even n <= N_EVEN
      are in S_3 (no failure before Grechuk's number).
  E3. Grechuk's counterexample: 1117175146 (even) NOT in S_3 but in S_4.
"""

import sys
from itertools import combinations
from sympy import isprime


def sieve(limit):
    is_p = bytearray([1]) * (limit + 1)
    is_p[0] = is_p[1] = 0
    i = 2
    while i * i <= limit:
        if is_p[i]:
            is_p[i * i:limit + 1:i] = bytearray(len(range(i * i, limit + 1, i)))
        i += 1
    return is_p


def offsets_by_popcount(N, kmax=3):
    """byk[j] = sorted list of m in [0,N] with popcount(m) exactly j, j<=kmax."""
    bits = []
    v = 1
    while v <= N:
        bits.append(v)
        v <<= 1
    byk = {j: [] for j in range(kmax + 1)}
    byk[0].append(0)
    nb = len(bits)
    for i in range(nb):
        if 1 <= kmax:
            byk[1].append(bits[i])
        for j in range(i + 1, nb):
            s2 = bits[i] + bits[j]
            if s2 <= N and 2 <= kmax:
                byk[2].append(s2)
            if kmax >= 3:
                for l in range(j + 1, nb):
                    s3 = s2 + bits[l]
                    if s3 <= N:
                        byk[3].append(s3)
    for j in byk:
        byk[j].sort()
    return byk


def min_powers(n, byk, is_p, kmax=3):
    """Minimal j in {0..kmax} with n = prime + (sum of j powers of 2); else None."""
    for j in range(0, kmax + 1):
        for m in byk[j]:
            if m >= n - 1:
                break
            if is_p[n - m]:
                return j
    return None


def in_S_k_big(n, k):
    """Membership for arbitrary n via sympy.isprime + popcount<=k offsets."""
    if n >= 2 and isprime(n):
        return True, 0
    bits = []
    v = 1
    while v < n:
        bits.append(v)
        v <<= 1
    for j in range(1, k + 1):
        for combo in combinations(bits, j):
            m = sum(combo)
            if m <= n - 2 and isprime(n - m):
                return True, j
    return False, None


def sweep(lo, hi, byk, is_p, label, kmax=3):
    dist = {j: 0 for j in range(kmax + 1)}
    failures = []
    smallest_needing_kmax = None
    largest_needing_kmax = None
    for n in range(lo, hi + 1, 2):
        j = min_powers(n, byk, is_p, kmax)
        if j is None:
            failures.append(n)
        else:
            dist[j] += 1
            if j == kmax:
                if smallest_needing_kmax is None:
                    smallest_needing_kmax = n
                largest_needing_kmax = n
    total = len(range(lo, hi + 1, 2))
    print(f"\n## {label}  (n in [{lo}, {hi}], count = {total})")
    if failures:
        print(f"  *** {len(failures)} NOT in S_{kmax}: "
              f"{failures[:20]}{' ...' if len(failures) > 20 else ''}")
    else:
        print(f"  PASS: every listed n is in S_{kmax} (no failure).")
    for j in range(kmax + 1):
        print(f"    min {j} power(s): {dist[j]:>8}  ({100.0 * dist[j] / total:5.2f}%)")
    print(f"  smallest needing exactly {kmax} powers: {smallest_needing_kmax}")
    print(f"  largest  needing exactly {kmax} powers (in range): {largest_needing_kmax}")
    return dist, failures


def main():
    N_ODD = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000
    N_EVEN = int(sys.argv[2]) if len(sys.argv) > 2 else 1_000_000
    N = max(N_ODD, N_EVEN)
    print(f"# Granville-Soundararajan oq-02 evidence  (N_ODD={N_ODD}, N_EVEN={N_EVEN})")
    is_p = sieve(N)
    byk = offsets_by_popcount(N, 3)

    # E1: odd side
    sweep(3, N_ODD if N_ODD % 2 == 1 else N_ODD - 1, byk, is_p,
          "E1 ODD sweep (GS-odd, k=3)", kmax=3)
    # extra: does <=2 already suffice for all odd in range?
    odd_not_S2 = [n for n in range(3, (N_ODD if N_ODD % 2 else N_ODD - 1) + 1, 2)
                  if min_powers(n, {0: byk[0], 1: byk[1], 2: byk[2]}, is_p, 2) is None]
    print(f"  [odd] count NOT in S_2 (would need the 3rd power): {len(odd_not_S2)} "
          f"{odd_not_S2[:8]}")
    print(f"  [odd] => in this range <=2 powers always suffice; the necessity of")
    print(f"         k=3 over k=2 (Crocker 1971) is beyond brute-force reach.")

    # E2: even side -- this is where S_3 is genuinely exercised
    sweep(2, N_EVEN if N_EVEN % 2 == 0 else N_EVEN - 1, byk, is_p,
          "E2 EVEN sweep (k=3 boundary)", kmax=3)

    # E3: Grechuk
    print(f"\n## E3 Grechuk counterexample (even, k=3)")
    G = 1117175146
    ok3, j3 = in_S_k_big(G, 3)
    ok4, j4 = in_S_k_big(G, 4)
    print(f"  {G}: even, popcount={bin(G).count('1')}")
    print(f"    in S_3 ? {ok3}" + ("" if ok3 else "  <-- confirms Grechuk: NOT in S_3"))
    print(f"    in S_4 ? {ok4}" + (f" (min {j4} powers)" if ok4 else "  (would break GS-even!)"))

    print("\n# done.")


if __name__ == "__main__":
    main()
