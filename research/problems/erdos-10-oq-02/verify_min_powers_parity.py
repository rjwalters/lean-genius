#!/usr/bin/env python3
"""
Erdős #10 / OQ-02 — Granville–Soundararajan conjecture (k = 3 for odd n).

GS conjecture: every odd n > 1 is a sum of a prime and AT MOST 3 powers of 2
(n = p + 2^{a_1} + ... + 2^{a_j}, j ≤ 3); the even companion needs ≤ 4. Open.

Reduction lemma (Session 1):  with  minPowers(n) := min number of powers of two
(repetition allowed) needed so that n − (that sum) is prime, we have
    n ∈ S_k  ⟺  minPowers(n) ≤ k  ⟺  ∃ m, popcount(m) ≤ k and (n−m) prime,
because the minimum number of powers of two summing to a fixed m equals popcount(m)
(carrying 2^a+2^a → 2^{a+1} never increases below the binary representation).

----------------------------------------------------------------------------
WHAT THIS SESSION ADDS (Session 2 refinement)
----------------------------------------------------------------------------
Session 1 observed "every odd n ≤ 3·10^6 ∈ S_2, so S_3 is only TRIVIALLY satisfied
on the odd side" — but did not check whether 2 powers is ever NECESSARY on odds.
It is.  This script computes minPowers exactly over both parities and pins the
in-range CAPS:

  * smallest odd  n with minPowers(n) = 2  is  905  (= 5·181, a *de Polignac
    number*: odd, composite, and not of the form 2^a + prime).
  * smallest even n with minPowers(n) = 3  is  906  (Session 1).

So 905 and 906 are CONSECUTIVE: the smallest odd that genuinely needs 2 powers is
immediately followed by the smallest even that genuinely needs 3.  In range the
caps are minPowers ≤ 2 (odd) and ≤ 3 (even) — a clean +1 parity offset — and the
GS conjecture proposes the *true* caps are exactly one larger: 3 (odd) and 4 (even).
The extra power is the "safety margin" beyond the empirically observed in-range cap,
and the offset's mechanism is parity: subtracting an even power 2^a (a≥1) from an
odd n leaves an odd primality candidate, whereas an even n must first spend a power
to repair parity, costing one extra throughout.

Pure stdlib (sieve of Eratosthenes; no sympy in the hot loop).
Run:  python3 verify_min_powers_parity.py
"""

from math import isqrt

# ---------------------------------------------------------------------------
N = 1_000_000           # sweep bound (Session 1 used 3·10^6 for the odd S_2 claim)
# ---------------------------------------------------------------------------

def sieve(limit):
    is_p = bytearray([1]) * (limit + 1)
    is_p[0] = is_p[1] = 0
    for i in range(2, isqrt(limit) + 1):
        if is_p[i]:
            is_p[i*i::i] = bytearray(len(is_p[i*i::i]))
    return is_p

print(f"sieving primes up to {N} ...")
IS_P = sieve(N)
POWERS = []
p = 1
while p <= N:
    POWERS.append(p)
    p <<= 1
# index helpers for popcount-2/3 offsets
NP = len(POWERS)

def min_powers(n):
    """minPowers(n): fewest powers of two (popcount of the offset m) with n−m prime,
    n−m ≥ 2.  Returns 0,1,2,3 or 4+ (4+ means 'needs ≥4 in this search')."""
    if n >= 2 and IS_P[n]:
        return 0
    # k = 1 : offset m = 2^a
    for m in POWERS:
        r = n - m
        if r < 2:
            break
        if IS_P[r]:
            return 1
    # k = 2 : m = 2^a + 2^b  (a ≥ b)
    for i in range(NP):
        pa = POWERS[i]
        if n - pa < 2:
            break
        for j in range(i + 1):
            r = n - pa - POWERS[j]
            if r < 2:
                break
            if IS_P[r]:
                return 2
    # k = 3 : m = 2^a + 2^b + 2^c
    for i in range(NP):
        pa = POWERS[i]
        if n - pa < 2:
            break
        for j in range(i + 1):
            pb = pa + POWERS[j]
            if n - pb < 2:
                break
            for l in range(j + 1):
                r = n - pb - POWERS[l]
                if r < 2:
                    break
                if IS_P[r]:
                    return 3
    return 4  # needs ≥ 4 powers within this search window

def is_de_polignac(n):
    """odd n that is NOT prime and NOT of the form 2^a + prime  (needs ≥2 powers)."""
    if n < 2 or n % 2 == 0:
        return False
    if IS_P[n]:
        return False
    for m in POWERS:
        r = n - m
        if r < 2:
            break
        if IS_P[r]:
            return False
    return True

# ---------------------------------------------------------------------------
if __name__ == "__main__":
    print("="*74)
    print("Erdős #10 OQ-02 — minPowers parity caps for Granville–Soundararajan")
    print("="*74)

    odd_dist = {0: 0, 1: 0, 2: 0, 3: 0, 4: 0}
    even_dist = {0: 0, 1: 0, 2: 0, 3: 0, 4: 0}
    first_odd = {}
    first_even = {}

    print(f"sweeping n = 2 .. {N} (exact minPowers) ...")
    for n in range(2, N + 1):
        k = min_powers(n)
        if n & 1:
            odd_dist[k] = odd_dist.get(k, 0) + 1
            if k not in first_odd:
                first_odd[k] = n
        else:
            even_dist[k] = even_dist.get(k, 0) + 1
            if k not in first_even:
                first_even[k] = n

    def pct(d):
        tot = sum(d.values())
        return {k: f"{100*v/tot:5.2f}%" for k, v in d.items()}

    print()
    print("ODD  minPowers distribution:", dict(odd_dist))
    print("       as fractions        :", pct(odd_dist))
    print("EVEN minPowers distribution:", dict(even_dist))
    print("       as fractions        :", pct(even_dist))
    print()
    print("smallest n by minPowers value:")
    for k in range(0, 5):
        print(f"   k={k}:  odd → {first_odd.get(k, '— none in range')}"
              f"      even → {first_even.get(k, '— none in range')}")

    # ----- headline checks -----
    print()
    print("-"*74)
    print("Headline facts")
    print("-"*74)
    odd_cap = max(k for k, v in odd_dist.items() if v > 0)
    even_cap = max(k for k, v in even_dist.items() if v > 0)
    print(f"in-range cap:  odd minPowers ≤ {odd_cap}   even minPowers ≤ {even_cap}"
          f"   (+1 parity offset {'CONFIRMED' if even_cap == odd_cap + 1 else 'NOT seen'})")
    print(f"smallest odd needing exactly 2 powers : {first_odd.get(2)}"
          f"   (expected 905; de Polignac = {is_de_polignac(905)}, 905 = 5·181)")
    print(f"smallest even needing exactly 3 powers: {first_even.get(3)}"
          f"   (expected 906, Session 1)")
    print(f"905 & 906 consecutive, caps (2 odd, 3 even) attained back-to-back: "
          f"{first_odd.get(2) == 905 and first_even.get(3) == 906}")

    # distribution shift: even ≈ odd shifted +1, but only APPROXIMATELY
    print()
    print("distribution shift  even[k] vs odd[k-1]  (approximate, NOT an identity):")
    for k in (1, 2, 3):
        e = even_dist.get(k, 0); o = odd_dist.get(k - 1, 0)
        print(f"   even[{k}]={e:>7}  odd[{k-1}]={o:>7}  diff={e-o:+d}")
    print("   minPowers(2j) ≤ 1 + minPowers(2j-1) (spend 2^0 to fix parity, then the"
          " odd subproblem), with EQUALITY usually but not always: an even n can also")
    print("   reach the prime 2 directly via m = n-2 (an even offset), occasionally")
    print("   beating the +1 route — this is the source of the small count deviations.")
    # GS conjecture margin
    print()
    print(f"GS conjecture caps: 3 (odd) / 4 (even) = in-range caps ({odd_cap}/{even_cap}) + 1"
          f"   ⇒ the conjectured bound is exactly one power beyond what is forced in range.")
    print(f"No odd n ≤ {N} needs 3 powers; no even n ≤ {N} needs 4 — "
          f"consistent with (but far weaker than) GS, whose hard cases (Crocker odd ∉ S_2,")
    print(f"Grechuk even 1117175146 ∉ S_3) live well beyond brute force.")
