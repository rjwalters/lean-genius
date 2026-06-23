#!/usr/bin/env python3
"""
Threshold-stability check for Erdős #1107, r=3 (cubeful) case
(OQ erdos-1107-oq-02-oq-01).

The merged ORIENT (#24190, `verify_cubeful_sums.py`) established that every n with the
"≤ 4 cubeful summands" property has a sharp effective threshold **N₃ = 2040**: the
exceptional set is exactly 45 numbers, the largest being 2039, with no exception in
(2039, 60000]. The ORIENT flagged one remaining *build-free* task before committing
2040 as the hypothesis of the eventual Lean `axiom cubeful_sum_threshold`:

    "confirm 2040 stability to a much larger bound (e.g. 10⁶) with a sieve-based DP."

This script does exactly that, efficiently:

  * Smallest-prime-factor sieve → cubeful (3-powerful: every prime exponent ≥ 3) basis
    up to N in O(N log log N), instead of per-number `sympy.factorint`.
  * `numpy` shift-OR bounded coin-change DP for "n is a sum of AT MOST 4 cubeful
    numbers", over the whole range [0, N] in a handful of vectorized passes.

It is build-free and reproducible (`python3 verify_cubeful_stability.py [N]`), and exits
non-zero unless the exceptional set is EXACTLY the known 45 (largest 2039) — so it
doubles as a regression guard that the threshold has not moved.

Results (this session, researcher-5):
  * N = 10⁶  : exceptions = the known 45, largest 2039, none in (2039, 10⁶].
  * N = 10⁷  : identical — exceptions = the known 45, largest 2039, none in (2039, 10⁷].
    A ~10-million-wide clean gap above the last exception hardens N₃ = 2040 substantially
    beyond the original 60000 bound. (The asymptotic itself — "every large n is a sum of
    ≤ 4 cubeful numbers" — remains open for r=3; 2040 is the effective threshold
    *conditional* on it, exactly parallel to the r=2 gallery entry.)
"""

import sys
import numpy as np

# The 45 known exceptions to "n = sum of ≤ 4 cubeful numbers" (from merged ORIENT #24190).
KNOWN_EXCEPTIONS = {
    5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 31, 38, 39, 46, 47, 53, 58, 69, 77, 79, 85,
    95, 101, 103, 111, 175, 196, 212, 228, 231, 247, 327, 444, 458, 490, 606, 662, 860,
    975, 1167, 1470, 1821, 1967, 2039,
}
THRESHOLD = 2040  # N₃: every n ≥ 2040 is (empirically) a sum of ≤ 4 cubeful numbers.


def smallest_prime_factor(n_max):
    """spf[i] = smallest prime factor of i (0 left for i that are prime > sqrt(n_max))."""
    spf = np.zeros(n_max + 1, dtype=np.int64)
    i = 2
    while i * i <= n_max:
        if spf[i] == 0:
            seg = spf[i * i :: i]
            spf[i * i :: i] = np.where(seg == 0, i, seg)
        i += 1
    return spf


def cubeful_basis(n_max, r=3):
    """All r-powerful numbers in [1, n_max]: every prime exponent ≥ r. 1 is admitted."""
    spf = smallest_prime_factor(n_max)
    basis = [1]
    for n in range(2, n_max + 1):
        m, ok = n, True
        while m > 1:
            p = int(spf[m]) or m  # spf==0 ⇒ m itself is prime (exponent 1 ⇒ not cubeful)
            e = 0
            while m % p == 0:
                m //= p
                e += 1
            if e < r:
                ok = False
                break
        if ok:
            basis.append(n)
    return basis


def reachable_at_most_k(n_max, basis, k):
    """Boolean array: reach[n] iff n is a sum of at most k elements of `basis`."""
    reach = np.zeros(n_max + 1, dtype=bool)
    reach[0] = True
    for _ in range(k):
        nxt = reach.copy()
        for b in basis:
            if b <= n_max:
                nxt[b:] |= reach[: n_max + 1 - b]
        reach = nxt
    return reach


def main():
    n_max = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000

    # --- Validation: reproduce the known squareful (r=2, ≤3) base case threshold 120. ---
    base = cubeful_basis(1000, r=2)
    reach2 = reachable_at_most_k(1000, base, 3)
    sq_exc = [n for n in range(1, 1001) if not reach2[n]]
    assert sq_exc == [7, 15, 23, 87, 111, 119], f"VALIDATION FAILED: {sq_exc}"
    print("VALIDATION PASSED: squareful (r=2, ≤3) reproduces exceptions {7,15,23,87,111,119}.")

    # --- The cubeful (r=3, ≤4) stability check over [1, n_max]. ---
    basis = cubeful_basis(n_max, r=3)
    reach = reachable_at_most_k(n_max, basis, 4)
    exc = [int(n) for n in np.flatnonzero(~reach) if n >= 1]
    above = [n for n in exc if n >= THRESHOLD]

    print(f"\n=== cubeful (r=3), at most 4 summands, range [1, {n_max}] ===")
    print(f"cubeful basis size: {len(basis)}")
    print(f"# exceptions: {len(exc)}   largest: {max(exc) if exc else None}")
    print(f"exceptions ≥ {THRESHOLD}: {above}")

    ok = True
    if set(exc) != KNOWN_EXCEPTIONS:
        ok = False
        print(f"FAIL: exception set differs from the known 45.\n  extra: "
              f"{sorted(set(exc) - KNOWN_EXCEPTIONS)}\n  missing: "
              f"{sorted(KNOWN_EXCEPTIONS - set(exc))}")
    if above:
        ok = False
        print(f"FAIL: found exception(s) ≥ {THRESHOLD} — threshold N₃ = {THRESHOLD} is WRONG.")

    if not ok:
        raise SystemExit(1)
    print(f"\nPASS: exception set is exactly the known 45 (largest 2039); "
          f"no exception in [{THRESHOLD}, {n_max}].")
    print(f"=> N₃ = {THRESHOLD} confirmed stable to {n_max} "
          f"(clean gap ~{n_max - 2039} above the last exception).")


if __name__ == "__main__":
    main()
