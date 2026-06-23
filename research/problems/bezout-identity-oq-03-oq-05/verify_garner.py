#!/usr/bin/env python3
"""
Certificate for bezout-identity-oq-03-oq-05: Garner's mixed-radix CRT reconstruction.

Goal of the OQ: formalize Garner's algorithm in Lean as an executable extension of
the gallery's two-modulus `crtInt` (BezoutIdentityOQ03.lean), and prove it equals
the CRT solution.

This script is a BUILD-FREE certificate (stdlib only, exact integer arithmetic). It
pins the precise objects a Lean formalization must implement and proves, by exhaustive
+ randomized testing, the three facts the correctness theorem rests on:

  (G1) Garner's mixed-radix coefficients v_j, computed sequentially via the partial-
       product inverse, reconstruct an x that is ≡ r_i (mod m_i) for every i and lies
       in [0, ∏ m_i).
  (G2) Garner's x equals the iterated two-modulus lift built from `crtInt` (the
       reduction route the Lean proof should take: fold `crtInt` over the list).
  (G3) Both equal Python's brute-force / direct CRT solution (the ground truth).

It also exercises the exact recurrence and the partial-product coprimality bookkeeping
that the Lean termination/coprimality proof must discharge.

Run: python3 verify_garner.py
"""

from math import gcd, prod
from itertools import product as iproduct
import random


def modinv(a, m):
    """Modular inverse of a mod m (m > 1, gcd(a,m)=1). Mirrors Int.gcdA via ext-Euclid."""
    a %= m
    g, x, _ = ext_gcd(a, m)
    assert g == 1, f"no inverse: gcd({a},{m})={g}"
    return x % m


def ext_gcd(a, b):
    """Extended Euclid: returns (g, x, y) with a*x + b*y = g. Mirrors Int.gcdA/gcdB."""
    old_r, r = a, b
    old_s, s = 1, 0
    old_t, t = 0, 1
    while r != 0:
        q = old_r // r
        old_r, r = r, old_r - q * r
        old_s, s = s, old_s - q * s
        old_t, t = t, old_t - q * t
    return old_r, old_s, old_t


def pairwise_coprime(ms):
    for i in range(len(ms)):
        for j in range(i + 1, len(ms)):
            if gcd(ms[i], ms[j]) != 1:
                return False
    return True


# ---------------------------------------------------------------------------
# (1) Garner's mixed-radix reconstruction — the function the OQ asks to formalize.
#
#   v_1 = r_1                                            mod m_1
#   v_j = (r_j - (v_1 + v_2 m_1 + ... + v_{j-1} m_1..m_{j-2}))
#           * (m_1..m_{j-1})^{-1}                        mod m_j
#   x   = v_1 + v_2 m_1 + v_3 m_1 m_2 + ... + v_k m_1..m_{k-1}
#
# Implemented as a left fold carrying (partial value `x`, partial product `P`),
# which is exactly the `List.foldl` shape a Lean definition would use.
# ---------------------------------------------------------------------------
def garner(pairs):
    """pairs = [(m_1, r_1), ..., (m_k, r_k)], pairwise-coprime moduli. Returns (x, coeffs)."""
    x = 0          # running reconstructed value (the mixed-radix partial sum)
    P = 1          # running partial product m_1..m_{j-1}
    coeffs = []
    for (m, r) in pairs:
        # v_j = (r - x) * P^{-1}  (mod m), where x is the value of the first j-1 digits
        v = ((r - x) % m) * modinv(P % m, m) % m
        coeffs.append(v)
        x = x + v * P            # append the new mixed-radix digit
        P = P * m
    return x % P, coeffs


# ---------------------------------------------------------------------------
# (2) Iterated two-modulus lift via the gallery's crtInt — the REDUCTION route.
#
#   crtInt(m, n, a, b) = a*n*gcdB(m,n) + b*m*gcdA(m,n)   [BezoutIdentityOQ03.lean:232]
#   satisfies  ≡ a (mod m),  ≡ b (mod n).
#
#   Fold it: combine running solution (mod running product P) with next (m_j, r_j).
#   The Lean correctness proof reduces Garner to this by induction on the list.
# ---------------------------------------------------------------------------
def crtInt(m, n, a, b):
    g, gcdA, gcdB = ext_gcd(m, n)
    assert g == 1
    return a * n * gcdB + b * m * gcdA


def crt_fold(pairs):
    x, P = pairs[0][1] % pairs[0][0], pairs[0][0]
    for (m, r) in pairs[1:]:
        x = crtInt(P, m, x, r) % (P * m)
        P *= m
    return x % P


# ---------------------------------------------------------------------------
# (3) Ground-truth direct CRT (brute force for small products, sympy-free formula else).
# ---------------------------------------------------------------------------
def crt_direct(pairs):
    P = prod(m for m, _ in pairs)
    x = 0
    for (m, r) in pairs:
        Pi = P // m
        x = (x + r * Pi * modinv(Pi % m, m)) % P
    return x


def check(pairs, label, exhaustive_brute=False):
    P = prod(m for m, _ in pairs)
    gx, coeffs = garner(pairs)
    fx = crt_fold(pairs)
    dx = crt_direct(pairs)
    # (G1) congruences + range
    for (m, r) in pairs:
        assert gx % m == r % m, f"{label}: Garner congruence fail mod {m}"
    assert 0 <= gx < P, f"{label}: Garner out of range"
    # mixed-radix digit bound: 0 <= v_j < m_j
    for (m, _), v in zip(pairs, coeffs):
        assert 0 <= v < m, f"{label}: digit out of range"
    # (G2) Garner == crt fold (the reduction)
    assert gx == fx, f"{label}: Garner != crtInt-fold ({gx} vs {fx})"
    # (G3) == direct ground truth
    assert gx == dx, f"{label}: Garner != direct CRT ({gx} vs {dx})"
    if exhaustive_brute:
        # independent brute-force search over [0,P)
        sols = [y for y in range(P) if all(y % m == r % m for m, r in pairs)]
        assert sols == [gx], f"{label}: brute uniqueness fail {sols} vs {gx}"
    return P


def main():
    random.seed(12345)  # deterministic
    total = 0

    # --- A. Exhaustive small cases with full brute-force uniqueness check ---
    small_mods = [2, 3, 4, 5, 7, 8, 9, 11, 13]
    a_cases = 0
    for k in (2, 3):
        for combo in iproduct(small_mods, repeat=k):
            ms = list(combo)
            if len(set(ms)) != k or not pairwise_coprime(ms):
                continue
            P = prod(ms)
            if P > 5000:
                continue
            # test all residue tuples for tiny products, else a sample
            res_iter = iproduct(*[range(m) for m in ms]) if P <= 600 else \
                       [tuple(random.randrange(m) for m in ms) for _ in range(20)]
            for rs in res_iter:
                check(list(zip(ms, rs)), f"small k={k} {ms}", exhaustive_brute=(P <= 600))
                a_cases += 1
    print(f"[A] exhaustive/sampled small cases: {a_cases} PASS")
    total += a_cases

    # --- B. Large randomized pairwise-coprime systems (big primes & prime powers) ---
    bank = [3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32,
            37, 41, 43, 47, 49, 53, 59, 61, 64, 67, 71, 73, 79, 81, 83]
    b_cases = 0
    for _ in range(4000):
        k = random.randint(2, 7)
        # greedily pick pairwise-coprime moduli
        ms = []
        random.shuffle(bank)
        for m in bank:
            if all(gcd(m, x) == 1 for x in ms):
                ms.append(m)
            if len(ms) == k:
                break
        if len(ms) < 2:
            continue
        rs = [random.randrange(m) for m in ms]
        check(list(zip(ms, rs)), f"rand {ms}")
        b_cases += 1
    print(f"[B] randomized large coprime systems: {b_cases} PASS")
    total += b_cases

    # --- C. Order-independence: Garner's value is independent of modulus order ---
    c_cases = 0
    for _ in range(1000):
        ms = [random.choice([3, 5, 7, 11, 13, 17, 19, 23])]
        bank2 = [3, 5, 7, 11, 13, 17, 19, 23]
        random.shuffle(bank2)
        for m in bank2:
            if all(gcd(m, x) == 1 for x in ms) and m not in ms:
                ms.append(m)
            if len(ms) == 4:
                break
        if len(set(ms)) < 2:
            continue
        rs = [random.randrange(m) for m in ms]
        pairs = list(zip(ms, rs))
        x0, _ = garner(pairs)
        perm = pairs[:]
        random.shuffle(perm)
        x1, _ = garner(perm)
        assert x0 == x1, f"order dependence! {x0} vs {x1}"
        c_cases += 1
    print(f"[C] order-independence checks: {c_cases} PASS")
    total += c_cases

    # --- D. Mixed-radix reconstruction identity is exact ---
    d_cases = 0
    for _ in range(500):
        bank3 = [3, 5, 7, 11, 13]
        random.shuffle(bank3)
        ms = bank3[:random.randint(2, 5)]
        rs = [random.randrange(m) for m in ms]
        pairs = list(zip(ms, rs))
        x, coeffs = garner(pairs)
        # x == sum v_j * (m_1..m_{j-1})
        acc, P = 0, 1
        for (m, _), v in zip(pairs, coeffs):
            acc += v * P
            P *= m
        assert acc % P == x, "mixed-radix expansion mismatch"
        d_cases += 1
    print(f"[D] mixed-radix expansion identity: {d_cases} PASS")
    total += d_cases

    print(f"\nALL {total} CHECKS PASS — Garner == crtInt-fold == direct CRT, "
          f"congruences + range + order-independence verified.")


if __name__ == "__main__":
    main()
