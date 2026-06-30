#!/usr/bin/env python3
"""
Durable numerical certificate for sum-of-divisors-oq-01
=======================================================

Euler's structural theorem (1747) on ODD perfect numbers:

    If N is odd and perfect (sigma(N) = 2N), then
        N = p^a * m^2
    with p prime, p = 1 (mod 4), a = 1 (mod 4), and gcd(p, m) = 1.

This is a *theorem* (fully provable), NOT the open existence question.
No odd perfect number is known; whether any exists is open. Euler's result
constrains the shape of any that might exist.

Key observation that makes this verifiable on MANY inputs (not the empty
set of odd perfect numbers): the structural conclusion follows already from
    v_2(sigma(N)) = 1
and N odd. Since sigma(N) = 2N with N odd gives v_2(sigma(N)) = v_2(2N) = 1,
the perfect case is a special instance of the lemma proved here on ~10^5
genuine witnesses.

Run:  python3 verify_euler_oddperfect.py   (requires sympy)
"""
import math
from sympy import factorint, isprime


def sigma(n: int) -> int:
    s = 1
    for p, a in factorint(n).items():
        s *= (p ** (a + 1) - 1) // (p - 1)
    return s


def v2(n: int) -> int:
    k = 0
    while n % 2 == 0:
        n //= 2
        k += 1
    return k


def check_L1():
    """sigma(p^a) is odd  <=>  a is even, for odd primes p.
    (sigma(p^a) = 1 + p + ... + p^a is a sum of a+1 odd terms.)"""
    primes = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
              59, 61, 67, 71, 73, 97, 101]
    bad = [(p, a) for p in primes for a in range(0, 12)
           if (sigma(p ** a) % 2 == 1) != (a % 2 == 0)]
    return bad


def check_L2():
    """For odd prime p and ODD exponent a:
        v_2(sigma(p^a)) == 1   <=>   (p = 1 mod 4  and  a = 1 mod 4).
    This isolates the unique 'special prime' whose sigma supplies the single
    factor of 2 in sigma(N) = 2N."""
    primes = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59,
              61, 67, 71, 73, 89, 97, 101, 109, 113]
    bad, witnessed = [], 0
    for p in primes:
        for a in range(1, 40, 2):
            val = v2(sigma(p ** a)) == 1
            cond = (p % 4 == 1 and a % 4 == 1)
            if val != cond:
                bad.append((p, a, v2(sigma(p ** a))))
            if val:
                witnessed += 1
    return bad, witnessed


def check_euler_form(bound: int):
    """EULER-FORM LEMMA (heart of the theorem).
    For every odd N in [3, bound) with v_2(sigma(N)) == 1:
        N = p^a * m^2, p prime, p = 1 mod 4, a = 1 mod 4, gcd(p, m) = 1.
    Returns (checked_count, failures)."""
    checked, fails = 0, []
    for N in range(3, bound, 2):
        if v2(sigma(N)) != 1:
            continue
        checked += 1
        f = factorint(N)
        odd_exp = [(p, a) for p, a in f.items() if a % 2 == 1]
        ok = (len(odd_exp) == 1)
        if ok:
            p, a = odd_exp[0]
            m2 = N // (p ** a)
            r = math.isqrt(m2)
            ok = (isprime(p) and p % 4 == 1 and a % 4 == 1
                  and r * r == m2 and m2 % p != 0)
        if not ok:
            fails.append((N, dict(f)))
    return checked, fails


def search_odd_perfect(bound: int):
    return [N for N in range(3, bound, 2) if sigma(N) == 2 * N]


if __name__ == "__main__":
    bad1 = check_L1()
    print("L1 (sigma(p^a) odd <=> a even):",
          "PASS" if not bad1 else f"FAIL {bad1[:5]}")

    bad2, wit = check_L2()
    print("L2 (a odd: v2(sigma(p^a))=1 <=> p=1,a=1 mod4):",
          "PASS" if not bad2 else f"FAIL {bad2[:8]}",
          f"| witnesses(v2==1)={wit}")

    BOUND = 2_000_000
    checked, fails = check_euler_form(BOUND)
    print(f"EULER-FORM over odd N in [3,{BOUND}) with v2(sigma)=1: "
          f"checked={checked}, FAILS={len(fails)}",
          "" if not fails else fails[:6])

    opn = search_odd_perfect(BOUND)
    print(f"odd perfect numbers < {BOUND}:", opn)
