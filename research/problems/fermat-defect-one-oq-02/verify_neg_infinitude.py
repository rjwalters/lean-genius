#!/usr/bin/env python3
"""
Verification for the negative-defect infinitude family at n = 3 formalized in
`proofs/Proofs/FermatDefectOneNegInfinitude.lean`.

The negative-defect Mahler family (parameter t >= 2):

    a = 9*t**3 - 1,  b = 9*t**4 - 3*t,  c = 9*t**4

is claimed to give, for every t >= 2, a primitive ordered negative-defect
witness a^3 + b^3 + 1 = c^3 (i.e. a^3 + b^3 - c^3 = -1), with c = 9*t**4
strictly increasing in t (hence infinitely many primitive witnesses).

This script checks, for a large range of t:
  (1) the cubic identity a^3 + b^3 + 1 = c^3,
  (2) the ordering 2 <= a <= b < c,
  (3) primitivity gcd(gcd(a,b),c) = 1,
  (4) the coprimality kernel gcd(9*t**3-1, 9*t**4) = 1 (lemma neg_family_coprime),
  (5) strict monotonicity of c = 9*t**4 (the injection 9*(n+2)**4).
"""
from math import gcd

def witness(t):
    return (9 * t**3 - 1, 9 * t**4 - 3 * t, 9 * t**4)

def check(tmax=20000):
    prev_c = None
    for t in range(2, tmax + 1):
        a, b, c = witness(t)
        assert a**3 + b**3 + 1 == c**3, f"(1) identity fails at t={t}"
        assert 2 <= a <= b < c, f"(2) ordering fails at t={t}: {(a,b,c)}"
        assert gcd(gcd(a, b), c) == 1, f"(3) not primitive at t={t}: {(a,b,c)}"
        assert gcd(9 * t**3 - 1, 9 * t**4) == 1, f"(4) kernel fails at t={t}"
        if prev_c is not None:
            assert c > prev_c, f"(5) c not strictly increasing at t={t}"
        prev_c = c
    return tmax

if __name__ == "__main__":
    n = check()
    print(f"All checks (1)-(5) PASS for t = 2..{n}.")
    for t in (2, 3, 4, 5):
        a, b, c = witness(t)
        print(f"  t={t}: (a,b,c)=({a},{b},{c}), a^3+b^3+1=c^3, gcd=1")
