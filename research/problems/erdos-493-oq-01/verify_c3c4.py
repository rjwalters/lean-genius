#!/usr/bin/env python3
"""
Verification for the C3/C4 structural theorems added to
`proofs/Proofs/Erdos493OQ01.lean` (Session 3).

The product-minus-sum map is (a, b) |-> a*b - (a+b) over a, b >= 2, with the
central bijection  n = a*b-(a+b), a,b>=2  <=>  n+1 = u*v, u,v>=1  (u=a-1, v=b-1).

C3 (hasSquareRep_iff):
    exists a>=2 with n = a*a-(a+a)        <=>   n+1 is a perfect square.

C4 (hasNontrivialRep_iff_factor):
    exists a,b>=3 with n = a*b-(a+b)      <=>   n+1 = u*v with u,v>=2 (composite).
"""
import math

def square_rep(n):
    a = 2
    while a * a - 2 * a <= n:
        if a * a - (a + a) == n:
            return (a, a)
        a += 1
    return None

def is_perfect_square(m):
    if m < 0:
        return False
    r = math.isqrt(m)
    return r * r == m

def nontrivial_rep(n):
    # both a, b >= 3
    a = 3
    while a * 3 - (a + 3) <= n:
        b = a
        while a * b - (a + b) <= n:
            if a * b - (a + b) == n:
                return (a, b)
            b += 1
        a += 1
    return None

def composite(m):
    if m < 2:
        return False
    return any(m % d == 0 for d in range(2, math.isqrt(m) + 1))

def main(nmax=2000):
    for n in range(0, nmax + 1):
        assert (square_rep(n) is not None) == is_perfect_square(n + 1), \
            f"C3 fails at n={n}"
        assert (nontrivial_rep(n) is not None) == composite(n + 1), \
            f"C4 fails at n={n}"
    print(f"C3 (square-rep <=> n+1 perfect square): PASS for n=0..{nmax}")
    print(f"C4 (nontrivial-rep <=> n+1 composite):  PASS for n=0..{nmax}")

if __name__ == "__main__":
    main()
