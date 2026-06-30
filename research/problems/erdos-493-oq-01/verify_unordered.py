#!/usr/bin/env python3
"""Verify the unordered representation-count identity (Part III of Erdos493OQ01.lean):

    2 * |{ {a,b} : a,b >= 2, a*b-(a+b) = n }|  =  tau(n+1) + [n+1 is a perfect square]

i.e. the number of unordered representations is ceil(tau(n+1)/2). This sharpens the
C5 primality/uniqueness capstone into a full count. Brute force vs. the closed form.
"""
import math


def tau(m: int) -> int:
    return sum(1 for d in range(1, m + 1) if m % d == 0)


def unordered_count(n: int) -> int:
    c = 0
    for a in range(2, n + 3):
        for b in range(a, n + 3):  # a <= b : canonical unordered rep
            if a * b - (a + b) == n:
                c += 1
    return c


def main() -> None:
    failures = 0
    for n in range(0, 400):
        lhs = 2 * unordered_count(n)
        m = n + 1
        is_sq = 1 if math.isqrt(m) ** 2 == m else 0
        rhs = tau(m) + is_sq
        if lhs != rhs:
            failures += 1
            print(f"FAIL n={n}: 2*unordered={lhs}  tau(n+1)+[sq]={rhs}")
    if failures == 0:
        print("ALL PASS (n = 0..399): 2*unordered = tau(n+1) + [n+1 perfect square]")
    else:
        print(f"{failures} FAILURES")


if __name__ == "__main__":
    main()
