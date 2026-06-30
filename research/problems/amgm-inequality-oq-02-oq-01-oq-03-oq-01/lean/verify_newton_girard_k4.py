#!/usr/bin/env python3
"""
Durable certificate for the Newton-Girard k=4 closed form
    p4 = e1^4 - 4 e1^2 e2 + 2 e2^2 + 4 e1 e3 - 4 e4
and the supporting k=4 recurrence
    p4 = e1 p3 - e2 p2 + e3 p1 - 4 e4.

Checks (symbolically, over Q):
  1. The k=4 recurrence holds for n = 2..6 variables.
  2. The k=4 closed form holds for n = 2..6 variables.
  3. Substituting the proven lower closed forms (p3, p2, p1) into the recurrence
     reproduces the closed form exactly (the `ring` step in `psum_four_closed`).
  4. The explicit 4-variable instance matches.

A residual of 0 for n >= 4 variables certifies the identity universally
(MvPolynomial level), since the elementary symmetric polynomials e1..e4 are
algebraically independent once there are at least 4 variables.

Run:  python3 verify_newton_girard_k4.py
"""
import sympy as sp
from itertools import combinations


def psum(xs, k):
    return sum(x ** k for x in xs)


def esym(xs, k):
    return sum(sp.prod(c) for c in combinations(xs, k))


def main():
    syms = sp.symbols('x0:6')  # up to 6 variables
    all_ok = True

    print("== (1) k=4 recurrence  p4 = e1 p3 - e2 p2 + e3 p1 - 4 e4 ==")
    for n in range(2, 7):
        xs = syms[:n]
        e1, e2, e3, e4 = (esym(xs, k) for k in (1, 2, 3, 4))
        p1, p2, p3, p4 = (psum(xs, k) for k in (1, 2, 3, 4))
        res = sp.expand(e1 * p3 - e2 * p2 + e3 * p1 - 4 * e4 - p4)
        print(f"  n={n}: residual = {res}")
        all_ok &= (res == 0)

    print("== (2) k=4 closed form  p4 = e1^4 - 4 e1^2 e2 + 2 e2^2 + 4 e1 e3 - 4 e4 ==")
    for n in range(2, 7):
        xs = syms[:n]
        e1, e2, e3, e4 = (esym(xs, k) for k in (1, 2, 3, 4))
        p4 = psum(xs, 4)
        res = sp.expand(e1**4 - 4*e1**2*e2 + 2*e2**2 + 4*e1*e3 - 4*e4 - p4)
        print(f"  n={n}: residual = {res}")
        all_ok &= (res == 0)

    print("== (3) recurrence + lower closed forms  ==>  closed form (the `ring` step) ==")
    e1, e2, e3, e4 = sp.symbols('e1 e2 e3 e4')
    p1 = e1
    p2 = e1**2 - 2*e2
    p3 = e1**3 - 3*e1*e2 + 3*e3
    p4_from_rec = e1*p3 - e2*p2 + e3*p1 - 4*e4
    closed = e1**4 - 4*e1**2*e2 + 2*e2**2 + 4*e1*e3 - 4*e4
    res = sp.expand(p4_from_rec - closed)
    print(f"  residual = {res}")
    all_ok &= (res == 0)

    print("== (4) explicit 4-variable instance ==")
    a, b, c, d = sp.symbols('a b c d')
    e1 = a + b + c + d
    e2 = a*b + a*c + a*d + b*c + b*d + c*d
    e3 = a*b*c + a*b*d + a*c*d + b*c*d
    e4 = a*b*c*d
    lhs = a**4 + b**4 + c**4 + d**4
    rhs = e1**4 - 4*(e1**2*e2) + 2*e2**2 + 4*(e1*e3) - 4*e4
    res = sp.expand(lhs - rhs)
    print(f"  residual = {res}")
    all_ok &= (res == 0)

    print()
    print("ALL CHECKS PASSED" if all_ok else "FAILURE: a residual was nonzero")
    return 0 if all_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
