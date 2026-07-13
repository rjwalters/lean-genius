#!/usr/bin/env python3
"""
Durable certificate for amgm-inequality-oq-02-oq-01-oq-03.

Newton-Girard k=3 closed form and the ordered-triple partition that underpins the
concrete Finset proof (Approach 1 in problem.md).

Exact integer arithmetic, no floats. All identities below are what the Lean proof
must establish; this script is the ground-truth check for the multiplicities.
"""
import itertools, random

def syms(x):
    e1 = sum(x)
    e2 = sum(a*b for a, b in itertools.combinations(x, 2))
    e3 = sum(a*b*c for a, b, c in itertools.combinations(x, 3))
    p1 = e1
    p2 = sum(v**2 for v in x)
    p3 = sum(v**3 for v in x)
    return e1, e2, e3, p1, p2, p3

def check(x):
    n = len(x); s = range(n)
    e1, e2, e3, p1, p2, p3 = syms(x)
    # (1) main closed form -- the shipped theorem
    assert p3 == e1**3 - 3*e1*e2 + 3*e3, ("closed", x)
    # (2) recurrence (sibling, MvPolynomial) -- reused bearer
    assert p3 == e1*p2 - e2*p1 + 3*e3, ("recurrence", x)
    # (3) parent k=2 closed form
    assert p2 == e1**2 - 2*e2, ("k2", x)
    # (4) ordered-triple partition: (sum x)^3 = p3 + 3*D + 6*e3
    triple = sum(x[i]*x[j]*x[k] for i in s for j in s for k in s)
    D = sum(x[i]**2 * x[j] for i in s for j in s if i != j)   # exactly-two-equal rep
    assert triple == e1**3, ("cube", x)
    assert triple == p3 + 3*D + 6*e3, ("partition 1/3/6", x)
    # (5) D collapses: D = e1*p2 - p3
    assert D == e1*p2 - p3, ("D", x)
    # (6) ordered distinct pairs vs powerset-2: sum_{i!=j} xi xj = 2 e2
    od = sum(x[i]*x[j] for i in s for j in s if i != j)
    assert od == 2*e2, ("od2", x)

def main():
    random.seed(20260615)
    # fixed fixtures incl. degenerate/empty/repeats
    fixtures = [[], [5], [2, 3], [1, 1, 1], [-2, 0, 3], [1, 2, 3, 4], [-5, -5, 7, 0, 11]]
    for x in fixtures:
        check(x)
    for n in range(0, 9):
        for _ in range(400):
            check([random.randint(-12, 12) for _ in range(n)])
    print("PASS: Newton-Girard k=3 closed form + ordered-triple partition (1/3/6),")
    print("      D = e1*p2 - p3, and 2*e2 = sum_{i!=j} xi xj")
    print("      verified exactly over fixtures + n=0..8 (400 trials each).")

if __name__ == "__main__":
    main()
