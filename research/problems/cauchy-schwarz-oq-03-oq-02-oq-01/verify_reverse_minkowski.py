#!/usr/bin/env python3
"""Durable verification for cauchy-schwarz-oq-03-oq-02-oq-01.

Open question: formalize the REVERSE Minkowski inequality for 0 < p < 1.

Forward Minkowski (p >= 1, already formalized in the parent
Proofs/CauchySchwarzOQ03OQ02.lean via Mathlib `NNReal.Lp_add_le`):

    (sum (a_i + b_i)^p)^(1/p)  <=  (sum a_i^p)^(1/p) + (sum b_i^p)^(1/p)

For 0 < p < 1 the inequality REVERSES (for nonnegative a_i, b_i):

    (sum (a_i + b_i)^p)^(1/p)  >=  (sum a_i^p)^(1/p) + (sum b_i^p)^(1/p)   (RM)

This script independently checks, from first principles (no Lean):
  (C1) RM holds across many random nonnegative vectors and many p in (0,1);
  (C2) equality holds iff a, b are proportional (or one is 0);
  (C3) the proof route is sound: REVERSE Holder (0<p<1, negative conjugate
       exponent q = p/(p-1) < 0, v > 0):
           sum u_i v_i  >=  (sum u_i^p)^(1/p) * (sum v_i^q)^(1/q);
  (C4) the term-level bound Mathlib DOES have, `rpow_add_le_add_rpow`
       ((a+b)^p <= a^p + b^p for 0<=p<=1), goes the WRONG way for RM:
       it yields an UPPER bound (LHS <= (X+Y)^(1/p)), not the RM lower bound.

Exit code 0 prints "ALL CHECKS PASSED".  Pure stdlib; no dependencies.
"""

import random
import sys

EPS = 1e-9


def Lp(v, p):
    """The p-functional (sum v_i^p)^(1/p) for nonnegative v (a quasi-norm when 0<p<1)."""
    return sum(x ** p for x in v) ** (1.0 / p)


def check_reverse_minkowski():
    """(C1) RM lower bound holds for all tested 0<p<1, all n; 0 violations."""
    random.seed(11)
    violations = 0
    total = 0
    for p in [0.05, 0.1, 0.25, 0.5, 0.75, 0.9, 0.99]:
        for n in [1, 2, 3, 5, 8]:
            for _ in range(2000):
                a = [random.random() * 3 for _ in range(n)]
                b = [random.random() * 3 for _ in range(n)]
                lhs = Lp([a[i] + b[i] for i in range(n)], p)
                rhs = Lp(a, p) + Lp(b, p)
                total += 1
                if lhs < rhs - EPS:
                    violations += 1
    assert violations == 0, f"RM violated in {violations}/{total} trials"
    return total


def check_equality_iff_proportional():
    """(C2) equality iff proportional (b = c*a) or one vector is 0; else strict."""
    random.seed(12)
    for p in [0.2, 0.4, 0.6, 0.8]:
        # proportional => equality
        a = [random.random() * 3 + 0.1 for _ in range(4)]
        c = random.random() * 5 + 0.1
        b = [c * x for x in a]
        gap = Lp([a[i] + b[i] for i in range(4)], p) - (Lp(a, p) + Lp(b, p))
        assert abs(gap) < 1e-7, f"proportional not equality at p={p}: gap={gap}"
        # one zero => equality (Lp(0)=0)
        z = [0.0, 0.0, 0.0, 0.0]
        gap0 = Lp([a[i] + z[i] for i in range(4)], p) - (Lp(a, p) + Lp(z, p))
        assert abs(gap0) < 1e-7, f"one-zero not equality at p={p}: gap={gap0}"
        # disjoint support (non-proportional, both nonzero) => STRICT
        u = [1.0, 0.0]
        v = [0.0, 1.0]
        gapd = Lp([u[i] + v[i] for i in range(2)], p) - (Lp(u, p) + Lp(v, p))
        assert gapd > 1e-6, f"disjoint support not strict at p={p}: gap={gapd}"
    return True


def check_reverse_holder():
    """(C3) reverse Holder (the proof engine for RM) holds, >= direction, v>0."""
    random.seed(13)
    violations = 0
    for p in [0.2, 0.3, 0.5, 0.7, 0.9]:
        q = p / (p - 1.0)  # negative conjugate: 1/p + 1/q = 1, q < 0
        assert abs(1.0 / p + 1.0 / q - 1.0) < 1e-12
        assert q < 0
        for n in [2, 3, 5]:
            for _ in range(2000):
                u = [random.random() * 2 + 0.01 for _ in range(n)]
                v = [random.random() * 2 + 0.05 for _ in range(n)]  # strictly > 0
                lhs = sum(u[i] * v[i] for i in range(n))
                rhs = Lp(u, p) * (sum(x ** q for x in v) ** (1.0 / q))
                if lhs < rhs - 1e-7:
                    violations += 1
    assert violations == 0, f"reverse Holder violated {violations} times"
    return True


def check_term_subadditivity_wrong_direction():
    """(C4) `rpow_add_le_add_rpow` ((a+b)^p<=a^p+b^p, 0<=p<=1) is present in
    Mathlib but yields only an UPPER bound on the RM LHS, not the RM lower
    bound -- so it does NOT by itself prove reverse Minkowski.

        sum (a_i+b_i)^p <= sum a_i^p + sum b_i^p = X + Y          [term subadd]
        => (sum (a_i+b_i)^p)^(1/p) <= (X+Y)^(1/p)                 [1/p > 0 incr]

    while RM needs   (...)^(1/p) >= X^(1/p) + Y^(1/p).
    Both are consistent because (X+Y)^(1/p) >= X^(1/p)+Y^(1/p) for 1/p>=1;
    the term bound is the OUTER inequality, strictly weaker than RM.
    """
    random.seed(14)
    for p in [0.3, 0.5, 0.7]:
        for _ in range(3000):
            n = 4
            a = [random.random() * 3 for _ in range(n)]
            b = [random.random() * 3 for _ in range(n)]
            X = sum(x ** p for x in a)
            Y = sum(x ** p for x in b)
            inner = sum((a[i] + b[i]) ** p for i in range(n))
            # term subadditivity: inner <= X + Y
            assert inner <= X + Y + EPS
            lhs = inner ** (1.0 / p)
            upper = (X + Y) ** (1.0 / p)
            rm_lower = X ** (1.0 / p) + Y ** (1.0 / p)
            # the Mathlib-available bound is the OUTER sandwich:
            #   rm_lower <= lhs <= upper
            assert rm_lower - EPS <= lhs <= upper + EPS
            # and `upper` is NOT a proof of `rm_lower <= lhs` (it bounds above)
            assert upper >= rm_lower - EPS
    return True


def main():
    n = check_reverse_minkowski()
    check_equality_iff_proportional()
    check_reverse_holder()
    check_term_subadditivity_wrong_direction()
    print(f"(C1) reverse Minkowski: 0 violations over {n} random trials")
    print("(C2) equality iff proportional / one-zero; disjoint support strict")
    print("(C3) reverse Holder route (q=p/(p-1)<0) holds, 0 violations")
    print("(C4) Mathlib `rpow_add_le_add_rpow` gives outer UPPER bound only")
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
