#!/usr/bin/env python3
"""
Exact verification for wilsons-theorem-oq-02-ext-oq-01.

OPEN QUESTION (OQ-01 of wilsons-theorem-oq-02-ext):
    Can the two-involution trick be formalized as a GENERAL theorem about
    finite abelian groups (not just the unit group (ZMod n)^x)?

GENERAL GAUSS-WILSON THEOREM (claim to verify):
    Let G be a finite abelian group and S = {x in G : x^2 = 1}.
      (1)  prod_{x in G} x = prod_{x in S} x          [pairing of x with x^{-1}]
      (2)  S is an elementary abelian 2-subgroup, so |S| = 2^r (a power of 2).
      (3)  The product of all elements of G is:
              - 1                      if S = {1}                 (|S| = 1)
              - t  (unique involution) if S = {1, t}              (|S| = 2)
              - 1                      if |S| >= 4 (2-rank >= 2)   two-involution trick
           Equivalently:  prod_{x in G} x = (the unique element of order 2 if one
           exists), otherwise 1.

This file checks the claim EXACTLY (integer/group arithmetic, no floats) over a
large family of finite abelian groups represented as products of cyclic groups
Z/n1 x Z/n2 x ... , covering:
  - all cyclic groups Z/n, n <= 200
  - all products Z/a x Z/b with a,b <= 30
  - selected triple/quad products including the 2-rank >= 2 and 2-rank = 3 cases
  - the classic (ZMod n)^x unit groups (the already-proven specialization) for n <= 200

For each group it independently:
  * computes P  = product of ALL elements,
  * computes S  = involutions+identity {x : 2x = 0},
  * computes PS = product over S,
  * checks P == PS,                                 (lemma 1)
  * checks |S| is a power of 2,                     (lemma 2)
  * predicts P by the trichotomy and checks it.     (main theorem)
"""

from itertools import product
from math import gcd


# ---- finite abelian group as additive Z/n1 x ... x Z/nk -------------------

def elements(mods):
    return list(product(*[range(m) for m in mods]))

def add(a, b, mods):
    return tuple((x + y) % m for x, y, m in zip(a, b, mods))

def double(a, mods):
    return tuple((2 * x) % m for x, m in zip(a, mods))

def group_product(mods):
    """Sum (additive 'product') of all elements of Z/n1 x ... x Z/nk."""
    acc = tuple(0 for _ in mods)
    for e in elements(mods):
        acc = add(acc, e, mods)
    return acc

def involutions(mods):
    """S = {x : 2x = 0}, includes identity."""
    zero = tuple(0 for _ in mods)
    return [e for e in elements(mods) if double(e, mods) == zero]

def product_over(subset, mods):
    acc = tuple(0 for _ in mods)
    for e in subset:
        acc = add(acc, e, mods)
    return acc

def is_power_of_two(n):
    return n >= 1 and (n & (n - 1)) == 0


def predict(mods):
    """Trichotomy prediction of prod of all elements."""
    zero = tuple(0 for _ in mods)
    S = involutions(mods)
    nontrivial = [x for x in S if x != zero]
    if len(nontrivial) == 0:
        return zero                  # |S| = 1
    if len(nontrivial) == 1:
        return nontrivial[0]         # |S| = 2: unique involution
    return zero                      # |S| >= 4: two-involution trick -> identity


def check_group(mods, fails):
    zero = tuple(0 for _ in mods)
    S = involutions(mods)
    P = group_product(mods)
    PS = product_over(S, mods)
    # lemma 1: P == PS
    if P != PS:
        fails.append((mods, "P != prod(S)", P, PS))
    # lemma 2: |S| is a power of two
    if not is_power_of_two(len(S)):
        fails.append((mods, "|S| not power of 2", len(S), None))
    # main theorem: trichotomy prediction
    pred = predict(mods)
    if P != pred:
        fails.append((mods, "trichotomy mismatch", P, pred))


# ---- (ZMod n)^x as a MULTIPLICATIVE group (the proven specialization) -----

def unit_group_product(n):
    """prod over (Z/n)^x, returned as element of Z/n. Also returns S, P_S."""
    units = [a for a in range(1, n) if gcd(a, n) == 1]
    P = 1
    for a in units:
        P = (P * a) % n
    S = [a for a in units if (a * a) % n == 1]
    PS = 1
    for a in S:
        PS = (PS * a) % n
    return P, S, PS

def check_unit_group(n, fails):
    if n < 2:
        return
    P, S, PS = unit_group_product(n)
    if P != PS % n:
        fails.append((("U", n), "P != prod(S)", P, PS % n))
    if not is_power_of_two(len(S)):
        fails.append((("U", n), "|S| not power of 2", len(S), None))
    nontrivial = [a for a in S if a != 1]
    if len(nontrivial) == 0:
        pred = 1
    elif len(nontrivial) == 1:
        pred = nontrivial[0]
    else:
        pred = 1
    if P != pred:
        fails.append((("U", n), "trichotomy mismatch", P, pred))


def main():
    fails = []
    tested = 0

    # cyclic Z/n, n <= 200
    for n in range(1, 201):
        check_group((n,), fails)
        tested += 1

    # products Z/a x Z/b, a,b <= 30
    for a in range(1, 31):
        for b in range(1, 31):
            check_group((a, b), fails)
            tested += 1

    # selected triples / quads, emphasizing 2-rank structure
    triples = [
        (2, 2, 2), (2, 2, 4), (2, 4, 8), (4, 4, 4), (2, 2, 3),
        (2, 6, 6), (3, 3, 3), (6, 10, 15), (2, 2, 2, 2), (2, 4, 6, 8),
        (12, 18, 30), (2, 2, 2, 3, 5),
    ]
    for t in triples:
        check_group(t, fails)
        tested += 1

    # unit groups (Z/n)^x, n <= 200  (the already-proven case)
    for n in range(2, 201):
        check_unit_group(n, fails)
        tested += 1

    print(f"Groups tested: {tested}")
    if fails:
        print(f"FAILURES: {len(fails)}")
        for f in fails[:40]:
            print("  ", f)
        raise SystemExit(1)
    print("ALL CHECKS PASSED")
    print("  - prod(G) == prod{x : x^2=1}            (pairing lemma)")
    print("  - |{x : x^2=1}| is always a power of 2  (elementary abelian 2-group)")
    print("  - trichotomy: prod(G) = unique involution if one exists, else 1")


if __name__ == "__main__":
    main()
