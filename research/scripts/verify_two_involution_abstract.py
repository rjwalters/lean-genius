#!/usr/bin/env python3
"""Durable verifier for OQ-01 (wilsons-theorem-oq-02-ext-oq-01).

Theorem (abstract two-involution trick): for any FINITE ABELIAN group G,
    |{x in G : x^2 = e}| >= 3  =>  prod_{x in G} x = e.

We model finite abelian groups as direct products of cyclic groups
Z/n1 x Z/n2 x ... (every finite abelian group is such a product, so this
sweep is exhaustive up to isomorphism for the chosen shapes). For each group
we compute, with EXACT integer arithmetic:
  - S = {x : 2x = 0}            (2-torsion / square roots of identity)
  - P = sum of ALL elements     (group operation written additively)
and check the equivalences the theorem and its companion cases predict:
  - |S| >= 3  =>  P = 0
  - |S| == 1  =>  P = 0            (only identity is an involution)
  - |S| == 2  =>  P = the unique non-identity involution

|S| is always a power of two (S is an elementary abelian 2-group), so the
case |S| in {1,2} vs |S|>=3 is the full trichotomy and >=3 means >=4.
"""

from itertools import product


def elements(shape):
    return product(*[range(n) for n in shape])


def add(a, b, shape):
    return tuple((x + y) % n for x, y, n in zip(a, b, shape))


def two_torsion(shape):
    zero = tuple(0 for _ in shape)
    return [g for g in elements(shape) if add(g, g, shape) == zero]


def prod_all(shape):
    zero = tuple(0 for _ in shape)
    acc = zero
    for g in elements(shape):
        acc = add(acc, g, shape)
    return acc


def check(shape):
    zero = tuple(0 for _ in shape)
    S = two_torsion(shape)
    P = prod_all(shape)
    s = len(S)
    if s >= 3:
        ok = (P == zero)
        rule = "|S|>=3 => P=e"
    elif s == 1:
        ok = (P == zero)
        rule = "|S|=1 => P=e"
    else:  # s == 2
        nontrivial = [x for x in S if x != zero]
        ok = (P == nontrivial[0])
        rule = "|S|=2 => P=involution"
    # |S| is always a power of two
    pow2 = (s & (s - 1)) == 0
    return ok and pow2, s, P, rule


def main():
    shapes = [
        # cyclic
        (2,), (3,), (4,), (5,), (6,), (7,), (8,), (9,), (12,), (15,), (16,),
        # rank-2 (the smallest non-cyclic / multiple-involution groups)
        (2, 2), (2, 4), (4, 4), (2, 6), (3, 3), (2, 8), (6, 6), (2, 2, 2),
        (2, 2, 3), (4, 2), (2, 2, 2, 2), (3, 5), (2, 3, 5), (2, 2, 4),
    ]
    fails = 0
    ge3 = 0
    for shape in shapes:
        ok, s, P, rule = check(shape)
        order = 1
        for n in shape:
            order *= n
        tag = "OK " if ok else "FAIL"
        if s >= 3:
            ge3 += 1
        print(f"{tag}  G=Z{list(shape)} |G|={order:<4} |S|={s:<3} P={P}  [{rule}]")
        if not ok:
            fails += 1
    print()
    print(f"groups tested: {len(shapes)},  with |S|>=3: {ge3},  failures: {fails}")
    if fails == 0:
        print("PASS: theorem statement verified on all sampled finite abelian groups.")
    else:
        print("VERIFICATION FAILED")
        raise SystemExit(1)


if __name__ == "__main__":
    main()
