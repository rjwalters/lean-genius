#!/usr/bin/env python3
"""
Brute-force confirmation of the hyperoctahedral orbit-size formula (★) used by
FourSquareDistributionOQ04Decomp.lean / ...Sign.lean.

For every m-tuple of integers with sum of squares = n, group by `shape` (the
sorted multiset of absolute values) and check that each fiber has size

    shapeContribution(m, shape) = (m! / prod_v count_v!) * 2^{#nonzero}.

Also separately confirms the sign-count half (signFiber_card):
    for fixed abs-profile g, #{f : |f i| = g i} = 2^{#{i : g i != 0}}.
"""
from itertools import product, permutations
from collections import Counter
from math import factorial, prod


def fiber_sizes(m, n):
    box = range(-n, n + 1)
    fibers = Counter()
    for f in product(box, repeat=m):
        if sum(x * x for x in f) == n:
            fibers[tuple(sorted(abs(x) for x in f))] += 1
    return fibers


def shape_contribution(m, shape):
    c = Counter(shape)
    arrangements = factorial(m) // prod(factorial(k) for k in c.values())
    nonzero = sum(1 for v in shape if v != 0)
    return arrangements * 2 ** nonzero


def check_orbit():
    mismatch = checked = 0
    for m in range(2, 6):
        for n in range(0, 13):
            for shape, sz in fiber_sizes(m, n).items():
                checked += 1
                if shape_contribution(m, shape) != sz:
                    mismatch += 1
                    print(f"  MISMATCH m={m} n={n} shape={shape} "
                          f"actual={sz} formula={shape_contribution(m, shape)}")
    print(f"(orbit) checked {checked} fibers (m<=5, n<=12), mismatches={mismatch}")
    return mismatch == 0


def multinomial(toFinset, count):
    """Nat.multinomial: (sum count)! / prod count!  over the distinct values."""
    total = sum(count[v] for v in toFinset)
    return factorial(total) // prod(factorial(count[v]) for v in toFinset)


def check_arrangement():
    """Validate the isolated residue `arrangement_card` of
    FourSquareDistributionOQ04Arrange.lean:

        #{ g : Fin m -> Z | multiset(g) = s } == Nat.multinomial s.toFinset s.count
                                              == m! / prod_v (count_v)!.

    For every multiset s drawn (with repetition) from {0,1,2} of size m <= 6, count
    the genuine arrangements (functions whose multiset image is s) by brute force and
    compare to BOTH the multinomial coefficient and the m!/prod count! divisor form.
    Also confirms prod count! | m! (the Nat.div in shapeContribution is exact).
    """
    mismatch = checked = 0
    values = (0, 1, 2)
    for m in range(0, 7):
        seen = set()
        for combo in product(values, repeat=m):
            s = tuple(sorted(combo))            # the multiset, as a sorted tuple
            if s in seen:
                continue
            seen.add(s)
            cnt = Counter(s)
            toFinset = set(cnt)                 # s.toFinset
            # genuine arrangement count: distinct orderings of the multiset s
            actual = len(set(permutations(s)))
            mult = multinomial(toFinset, cnt)
            div_form = factorial(m) // prod(factorial(k) for k in cnt.values())
            checked += 1
            # divisibility: Nat.div is exact
            exact = factorial(m) % prod(factorial(k) for k in cnt.values()) == 0
            if not (actual == mult == div_form and exact):
                mismatch += 1
                print(f"  ARRANGE MISMATCH m={m} s={s} actual={actual} "
                      f"multinomial={mult} divform={div_form} exact={exact}")
    print(f"(arrange) checked {checked} multisets (values in {{0,1,2}}, m<=6), "
          f"mismatches={mismatch}")
    return mismatch == 0


def check_sign():
    mismatch = checked = 0
    for m in range(1, 6):
        for g in product(range(-2, 3), repeat=m):
            fiber = [f for f in product(range(-2, 3), repeat=m)
                     if all(abs(f[i]) == abs(g[i]) for i in range(m))]
            expected = 2 ** sum(1 for x in g if x != 0)
            checked += 1
            if len(fiber) != expected:
                mismatch += 1
                print(f"  SIGN MISMATCH m={m} g={g} actual={len(fiber)} formula={expected}")
    print(f"(sign) checked {checked} abs-profiles (m<=5), mismatches={mismatch}")
    return mismatch == 0


if __name__ == "__main__":
    ok = check_orbit() and check_sign() and check_arrangement()
    print("RESULT:", "PASS" if ok else "FAIL")
    raise SystemExit(0 if ok else 1)
