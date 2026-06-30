#!/usr/bin/env python3
"""Durable verification for wilsons-theorem-oq-02-ext-oq-01.

Miller's theorem (1903): In a finite abelian group G, the product of ALL
elements (in any order; abelian so order-independent) equals the identity,
UNLESS G has a unique element of order 2, in which case the product equals
that unique involution.

The gallery's WilsonsTheoremOQ02Ext.lean proves the (ZMod n)^x specialization
via the "two-involution trick": if the 2-torsion subgroup
    S = {x in G : x^2 = 1}
has |S| >= 3, then prod_{x in S} x = 1, hence prod_{x in G} x = 1.

OQ-01 asks: does the trick generalize to arbitrary finite abelian groups?
This script confirms, by exact group arithmetic, that:

  (A) prod_{x in G} x = prod_{x in S} x                     (pairing off g != g^-1)
  (B) |S| >= 3  =>  prod_{x in S} x = 1   (the two-involution trick)
  (C) |S| == 1  =>  prod = 1
  (D) |S| == 2  =>  prod = the unique involution t
  (E) full Miller classification holds

Groups are realized as G = Z/m_1 x Z/m_2 x ... x Z/m_k (every finite abelian
group is such a product), tuples added componentwise mod m_i.  No floats:
all arithmetic is exact integer modular arithmetic.
"""

from itertools import product


def group_elements(mods):
    """All elements of Z/m_1 x ... x Z/m_k as tuples."""
    return list(product(*[range(m) for m in mods]))


def add(a, b, mods):
    return tuple((x + y) % m for x, y, m in zip(a, b, mods))


def total_product(mods):
    """Sum (group op is +) of ALL elements of the product group."""
    acc = tuple(0 for _ in mods)
    for g in group_elements(mods):
        acc = add(acc, g, mods)
    return acc


def two_torsion(mods):
    """S = {x : 2x = 0}, i.e. x_i in {0, m_i/2} when m_i even, else x_i = 0."""
    zero = tuple(0 for _ in mods)
    S = [g for g in group_elements(mods)
         if add(g, g, mods) == zero]
    return S


def prod_over(elems, mods):
    acc = tuple(0 for _ in mods)
    for g in elems:
        acc = add(acc, g, mods)
    return acc


def check(mods):
    zero = tuple(0 for _ in mods)
    S = two_torsion(mods)
    involutions = [t for t in S if t != zero]   # order exactly 2

    P_all = total_product(mods)
    P_S = prod_over(S, mods)

    # (A) product over G equals product over 2-torsion
    assert P_all == P_S, f"(A) failed for {mods}: {P_all} != {P_S}"

    # (B)/(C)/(D): classification of P_S by |S|
    if len(S) >= 3:
        assert P_S == zero, f"(B) failed for {mods}: |S|={len(S)} but P_S={P_S}"
        regime = "B: |S|>=3 -> 1"
    elif len(S) == 1:
        assert P_S == zero, f"(C) failed for {mods}"
        regime = "C: |S|=1 -> 1"
    elif len(S) == 2:
        t = involutions[0]
        assert P_S == t, f"(D) failed for {mods}: P_S={P_S}, t={t}"
        regime = "D: |S|=2 -> unique involution"
    else:
        raise AssertionError("S must contain identity, |S|>=1")

    # (E) full Miller statement
    if len(involutions) == 1:
        assert P_all == involutions[0]
        miller = "unique involution -> prod = t"
    else:
        assert P_all == zero
        miller = "no/multiple involutions -> prod = 1"

    return len(S), len(involutions), P_all, regime, miller


def main():
    # A broad sweep of finite abelian group structures.
    test_mods = [
        # cyclic
        (2,), (3,), (4,), (5,), (6,), (7,), (8,), (9,), (10,), (12,),
        (16,), (15,), (24,),
        # rank 2
        (2, 2), (2, 3), (3, 3), (2, 4), (4, 4), (2, 6), (6, 6), (2, 8),
        (3, 5), (4, 6), (2, 2),
        # rank 3+
        (2, 2, 2), (2, 2, 3), (2, 2, 4), (2, 3, 5), (2, 2, 2, 2),
        (3, 3, 3), (2, 4, 6),
        # the gallery's caution case: Z/3 x Z/3 has |S|=1
        (3, 3),
        # elementary abelian 2-groups (rank r => |S| = 2^r)
        (2,), (2, 2), (2, 2, 2), (2, 2, 2, 2),
        # mixed with odd parts
        (10, 15), (12, 8),
    ]

    n_pass = 0
    print(f"{'group':<18}{'|S|':>4}{'#inv':>6}  {'prod':<14}{'regime':<28}{'Miller'}")
    print("-" * 100)
    for mods in test_mods:
        sS, ninv, P, regime, miller = check(mods)
        gname = "Z" + "xZ".join("" for _ in mods)  # placeholder
        gname = " x ".join(f"Z/{m}" for m in mods)
        print(f"{gname:<18}{sS:>4}{ninv:>6}  {str(P):<14}{regime:<28}{miller}")
        n_pass += 1

    # Exhaustive small sweep: all products of moduli in 2..6, up to rank 3.
    extra = 0
    from itertools import product as iproduct
    for r in (1, 2, 3):
        for mods in iproduct(range(2, 7), repeat=r):
            check(mods)
            extra += 1

    print("-" * 100)
    print(f"PASS: {n_pass} tabulated groups + {extra} exhaustive (rank<=3, moduli 2..6)")
    print("All checks (A)-(E) hold. Miller's theorem / two-involution trick confirmed.")


if __name__ == "__main__":
    main()
