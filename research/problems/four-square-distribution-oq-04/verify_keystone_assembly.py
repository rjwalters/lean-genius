#!/usr/bin/env python3
"""
Certificate for FourSquareDistributionOQ04Keystone.lean.

The Lean file proves, UNCONDITIONALLY (no sorry, no axiom), the two
bookkeeping steps of the Sign-file blueprint:

  Step 1 (absFiber_eq_signFiber):
      { f : reps(m,n) | shape f = s, |f| = g } = signFiber(g)
      i.e. the fiber of the absolute-value map over an attained profile g
      is exactly the set of sign-flips of g.

  Step 3 (shapeFiber_card_eq_arrangements_mul):
      |{ f : reps(m,n) | shape f = s }|
          = (# distinct abs-profiles g of shape s realized in reps(m,n))
            * 2 ^ (#nonzero parts of s)

This script checks BOTH against brute enumeration of the genuine
representation set reps(m,n) = { f in Z^m : sum f_i^2 = n }, for all
m <= 5 and n <= 12.  The only remaining (conditional) input to the Lean
keystone is then

      #abs-profiles of shape s = m! / prod_v (count_v)!     (arrangement_card)

which is certified separately by verify_orbit_formula.py (check_arrangement).

This file does NOT re-prove that residue; it isolates exactly the part the
new Lean file discharges, so a reader can see the unconditional content is
sound independent of arrangement_card.

Run:  python3 verify_keystone_assembly.py
Exit 0 on success; raises AssertionError on any mismatch.
"""

from itertools import product
from collections import Counter
from math import factorial, prod


def reps(m, n):
    """All integer m-tuples with sum of squares = n (box [-n,n]^m is lossless)."""
    rng = range(-n, n + 1)
    out = []
    for f in product(rng, repeat=m):
        if sum(x * x for x in f) == n:
            out.append(f)
    return out


def shape(f):
    """Multiset of absolute values, as a sorted tuple."""
    return tuple(sorted(abs(x) for x in f))


def abs_profile(f):
    """The coordinatewise |f| (an arrangement of shape f)."""
    return tuple(abs(x) for x in f)


def nonzero_count(s):
    return sum(1 for v in s if v != 0)


def arrangement_count_formula(s):
    """m! / prod_v (count_v)! for the multiset s (a tuple)."""
    m = len(s)
    counts = Counter(s)
    return factorial(m) // prod(factorial(c) for c in counts.values())


def check(m_max=5, n_max=12):
    checked_fibers = 0
    checked_step1 = 0
    for m in range(1, m_max + 1):
        for n in range(0, n_max + 1):
            R = reps(m, n)
            # group representations by shape
            by_shape = {}
            for f in R:
                by_shape.setdefault(shape(f), []).append(f)
            for s, fiber in by_shape.items():
                # --- Step 1: each abs-profile fiber is the set of sign-flips ---
                profiles = {}
                for f in fiber:
                    profiles.setdefault(abs_profile(f), []).append(f)
                for g, signfiber in profiles.items():
                    # signFiber(g): all tuples agreeing with g up to sign,
                    # which (since these are representations) is exactly the
                    # product over coordinates of {g_i, -g_i}.
                    choices = [(-c, c) if c != 0 else (0,) for c in g]
                    brute_signfiber = set(product(*[set(ch) for ch in choices]))
                    assert set(signfiber) == brute_signfiber, (
                        f"Step1 fail m={m} n={n} g={g}: "
                        f"{set(signfiber)} != {brute_signfiber}"
                    )
                    # each sign fiber has size 2^(#nonzero of g)
                    assert len(signfiber) == 2 ** nonzero_count(g)
                    checked_step1 += 1

                # --- Step 3: fiber = (#profiles) * 2^(#nonzero s) ---
                nz = nonzero_count(s)
                assert len(fiber) == len(profiles) * (2 ** nz), (
                    f"Step3 fail m={m} n={n} s={s}: "
                    f"{len(fiber)} != {len(profiles)} * 2^{nz}"
                )
                # cross-check the (conditional) residue too, for confidence
                assert len(profiles) == arrangement_count_formula(s), (
                    f"arrangement residue fail m={m} n={n} s={s}: "
                    f"{len(profiles)} != {arrangement_count_formula(s)}"
                )
                # and the full (★): fiber = m!/prod count! * 2^nonzero
                assert len(fiber) == arrangement_count_formula(s) * (2 ** nz)
                checked_fibers += 1
    return checked_fibers, checked_step1


if __name__ == "__main__":
    nf, ns = check()
    print(f"PASS: {nf} shape-fibers and {ns} sign-fibers verified "
          f"(m<=5, n<=12).")
    print("  Step 1 (absFiber_eq_signFiber): OK")
    print("  Step 3 (shapeFiber = #profiles * 2^nonzero): OK")
    print("  arrangement residue and full (star): OK (cross-check)")
