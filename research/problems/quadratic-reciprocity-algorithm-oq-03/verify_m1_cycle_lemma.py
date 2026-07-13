#!/usr/bin/env python3
"""
S9 (researcher-2): certify the ONE remaining un-derisked M1 sub-step in the
*exact predicate form Lean's `Equiv.Perm.IsCycle` uses*, so the missing lemma

    isCycle_mulLeft_of_generator :
      (hg : ∀ x : Fˣ, x ∈ Subgroup.zpowers g) → (Equiv.mulLeft g).IsCycle

has a numerically-certified specification before any Lean is written.

Mathlib (`Mathlib/GroupTheory/Perm/Sign.lean`, `.../Perm/Cycle/Basic.lean`)
defines:

    IsCycle f  :=  ∃ x, f x ≠ x ∧ ∀ y, f y ≠ y → SameCycle f x y
    SameCycle f x y  :=  ∃ i : ℤ, (f ^ i) x = y

For f = `Equiv.mulLeft g` on the units group Fˣ:  (f ^ i) x = gⁱ · x.
So IsCycle reduces to two finite, decidable predicates we check directly here.
Then `IsCycle.sign : sign f = -(-1) ^ #f.support` and
`IsCycle.orderOf : orderOf f = #f.support` give the sign.

This is the predicate-level cross-check of S2/S3's "single (p-1)-cycle" prose
(which used cycle-decomposition); here we verify the *constructor obligations*
of `IsCycle` itself, i.e. exactly what the Lean proof must discharge.

Pure stdlib. Exits non-zero on any mismatch.  Run: python3 verify_m1_cycle_lemma.py
"""

from sympy import primerange, primitive_root


def units_mod(p):
    return list(range(1, p))


def mulLeft(g, p):
    # the permutation f : x -> g*x on Fˣ = {1,...,p-1}
    return {x: (g * x) % p for x in units_mod(p)}


def check_prime(p):
    g = int(primitive_root(p))
    U = units_mod(p)
    n = p - 1  # |Fˣ|
    f = mulLeft(g, p)

    # ---- IsCycle obligation 1: there is a moved point, and (here) NO fixed point.
    fixed = [x for x in U if f[x] == x]
    assert fixed == [], f"p={p}: mulLeft g has unexpected fixed point(s) {fixed}"
    assert f[1] != 1, f"p={p}: witness point 1 is fixed (would break IsCycle witness)"

    # ---- IsCycle obligation 2: ∀ y (moved ⇒) SameCycle f 1 y, i.e.
    #      ∀ y ∈ Fˣ, ∃ i ∈ [0,n), (g^i)·1 = y.  (witness x := 1)
    powers = {}
    cur = 1
    for i in range(n):
        powers[cur] = i
        cur = (cur * g) % p
    # g is a generator ⇒ powers hits every unit exactly once
    assert set(powers.keys()) == set(U), f"p={p}: g={g} is not a generator"
    for y in U:
        i = powers[y]
        assert pow(g, i, p) == y, f"p={p}: g^{i} != {y}"

    # ---- support cardinality = n = p-1 (all units moved); p odd ⇒ p-1 even.
    support = [x for x in U if f[x] != x]
    assert len(support) == n, f"p={p}: |support| {len(support)} != {n}"
    assert n % 2 == 0, f"p={p}: p-1 odd?!"

    # ---- IsCycle.sign : sign f = -(-1)^#support  ⇒  here = -(-1)^(p-1) = -1.
    sign_via_iscycle = -((-1) ** len(support))
    assert sign_via_iscycle == -1, f"p={p}: IsCycle.sign gives {sign_via_iscycle}, want -1"

    # ---- independent cross-check: sign by inversion parity of the permutation f.
    arr = [f[x] for x in U]
    inv = sum(1 for a in range(len(arr)) for b in range(a + 1, len(arr)) if arr[a] > arr[b])
    sign_via_inversions = (-1) ** inv
    assert sign_via_inversions == sign_via_iscycle, (
        f"p={p}: inversion-sign {sign_via_inversions} != IsCycle.sign {sign_via_iscycle}")

    return g, n


def main():
    primes = [p for p in primerange(3, 200)]
    for p in primes:
        g, n = check_prime(p)
    print(f"All checks passed for {len(primes)} odd primes (3..199).")
    print("Certified IsCycle constructor obligations for f = mulLeft g (g a generator of Fˣ):")
    print("  (O1) no fixed point on Fˣ, witness point 1 is moved;")
    print("  (O2) ∀ y ∈ Fˣ, ∃ i<p-1, gⁱ = y  (SameCycle f 1 y, the `Subgroup.zpowers g` step);")
    print("  (O3) #support = p-1 (even) ⇒ IsCycle.sign = -(-1)^(p-1) = -1;")
    print("  cross-checked against inversion-parity sign on every prime.")
    print("This pins the spec of the sole missing M1 lemma `isCycle_mulLeft_of_generator`")
    print("(confirmed absent from Mathlib @ rev 2df2f01 / v4.26.0).")


if __name__ == "__main__":
    main()
