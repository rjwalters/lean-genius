#!/usr/bin/env python3
"""Reproducible verification of Step 4 (`normalizer_iso_AGL1Z`) for
abel-ruffini-galois-extensions-oq-06-galois-direction.

Background. The file proves a primitive solvable `H <= S_p` (p prime) embeds
into `AGL(1,p)`. Step 4 (`normalizer_iso_AGL1Z`) is the structural core:

    N_{S_p}(<sigma>)  ~=  AGL1Z p          (sigma any p-cycle in S_p)

stated as a group hom `phi : N_{S_p}(<sigma>) ->* AGL1Z p` that is BOTH
injective AND surjective. The parent file's `AGL1Z.toPerm` realises AGL(1,p)
concretely as the affine permutations `x |-> a + u*x` (a in ZMod p,
u in (ZMod p)^x).

WHY A SEPARATE SCRIPT FROM verify_step5_normalizer.py. The S7 Step-5 script
certifies only the EASY inclusion `AGL image  SUBSET  N(<sigma>)` (every
affine map normalises the translation subgroup). That does NOT certify Step 4:
Step 4's `phi` must be SURJECTIVE, i.e. the normalizer contains NOTHING BEYOND
the affine maps -- equivalently `|N_{S_p}(<sigma>)| = p*(p-1)` exactly. The
surjective half is the genuinely harder, previously-uncertified direction
(injectivity is immediate -- the affine maps are distinct permutations).

This script brute-forces the FULL symmetric group S_p and computes the exact
normalizer, certifying for sigma = (x |-> x+1) (a genuine p-cycle):

  (A) N_{S_p}(<sigma>) equals EXACTLY the affine-group image
      { x|->a+u*x : a in ZMod p, u in (ZMod p)^x }  (set equality, both
      directions) -- so phi is a bijection onto AGL(1,p): injective AND
      SURJECTIVE. This is the Step 4 isomorphism claim, the surjective half
      being the new content here.

  (B) |N_{S_p}(<sigma>)| = p*(p-1) = |AGL1Z p| (parent `AGL1Z.card_eq`), and
      the Sylow-p count n_p = |S_p| / |N| = (p-2)! satisfies n_p = 1 mod p
      (Sylow III sanity check on the classical order arithmetic Step 4 rests on).

  (C) The recovered conjugation map h |-> (a,u) is a GROUP ISOMORPHISM:
      multiplicative on the normalizer (phi(h1 . h2) = phi(h1) . phi(h2) under
      the AGL1Z product (a,u)(b,v) = (a + u*b, u*v)), confirming phi is a
      homomorphism, not merely a set bijection.

Brute force is over all p! permutations, so p in {3,5,7} (7! = 5040). This is
a finite-model certification that Step 4's `phi` is a genuine group iso before
a Docker-up ACT spends ~80-150 LOC discharging it. An assert failure means a
finding changed.

Run: python3 verify_step4_normalizer.py   (needs only sympy)
"""

from itertools import permutations
from math import factorial


def perm_from_affine(a, u, p):
    """Affine permutation x |-> a + u*x on ZMod p, as a tuple of images."""
    return tuple((a + u * x) % p for x in range(p))


def compose(f, g):
    """(f o g)(x) = f(g(x)); permutations as image tuples."""
    return tuple(f[g[x]] for x in range(len(g)))


def inverse(f):
    inv = [0] * len(f)
    for x, fx in enumerate(f):
        inv[fx] = x
    return tuple(inv)


def units(p):
    # p prime => every nonzero residue is a unit
    return [u for u in range(1, p)]


def cyclic_group(sigma, p):
    """<sigma> = { sigma^0, ..., sigma^{p-1} } as a set of image tuples."""
    elts = set()
    cur = tuple(range(p))  # identity
    for _ in range(p):
        elts.add(cur)
        cur = compose(sigma, cur)
    return elts


def affine_image(p):
    """{ x|->a+u*x } as a set of permutation tuples = AGL(1,p) image."""
    return {perm_from_affine(a, u, p) for u in units(p) for a in range(p)}


def normalizer_in_Sp(subgroup_set, p):
    """{ g in S_p : g . K . g^{-1} = K } by brute force over all of S_p."""
    K = subgroup_set
    N = set()
    for tup in permutations(range(p)):
        g = tuple(tup)
        ginv = inverse(g)
        # g K g^{-1} == K  iff  for every k in K, g k g^{-1} in K
        # (|conjugate set| = |K| automatically, so subset => equal)
        if all(compose(compose(g, k), ginv) in K for k in K):
            N.add(g)
    return N


def recover_affine_params(h, p):
    """Given an affine perm h (x|->a+u*x), recover (a,u): a=h(0), u=h(1)-h(0)."""
    a = h[0]
    u = (h[1] - h[0]) % p
    return (a, u)


def agl_mul(g1, g2, p):
    """AGL1Z product: (a,u)(b,v) = (a + u*b, u*v) (parent `AGL1Z.mul_trans/scale`)."""
    a, u = g1
    b, v = g2
    return ((a + u * b) % p, (u * v) % p)


def verify_prime(p):
    sigma = perm_from_affine(1, 1, p)  # x |-> x + 1, a genuine p-cycle

    # sigma is a p-cycle: order p, support = everything
    assert cyclic_group(sigma, p).__len__() == p, f"<sigma> order != p for p={p}"

    K = cyclic_group(sigma, p)
    N = normalizer_in_Sp(K, p)
    A = affine_image(p)

    # (A) set equality: N == affine image  (injective AND surjective phi)
    assert N == A, (
        f"p={p}: normalizer != affine image "
        f"(|N|={len(N)}, |A|={len(A)}, extra={len(N - A)}, missing={len(A - N)})"
    )

    # (B) order arithmetic
    assert len(N) == p * (p - 1), f"p={p}: |N|={len(N)} != p(p-1)={p*(p-1)}"
    n_p = factorial(p) // len(N)
    assert n_p == factorial(p - 2), f"p={p}: n_p={n_p} != (p-2)!={factorial(p-2)}"
    assert n_p % p == 1, f"p={p}: Sylow III violated, n_p={n_p} not = 1 mod p"

    # (C) the recovered map h |-> (a,u) is a group homomorphism on N
    sample = sorted(N)
    for h1 in sample:
        for h2 in sample:
            lhs = recover_affine_params(compose(h1, h2), p)
            rhs = agl_mul(recover_affine_params(h1, p),
                          recover_affine_params(h2, p), p)
            assert lhs == rhs, f"p={p}: phi not multiplicative on {h1},{h2}"

    print(f"  p={p:2d}: |N_S_p(<sigma>)| = {len(N):4d} = p(p-1), "
          f"n_p = {n_p} = (p-2)! = 1 mod p, N == AGL image, phi a group iso  OK")


def main():
    print("Step 4 (normalizer_iso_AGL1Z) finite-model certification")
    print("Certifying N_{S_p}(<sigma>) == AGL(1,p) image (injective+SURJECTIVE)")
    print("and that the conjugation map is a group isomorphism:")
    for p in (3, 5, 7):
        verify_prime(p)
    print("All Step 4 assertions passed.")


if __name__ == "__main__":
    main()
