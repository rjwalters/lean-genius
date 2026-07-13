#!/usr/bin/env python3
"""Reproducible verification of Step 5 (`H_le_normalizer`) for
abel-ruffini-galois-extensions-oq-06-galois-direction.

Background. The file proves: a primitive solvable `H <= S_p` (p prime) is
conjugate into AGL(1,p). The concrete witness group is
`H = (AGL1Z.toPerm p).range`, where `AGL1Z.toPerm` sends `(a,u)` (a in ZMod p,
u in (ZMod p)^x) to the affine permutation `x |-> a + u*x` (parent file
AbelRuffiniGaloisExtensionsOQ06.lean). Its normal Sylow-p is the translation
subgroup `P = <sigma>`, `sigma = (x |-> x+1)`.

S5 (researcher-5, 2026-06-13) found the *original* Step 5 statement UNSOUND:
`(hsigma : sigma in H) => H <= N_{S_p}(<sigma>)` is FALSE for an arbitrary
`sigma in H`. S5 gave the corrected signature: `sigma` must generate the
*normal* Sylow-p `P` (Steps 2+3), not be an arbitrary element of `H`.

This script certifies, by direct permutation computation on `ZMod p`, that:

  (A) CORRECTED Step 5 is TRUE: with `sigma = (x|->x+1)` generating the
      translation subgroup `P`, every `h in H` normalizes `<sigma>`
      (i.e. `H <= N(<sigma>)`). Closed form: conjugating `tau_c : x|->x+c`
      by `h : x|->a+u*x` yields `tau_{u*c}`, which lies in `<sigma>`.

  (B) The ORIGINAL Step 5 is FALSE (regression guard reproducing S5's
      counterexample): with `sigma' = (x|->2x) in H` (not a translation),
      some `h in H` has `h sigma' h^{-1} not in <sigma'>`, so
      `H </= N(<sigma'>)`.

Run: python3 verify_step5_normalizer.py   (needs only sympy)
All assertions must pass (an assert failure means a finding changed).
"""

from sympy import primerange


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
    return [u for u in range(1, p) if u != 0]  # p prime => all nonzero are units


def affine_group(p):
    """H = AGL(1,p) = { x|->a+u*x : a in ZMod p, u in (ZMod p)^x }."""
    return [perm_from_affine(a, u, p) for u in units(p) for a in range(p)]


def cyclic_subgroup(sigma, p):
    """<sigma> = { sigma^k }."""
    elts = set()
    cur = tuple(range(p))  # identity
    while cur not in elts:
        elts.add(cur)
        cur = compose(sigma, cur)
    return elts


def normalizes(h, subgroup):
    """Does h normalize the subgroup? i.e. h s h^{-1} in subgroup for all s."""
    hinv = inverse(h)
    return all(compose(compose(h, s), hinv) in subgroup for s in subgroup)


def check_prime(p, verbose=False):
    H = affine_group(p)
    assert len(H) == p * (p - 1), f"p={p}: |H| should be p(p-1)={p*(p-1)}, got {len(H)}"

    identity = tuple(range(p))

    # ---- (A) CORRECTED Step 5: sigma generates the normal Sylow-p (translations).
    sigma = perm_from_affine(1, 1, p)          # x |-> x + 1
    P = cyclic_subgroup(sigma, p)              # translation subgroup
    assert len(P) == p, f"p={p}: <sigma> should be the order-p translation group, got {len(P)}"
    # It really is the full set of translations:
    translations = {perm_from_affine(c, 1, p) for c in range(p)}
    assert P == translations, f"p={p}: <sigma> != translation subgroup"
    # P is normal in H (Step 2): every h in H normalizes P.
    assert all(normalizes(h, P) for h in H), f"p={p}: translation subgroup not normal in H"
    # Hence H <= N(<sigma>)  -- the corrected Step 5 conclusion.
    assert all(normalizes(h, P) for h in H)

    # Closed-form cross-check: conj of tau_c by (a,u) is tau_{u*c}.
    for u in units(p):
        for a in range(p):
            h = perm_from_affine(a, u, p)
            hinv = inverse(h)
            for c in range(p):
                tau_c = perm_from_affine(c, 1, p)
                conj = compose(compose(h, tau_c), hinv)
                assert conj == perm_from_affine((u * c) % p, 1, p), (
                    f"p={p}: conj(tau_{c}) by (a={a},u={u}) != tau_{u*c%p}")

    # ---- (B) ORIGINAL Step 5 is FALSE: arbitrary sigma' in H need not work.
    # Use S5's counterexample family: sigma' = (x |-> g*x) for a generator g
    # (a non-translation fixing 0). Find an h in H breaking normalization.
    g = next(u for u in units(p) if len(cyclic_subgroup(perm_from_affine(0, u, p), p)) == (p - 1))
    sigma2 = perm_from_affine(0, g, p)         # x |-> g*x, fixes 0, in H
    assert sigma2 in H
    P2 = cyclic_subgroup(sigma2, p)
    # every element of <sigma'> fixes 0 (they are all x|->g^k x):
    assert all(s[0] == 0 for s in P2), f"p={p}: <sigma'> should fix 0"
    # translation by 1 conjugates sigma' off the stabilizer of 0:
    h = perm_from_affine(1, 1, p)              # x |-> x + 1, in H
    bad = compose(compose(h, sigma2), inverse(h))
    assert bad not in P2, f"p={p}: expected counterexample, but h sigma' h^-1 in <sigma'>"
    assert not normalizes(h, P2), f"p={p}: expected H not<= N(<sigma'>)"

    if verbose:
        print(f"  p={p:3d}: |H|={len(H)}=p(p-1); <x+1> normal Sylow-p (order {len(P)}); "
              f"H<=N(<x+1>) OK; counterexample <{g}x> breaks original Step 5 OK")


def main():
    primes = list(primerange(3, 30))  # odd primes; |H|=p(p-1) so cost ~ p^3 per check
    print("Verifying Step 5 (H <= N(<sigma>)) for H = AGL(1,p) on ZMod p")
    for p in primes:
        check_prime(p, verbose=True)
    print(f"\nAll checks passed for {len(primes)} odd primes (3..{primes[-1]}).")
    print("(A) corrected Step 5 (sigma generates the NORMAL Sylow-p): H <= N(<sigma>) holds.")
    print("(B) original Step 5 (arbitrary sigma in H): FALSE -- S5 counterexample reproduced.")


if __name__ == "__main__":
    main()
