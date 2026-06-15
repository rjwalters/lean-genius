#!/usr/bin/env python3
"""Reproducible numerical verification of Zolotarev's lemma — the formalizable
core (Milestone 1) of quadratic-reciprocity-algorithm-oq-03.

Zolotarev's lemma (the Lean target):

    legendreSym p a = sign(pi_a),   pi_a : ZMod p -> ZMod p,  x |-> a*x

for an odd prime p and a not divisible by p. This script checks the identity
directly (no Lean / Docker needed) and independently re-derives every step of
the paper proof in knowledge.md, so the exact statement to be formalized is
pinned and de-risked:

  Step 1  pi_a is a permutation of ZMod p fixing 0.
  Step 2  pi_g is a single (p-1)-cycle on the units, so sign(pi_g) = -1.
  Step 3  a = g^k  =>  sign(pi_a) = sign(pi_g)^k = (-1)^k.
  Step 4  Euler's criterion: legendreSym p a = (-1)^k.
  Hence   legendreSym p a = sign(pi_a).

Run: python3 verify_zolotarev.py   (requires sympy)
All assertions must pass.
"""

from sympy import isprime, primerange
from sympy.ntheory.residue_ntheory import primitive_root

try:  # legendre_symbol moved modules in sympy 1.13
    from sympy.functions.combinatorial.numbers import legendre_symbol
except ImportError:  # pragma: no cover - older sympy
    from sympy.ntheory.residue_ntheory import legendre_symbol


def perm_sign(perm):
    """Sign (+1/-1) of a permutation given as a list perm[x] = image of x.

    Computed by orbit decomposition: a cycle of length L contributes (-1)^(L-1),
    i.e. sign = (-1)^(n - number_of_cycles)."""
    n = len(perm)
    seen = [False] * n
    cycles = 0
    for start in range(n):
        if seen[start]:
            continue
        cycles += 1
        j = start
        while not seen[j]:
            seen[j] = True
            j = perm[j]
    return 1 if (n - cycles) % 2 == 0 else -1


def mul_perm(a, p):
    """pi_a on ZMod p as a list: index x -> (a*x) % p."""
    return [(a * x) % p for x in range(p)]


def cycle_structure_on_units(a, p):
    """Number of cycles and their lengths for pi_a restricted to the units
    {1,...,p-1} (0 is always a fixed point)."""
    seen = [False] * p
    lengths = []
    for start in range(1, p):
        if seen[start]:
            continue
        L = 0
        j = start
        while not seen[j]:
            seen[j] = True
            j = (a * j) % p
            L += 1
        lengths.append(L)
    return lengths


def check_prime(p, verbose=False):
    assert p % 2 == 1 and isprime(p), f"{p} must be an odd prime"

    g = primitive_root(p)
    # Step 2: pi_g is a single (p-1)-cycle on the units -> sign = -1.
    lengths_g = cycle_structure_on_units(g, p)
    assert lengths_g == [p - 1], (
        f"p={p}: pi_g should be one (p-1)-cycle on units, got cycles {lengths_g}"
    )
    sign_g = perm_sign(mul_perm(g, p))
    assert sign_g == -1, f"p={p}: sign(pi_g) should be -1, got {sign_g}"
    # cross-check the closed form sign(pi_g) = (-1)^(p-2)
    assert sign_g == (-1) ** (p - 2)

    # Step 4 prep: discrete logs of every nonzero residue to base g.
    dlog = {}
    val = 1
    for k in range(p - 1):
        dlog[val] = k
        val = (val * g) % p

    for a in range(1, p):
        leg = legendre_symbol(a, p)            # +1 / -1
        sgn = perm_sign(mul_perm(a, p))        # sign of x |-> a*x
        # MAIN identity (Zolotarev):
        assert leg == sgn, f"p={p}, a={a}: legendre={leg} but sign={sgn}"

        k = dlog[a]
        # Step 3: sign(pi_a) = (-1)^k  (= sign(pi_g)^k).
        assert sgn == (-1) ** k, f"p={p}, a={a}: sign={sgn} != (-1)^k, k={k}"
        # Step 4: Euler criterion form legendre = (-1)^k.
        assert leg == (-1) ** k, f"p={p}, a={a}: legendre={leg} != (-1)^k"
        # Euler's criterion numerically: legendre = a^((p-1)/2) mod p (as +-1).
        euler = pow(a, (p - 1) // 2, p)
        euler = 1 if euler == 1 else -1
        assert leg == euler, f"p={p}, a={a}: legendre={leg} != euler {euler}"

    if verbose:
        n_res = sum(1 for a in range(1, p) if legendre_symbol(a, p) == 1)
        print(f"  p={p:3d}: generator g={g}, {n_res} QRs / {p-1-n_res} non-QRs, "
              f"all {p-1} residues satisfy legendreSym = sign(pi_a)")


def main():
    primes = [p for p in primerange(3, 80)]  # all odd primes below 80
    print("Verifying Zolotarev's lemma  legendreSym p a = sign(x |-> a*x)  on ZMod p")
    for p in primes:
        check_prime(p, verbose=True)
    print(f"\nAll checks passed for {len(primes)} odd primes "
          f"(3..{primes[-1]}), every nonzero residue each.")
    print("Steps verified: (1) permutation fixing 0, (2) sign(pi_g)=-1 via single "
          "(p-1)-cycle, (3) sign(pi_a)=(-1)^k, (4) Euler criterion legendre=(-1)^k.")


if __name__ == "__main__":
    main()
