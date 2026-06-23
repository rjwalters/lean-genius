#!/usr/bin/env python3
"""
Certificate: a SINGLE linear arithmetic progression of primes, p ≡ 1 (mod 4n),
is a universal quadratic-residue-seed supplier for the "if" direction of
Legendre's three-square theorem — for EVERY non-excluded core n, across ALL
residue classes mod 8, not just n ≡ 3 (mod 8).

Context
-------
proofs/Proofs/ThreeSquares.lean reduces the sufficiency direction
(¬IsExcludedForm n ⟹ n = x²+y²+z²) to two axioms:
  - `dirichlet_key_lemma`: keyed on a prime of the RIGID form p = d·n − 1 with
    the side-condition (−d | p) = 1, and
  - `not_excluded_form_is_sum_three_sq`: a mod-8 case split that picks d per
    residue class and feeds `dirichlet_key_lemma`.

Two prior certificates in this directory established, for the n ≡ 3 (mod 8)
class only:
  - verify_residue3_obstruction.py / ThreeSquaresResidue3Obstruction.lean:
    the rigid form p = d·n − 1 is UNSATISFIABLE for n ≡ 3 (mod 8) (Jacobi
    reciprocity forces (−n|p) = −1 on the residue p ≡ −1 (mod n));
  - verify_single_ap_residue3.py: dropping the rigid tie and asking only for a
    prime p ≡ 1 (mod 4n) repairs the n ≡ 3 (mod 8) class via one linear AP.

This certificate generalizes the repair to the WHOLE theorem.

Finding (certified here)
------------------------
For p ≡ 1 (mod 4n) the Kronecker character χ_{−n} (conductor | 4n) evaluates at
residue 1, so (−n | p) = χ_{−n}(1) = 1 — independent of n's residue mod 8 and of
n's parity. Concretely:
  - p ≡ 1 (mod 4)  ⟹ (−1 | p) = 1, hence (−n | p) = (n | p).
  - n even, n = 2^k·m (m odd): 8 | 4n ⟹ p ≡ 1 (mod 8) ⟹ (2 | p) = 1, so the
    even part contributes 1; (m | p) = (p | m) [p ≡ 1 mod 4] = (1 | m) = 1
    [p ≡ 1 mod m]. So (−n | p) = 1.
  - n odd: (n | p) = (p | n) [p ≡ 1 mod 4] = (1 | n) = 1 [p ≡ 1 mod n].
In every case (−n | p) = 1, so −n is a quadratic residue mod p: ∃ r, r² ≡ −n
(mod p). That is exactly the isotropy seed the Dirichlet sublattice construction
needs (the form Q = x² + n·(…) ≡ 0 (mod p) on the congruence sublattice).

Consequence for the Lean proof architecture
--------------------------------------------
The mod-8 case split in `not_excluded_form_is_sum_three_sq` is supplying the QR
seed by a different d per class. This certificate shows ONE class — the prime AP
p ≡ 1 (mod 4n), gcd(1, 4n) = 1 always so Mathlib's `PrimesInAP` applies
unconditionally — supplies it uniformly for all non-excluded n. So the seed step
can collapse from a 5-way (residues 1,2,3,5,6) case split to a single
`PrimesInAP` instantiation.

SCOPE / HONESTY NOTE: this certifies only the QUADRATIC-RESIDUE seed, i.e. that
−n is a QR mod a prime drawn from one fixed AP. It does NOT by itself discharge
`dirichlet_key_lemma`: the representation n = x²+y²+z² still requires the
Minkowski geometry-of-numbers step on the congruence sublattice, which is the
distinct build-gated Lean work (the existing `minkowski_ellipsoid_has_lattice_point`
is over the standard ℤ³ lattice; the sublattice instance is still missing). The
brute-force check (4) below is a cross-check that the cores are genuinely
representable, not evidence that QR ⟹ representation.

What is checked (build-free, pure stdlib + sympy)
-------------------------------------------------
For every square-free non-excluded core n (n % 8 ≠ 7) up to N, across residues
n % 8 ∈ {1,2,3,5,6}:
  (1) (−n | p) depends only on p mod 4n              (character periodicity)
  (2) every prime p ≡ 1 (mod 4n) has (−n | p) = 1    (universal seed class)
  (3) a concrete prime p ≡ 1 (mod 4n) exists         (Dirichlet, made explicit)
  (4) n really is a sum of three squares             (brute-force cross-check)

Run: python3 verify_universal_single_ap.py
"""
import math
from sympy import jacobi_symbol, primerange


def squarefree(n: int) -> bool:
    i = 2
    while i * i <= n:
        if n % (i * i) == 0:
            return False
        i += 1
    return True


def is_sum_three_squares(n: int) -> bool:
    for x in range(math.isqrt(n) + 1):
        for y in range(x, math.isqrt(n - x * x) + 1):
            z2 = n - x * x - y * y
            if z2 >= 0 and math.isqrt(z2) ** 2 == z2:
                return True
    return False


def check(N: int = 4000) -> bool:
    ns = [n for n in range(2, N) if squarefree(n) and n % 8 != 7]
    by_res = {r: 0 for r in (1, 2, 3, 5, 6)}
    periodicity_ok = True
    universal_qr = True
    concrete_prime = 0
    reps_ok = 0
    violations = []

    for n in ns:
        M = 4 * n
        by_res[n % 8] = by_res.get(n % 8, 0) + 1
        # (1) periodicity of (-n|p) mod 4n
        seen = {}
        for p in primerange(3, 30 * n):
            if p == n or n % p == 0:
                continue
            r = p % M
            v = jacobi_symbol((-n) % p, p)
            if r in seen and seen[r] != v:
                periodicity_ok = False
            seen[r] = v
        # (2)+(3) the a = 1 class: EVERY sampled prime p ≡ 1 mod 4n has (-n|p)=1
        found = None
        sampled = 0
        for p in primerange(2, 400 * n):
            if p % M == 1 and p != n and n % p:
                if jacobi_symbol((-n) % p, p) != 1:
                    universal_qr = False
                    violations.append((n, p))
                if found is None:
                    found = p
                sampled += 1
                if sampled >= 3:
                    break
        if found is not None:
            concrete_prime += 1
        # (4) n is a sum of three squares (cross-check)
        if is_sum_three_squares(n):
            reps_ok += 1

    total = len(ns)
    print(f"square-free non-excluded cores (n%8 != 7) in [2,{N}): {total}")
    print(f"   by residue mod 8: {by_res}")
    print(f"(1) (-n|p) periodic mod 4n:                  {periodicity_ok}")
    print(f"(2) every prime p≡1 mod 4n has (-n|p)=1:     {universal_qr} "
          f"(violations: {len(violations)})")
    print(f"(3) concrete prime p≡1 mod 4n found:         {concrete_prime}/{total}")
    print(f"(4) n is a sum of three squares:             {reps_ok}/{total}")
    ok = (periodicity_ok and universal_qr and concrete_prime == total
          and reps_ok == total)
    print("ALL CHECKS PASS" if ok else "FAILURE")
    return ok


if __name__ == "__main__":
    import sys
    sys.exit(0 if check() else 1)
