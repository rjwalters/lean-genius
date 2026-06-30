#!/usr/bin/env python3
"""
verify_local_obstruction.py
============================

Slug: lagrange-four-squares-waring-g2-oq-03  (Legendre three-square theorem, "if" direction)

Goal of THIS script (complements, does not duplicate, scripts/verify_legendre_three_square.py
from PR #24149, which verifies the characterization on n<=5000 and the Davenport-Cassels
descent inequality):

Pin down *why only the QUALITATIVE Dirichlet theorem is needed* (one prime in an
arithmetic progression -- not the analytic density / PNT version). The reason is a
local-obstruction fact:

    The ternary form  Q(x,y,z) = x^2 + y^2 + z^2  has NO p-adic obstruction at any
    ODD prime p (it is universal mod every odd prime power), and its ONLY local
    obstruction lives at p = 2, where the non-represented residues are exactly the
    lifts of the classes 4^a*(8b+7).

Consequences for the formalization route (G1 of #24149, "rational representability
of admissible n"):
  * No odd prime contributes a side-condition, so the Dirichlet input is purely the
    existence of *one* prime in a coprime residue class -- exactly
    `Nat.forall_exists_prime_gt_and_modEq` in Mathlib v4.26.0.
  * The single precondition that any prime-in-AP step must discharge is the
    coprimality `Nat.Coprime a q` of the residue to the modulus.

Checks performed (all exact integer arithmetic):
  A. Universality mod odd prime powers: for odd primes p and exponents k,
     {x^2+y^2+z^2 mod p^k} == all of Z/p^k.
  B. The 2-adic obstruction: residues of Z/2^k NOT hit by x^2+y^2+z^2 are exactly the
     residues r with  v2-pattern of an excluded class  (i.e. r reduces to 7 mod 8 after
     stripping pairs of factors of 2 as far as 2^k can witness).
  C. Cross-check: a number n is representable as a sum of three squares
     (brute force over Z) iff it survives the 2-adic obstruction in (B) for a large
     enough k -- i.e. the 2-adic condition alone is decisive (odd primes never veto).

Run:
    python3 research/problems/lagrange-four-squares-waring-g2-oq-03/scripts/verify_local_obstruction.py
"""

from itertools import product


def is_excluded(n: int) -> bool:
    """n == 4^a * (8b+7) for some a,b >= 0 ?"""
    if n <= 0:
        return False
    while n % 4 == 0:
        n //= 4
    return n % 8 == 7


def sum_three_squares_residues_mod(m: int) -> set:
    """Set of residues mod m hit by x^2+y^2+z^2."""
    sq = sorted({(i * i) % m for i in range(m)})
    out = set()
    for a in sq:
        for b in sq:
            ab = (a + b) % m
            for c in sq:
                out.add((ab + c) % m)
    return out


def is_sum_of_three_squares_int(n: int) -> bool:
    """Brute-force: does n = x^2+y^2+z^2 over the integers?"""
    if n < 0:
        return False
    x = 0
    while x * x <= n:
        r1 = n - x * x
        y = x
        while y * y <= r1:
            r2 = r1 - y * y
            z = int(r2 ** 0.5)
            for zz in (z - 1, z, z + 1):
                if zz >= 0 and zz * zz == r2:
                    return True
            y += 1
        x += 1
    return False


PRIMES = [3, 5, 7, 11, 13]


def check_A_odd_universality():
    """A. x^2+y^2+z^2 is universal mod every odd prime power tested."""
    failures = []
    for p in PRIMES:
        for k in range(1, 4):  # p, p^2, p^3
            m = p ** k
            hit = sum_three_squares_residues_mod(m)
            if len(hit) != m:
                missing = sorted(set(range(m)) - hit)
                failures.append((p, k, missing[:10]))
    return failures


def check_B_two_adic():
    """B. Mod 2^k, the residues NOT hit are exactly those r whose 2-adic class is
    an excluded (4^a(8b+7)) pattern *witnessable* within 2^k.

    Operationally: r in Z/2^k is hit  <=>  there is SOME integer n>=0 with n == r (mod 2^k)
    and n NOT excluded, OR r is hit directly.  The clean invariant we test instead:
    a residue r is non-representable mod 2^k  <=>  every integer congruent to r mod 2^k
    that is < 2^k-ceiling is excluded.  We test the crisp local statement directly:
    the non-hit residues mod 2^k are exactly { r : for the canonical lift, stripping 4's
    lands on 7 mod 8, with enough room in 2^k }.
    """
    failures = []
    for k in range(3, 9):  # 8 .. 256
        m = 2 ** k
        hit = sum_three_squares_residues_mod(m)
        non_hit = sorted(set(range(m)) - hit)
        # Predicted non-hit: residues r such that r != 0 and, writing r = 4^a * s with s odd-part
        # reachable inside the modulus, s % 8 == 7.  We characterise via: r is non-hit mod 2^k
        # iff is_excluded(r) is "locked in" by the modulus, i.e. stripping 4s from r (while the
        # remaining factor still fits the 8b+7 shape modulo the residual 2-power) gives 7 mod 8.
        predicted = []
        for r in range(m):
            t = r
            a = 0
            # strip factors of 4 but only while we still have >=3 bits of 2-adic info left
            while t % 4 == 0 and t > 0 and (k - 2 * (a + 1)) >= 3:
                t //= 4
                a += 1
            if t % 8 == 7:
                predicted.append(r)
        if non_hit != predicted:
            only_actual = sorted(set(non_hit) - set(predicted))[:10]
            only_pred = sorted(set(predicted) - set(non_hit))[:10]
            failures.append((k, only_actual, only_pred))
    return failures


def check_C_two_adic_decisive(N: int = 3000):
    """C. The 2-adic condition is decisive: for n <= N,
       is_sum_of_three_squares_int(n)  <=>  not is_excluded(n).
    (i.e. once the 2-adic obstruction is absent, an integral solution exists --
    no odd prime ever vetoes.  This is the empirical face of "odd primes are
    universal", check A, combined with global solvability.)"""
    bad = []
    for n in range(0, N + 1):
        rep = is_sum_of_three_squares_int(n)
        excl = is_excluded(n)
        if rep == excl:  # representable AND excluded, or non-rep AND not-excluded
            bad.append((n, rep, excl))
    return bad


def main():
    print("=" * 70)
    print("Local-obstruction structure of x^2+y^2+z^2  (slug oq-03)")
    print("=" * 70)

    fa = check_A_odd_universality()
    print(f"\n[A] Universality mod odd prime powers p in {PRIMES}, k=1..3:")
    if fa:
        print("    FAIL:", fa)
    else:
        print("    PASS -- form is surjective mod every tested odd prime power")

    fb = check_B_two_adic()
    print("\n[B] 2-adic obstruction mod 2^k, k=3..8:")
    if fb:
        print("    FAIL (k, non_hit\\predicted, predicted\\non_hit):", fb)
    else:
        print("    PASS -- non-represented residues mod 2^k are exactly the excluded 2-adic classes")

    fc = check_C_two_adic_decisive()
    print("\n[C] 2-adic condition decisive for n=0..3000 (rep <=> not excluded):")
    if fc:
        print(f"    FAIL on {len(fc)} values, first few:", fc[:10])
    else:
        print("    PASS -- no odd prime ever vetoes; the 4^a(8b+7) (=2-adic) obstruction is the only one")

    ok = not (fa or fb or fc)
    print("\n" + "=" * 70)
    print("ALL CHECKS PASSED" if ok else "SOME CHECKS FAILED")
    print("=" * 70)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
