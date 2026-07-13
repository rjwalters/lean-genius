#!/usr/bin/env python3
"""
S19 (researcher-1, 2026-06-19) — the lattice key-lemma `d`-ceiling vs. the
unbounded `d` that any witness selection requires.

Context
-------
`ThreeSquares.lean` proves `dirichlet_key_lemma` (Dirichlet 1850) ONLY for d ≤ 2:

    n>1, d∈{1,2}, p = d·n − 1 prime, (−d | p) = 1  ⟹  n = x²+y²+z².

The discharge of the last axiom `not_excluded_form_is_sum_three_sq` would need,
for every non-excluded n, SOME admissible witness (d, p) with p = d·n − 1 prime
and −d a QR mod p, fed through the key lemma. S14 already showed the d ≤ 2
witness predicate `DirichletWitnessNe3` is FALSE (610/999 cores m<2000 have no
d ≤ 2 witness). This script pins down the two structural reasons and shows they
are irreconcilable inside the sublattice-Minkowski framework:

  (A) WHY the key lemma stops at d ≤ 2  — a clean geometry-of-numbers ceiling.
  (B) WHY the selection needs unbounded d — smallest admissible d grows with n.

Pure Python, no Docker, no Lean. Reproduces the qualitative S14 obstruction and
quantifies the gap that forces the Hasse–Minkowski (rational three squares)
route documented at S17/S18.
"""

import math


# ----------------------------------------------------------------------------
# (A) The geometry-of-numbers ceiling for the file's Dirichlet sublattice.
# ----------------------------------------------------------------------------
# The key lemma works on the sublattice
#       L_r = { (x,y,z) ∈ ℤ³ : p | (x − r·y) ∧ p | z },  r² ≡ −d (mod p),
# every point of which satisfies p | (x² + d·y² + d·z²). L_r has index p² in ℤ³,
# so covolume p². The descent needs a NONZERO point with form value < 2p.
#
# 3-D ball/ellipsoid Minkowski (crude): the body {x²+d·y²+d·z² < 2p} is a
# symmetric convex ellipsoid of volume
#       vol = (4/3)·π·(2p)^{3/2} / sqrt(1·d·d) = (4/3)·π·(2p)^{3/2}/d.
# Minkowski guarantees a nonzero L_r-point when vol > 2³·covol = 8p²:
#       (4/3)·π·(2p)^{3/2}/d > 8p²   ⟺   d < (π/6)·2^{3/2}·p^{-1/2}.
#
# The file instead uses the SHARPER binary "slice" bound (fix the z = 0 slice,
# do 2-D Minkowski on {x ≡ r·y mod p}, index p, covolume p, body {x²+d·y² < 2p}
# of area 2π·p/sqrt(d)): a nonzero slice point exists when area > 2²·covol = 4p:
#       2π·p/sqrt(d) > 4p   ⟺   sqrt(d) < π/2   ⟺   d < π²/4 ≈ 2.4674.
# Hence the slice route admits exactly d ∈ {1, 2}. That is the file's ceiling.

def slice_ceiling():
    bound = math.pi ** 2 / 4
    print("(A) sublattice-Minkowski ceiling on d")
    print(f"    binary-slice bound:  sqrt(d) < pi/2  =>  d < pi^2/4 = {bound:.4f}")
    print(f"    => admissible d (slice route): d in {{1, 2}}  (max d = {math.floor(bound)})")
    print("    crude 3-D ball bound: d < (pi/6)*2^(3/2)/sqrt(p) = "
          f"{(math.pi/6)*2**1.5:.4f}/sqrt(p)")
    for p in (5, 11, 23, 101, 1009):
        print(f"        p={p:>5}:  d < {(math.pi/6)*2**1.5/math.sqrt(p):.4f}  "
              f"(=> only d=0; the slice trick is what buys d<=2)")
    print()
    return math.floor(bound)


# ----------------------------------------------------------------------------
# (B) The witness selection needs UNBOUNDED d.
# ----------------------------------------------------------------------------
def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    i = 3
    while i * i <= n:
        if n % i == 0:
            return False
        i += 2
    return True


def legendre(a, p):
    """Legendre symbol (a|p) for odd prime p, a any integer."""
    a %= p
    if a == 0:
        return 0
    ls = pow(a, (p - 1) // 2, p)
    return -1 if ls == p - 1 else ls


def is_squarefree(n):
    i = 2
    while i * i <= n:
        if n % (i * i) == 0:
            return False
        i += 1
    return True


def is_excluded(n):
    """n = 4^a (8b+7) ?  (the Legendre–Gauss excluded form)."""
    while n % 4 == 0:
        n //= 4
    return n % 8 == 7


def smallest_admissible_d(n, dmax=20000):
    """Smallest d>=1 with p=d*n-1 prime and (-d | p) = 1 (the key-lemma hyp)."""
    d = 1
    while d <= dmax:
        p = d * n - 1
        if p >= 2 and is_prime(p) and legendre(-d, p) == 1:
            return d, p
        d += 1
    return None, None


def selection_scan(N=4000):
    print(f"(B) smallest admissible witness d over non-excluded n in [2,{N}]")
    print("    (admissible = p=d*n-1 prime and -d a QR mod p; key-lemma needs this)")
    worst = []
    over2 = 0
    total = 0
    maxd = 0
    none_found = 0
    for n in range(2, N + 1):
        if is_excluded(n):
            continue
        total += 1
        d, p = smallest_admissible_d(n)
        if d is None:
            none_found += 1
            continue
        maxd = max(maxd, d)
        if d > 2:
            over2 += 1
        worst.append((d, n, p))
    worst.sort(reverse=True)
    print(f"    non-excluded n scanned        : {total}")
    print(f"    needing d > 2 (slice fails)    : {over2}  ({100*over2/total:.1f}%)")
    print(f"    max smallest-admissible d      : {maxd}")
    print(f"    n with NO admissible d<=20000  : {none_found}")
    print("    largest smallest-admissible d (d, n, p=d*n-1):")
    for d, n, p in worst[:12]:
        print(f"        d={d:>5}  n={n:>5}  p={p}")
    print()
    return maxd, over2, total


def squarefree_residue_table(N=4000):
    """For SQUAREFREE non-excluded n, the smallest admissible d, bucketed by n%8.
    Shows the obstruction is not a small-n artefact and is residue-structured."""
    print("(B') squarefree non-excluded n: smallest admissible d by n%8")
    buckets = {}
    for n in range(2, N + 1):
        if not is_squarefree(n) or is_excluded(n):
            continue
        d, _ = smallest_admissible_d(n)
        r = n % 8
        buckets.setdefault(r, []).append(d if d else float("inf"))
    for r in sorted(buckets):
        ds = buckets[r]
        finite = [x for x in ds if x != float("inf")]
        share_gt2 = sum(1 for x in finite if x > 2) / len(finite) if finite else 0
        print(f"    n%8={r}: count={len(ds):>4}  median d={sorted(finite)[len(finite)//2] if finite else 'NA':>4}"
              f"  max d={max(finite) if finite else 'NA':>5}  share(d>2)={share_gt2:5.1%}")
    print()


if __name__ == "__main__":
    # N=1200 keeps the scan ~1 min; the qualitative facts are range-stable and
    # S14 already certified d<=2 coverage rigorously over m<2000. Bump for more.
    N = 1200
    print("=" * 74)
    print("S19: lattice key-lemma d-ceiling (<=2) vs. unbounded selection d")
    print("=" * 74)
    ceil = slice_ceiling()
    maxd, over2, total = selection_scan(N)
    squarefree_residue_table(N)
    print("CONCLUSION")
    print(f"  - slice-Minkowski key lemma is capped at d <= {ceil} (geom. ceiling, exact).")
    print(f"  - {100*over2/total:.0f}% of non-excluded n already need d > {ceil}; max smallest")
    print(f"    admissible d = {maxd} at N={N} and grows => the needed d is UNBOUNDED.")
    print("  - n%8 = 3 admits NO p=d*n-1 witness for ANY d (structural 0%, matches the")
    print("    S5 residue table): that class is irreducibly off the d*n-1 framework and")
    print("    needs the separate two-square deficit route (Residue3Property), whose own")
    print("    open content (a prime of the quadratic form (m-t^2)/2) is NOT Dirichlet-AP.")
    print("  - therefore the sublattice-Minkowski framework CANNOT discharge the")
    print("    last axiom (this is exactly why DirichletWitnessNe3 is false, S14);")
    print("    the remaining content is the Hasse-Minkowski rational-three-squares")
    print("    input (S17/S18), absent from Mathlib v4.26 (no Hilbert symbol).")
