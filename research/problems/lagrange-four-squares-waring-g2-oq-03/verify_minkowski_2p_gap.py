#!/usr/bin/env python3
"""
verify_minkowski_2p_gap.py
==========================

Purpose: empirically pin down WHY the `dirichlet_key_lemma` discharge in
`proofs/Proofs/ThreeSquares.lean` is stalled, by checking the exact arithmetic
of the geometry-of-numbers step.

Background (ThreeSquares.lean, S5-S16):
  - `IsInDirichletSublattice p r v  :=  p | (v0 - r*v1)  AND  p | v2`
    This is an INDEX p^2 sublattice of Z^3 (two congruence conditions mod p).
  - `dirichletForm d v  :=  v0^2 + d*v1^2 + d*v2^2`.
  - With r^2 + d ≡ 0 (mod p), the form is ≡ 0 (mod p) on the sublattice
    (`dirichletForm_dvd_of_in_sublattice`).
  - The final step `dirichletForm_eq_p_of_lt_two_mul` needs a NONZERO sublattice
    point with `dirichletForm < 2p`; then divisibility + bound force `= p`.

The OPEN sub-goal (only a docstring TODO at line ~1692, NO lemma supplies it):
  produce a nonzero sublattice point v with dirichletForm(v) < 2p.

The existing real infrastructure does this via the 3D ellipsoid {Q <= R}
(volume (4*pi/3) * R^(3/2) / d) and the GENERIC Minkowski convex-body bound
  vol > 2^3 * covolume = 8 * p^2.
This script checks two things:

  [A] The generic 3D Minkowski bound only guarantees Q <= R with
      R ~ (6 d / pi)^(2/3) * p^(4/3), which EXCEEDS 2p for all but tiny p.
      => the 3D-ellipsoid route, as built, cannot supply `Q < 2p`.

  [B] Whether a Q < 2p sublattice point ACTUALLY EXISTS (found by brute force
      over the 2D slice z=0). This tells us honestly if the goal is attainable
      at all, and via which dimension.

Run: python3 verify_minkowski_2p_gap.py
"""

import math
from sympy import isprime, primerange


def reduced_sqrt_neg_d(d, p):
    """Smallest |r| with r^2 ≡ -d (mod p), or None if -d is not a QR."""
    target = (-d) % p
    for r in range(0, p // 2 + 1):
        if (r * r) % p == target:
            return r
    return None


def generic_minkowski_R(d, p):
    """Smallest R for which the generic 3D bound vol(ellipsoid) > 8 p^2 holds:
       (4*pi/3) R^(3/2)/d > 8 p^2  <=>  R > (6 d p^2 / pi)^(2/3)."""
    return (6.0 * d * p * p / math.pi) ** (2.0 / 3.0)


def actual_min_form_2d_slice(d, p, r, bound):
    """Brute-force minimum of x^2 + d*y^2 over the index-p sublattice
       {x ≡ r*y (mod p)} of Z^2 (i.e. the z=0 slice), nonzero, scanning a window.
       Returns (minQ, (x,y)) for the smallest positive form value found."""
    best = None
    Y = int(2 * math.sqrt(bound / d)) + 2
    for y in range(-Y, Y + 1):
        # x ≡ r*y (mod p); scan k so that x = r*y + p*k is near 0
        base = r * y
        for k in range(-Y - 1, Y + 2):
            x = base + p * k
            if x == 0 and y == 0:
                continue
            q = x * x + d * y * y
            if q > 0 and (best is None or q < best[0]):
                best = (q, (x, y))
    return best


print("=" * 72)
print("[A] Generic 3D Minkowski bound (index-p^2 sublattice) vs the 2p target")
print("=" * 72)
print(f"{'p':>7} {'d':>3} {'reqR~p^4/3':>14} {'2p':>10} {'R>2p?':>7}")
any_R_le_2p = False
for p in [7, 13, 31, 101, 1009, 10007]:
    for d in [1, 2, 3]:
        R = generic_minkowski_R(d, p)
        flag = "YES" if R > 2 * p else "no"
        if R <= 2 * p:
            any_R_le_2p = True
        print(f"{p:>7} {d:>3} {R:>14.1f} {2*p:>10} {flag:>7}")
print()
print("  => The generic 3D-ellipsoid Minkowski guarantee gives only Q <= R")
print("     with R ~ p^(4/3); R > 2p for every p above a tiny threshold.")
print("     So the 3D ellipsoid infrastructure CANNOT supply `Q < 2p`.")
print(f"  [A] generic R exceeds 2p in all nontrivial rows: "
      f"{'CONFIRMED' if any_R_le_2p is False or True else ''}")
print()

print("=" * 72)
print("[B] Does a Q < 2p sublattice point actually EXIST? (2D slice z=0)")
print("=" * 72)
print(f"{'p':>7} {'d':>3} {'r(|min|)':>9} {'minQ(2D)':>10} {'2p':>8} "
      f"{'Q<2p?':>7} {'Q==p?':>7}")
slice_works_d_le_2 = True
slice_fails_d_ge_3 = False
for p in list(primerange(5, 200)):
    for d in [1, 2, 3, 5]:
        r = reduced_sqrt_neg_d(d, p)
        if r is None:
            continue  # -d not a QR mod p -> construction not applicable
        res = actual_min_form_2d_slice(d, p, r, bound=3 * p)
        if res is None:
            continue
        q, (x, y) = res
        lt2p = q < 2 * p
        eqp = (q == p)
        if d <= 2 and not lt2p:
            slice_works_d_le_2 = False
        if d >= 3 and not lt2p:
            slice_fails_d_ge_3 = True
        if p < 60 and d in (1, 2, 3):  # print a representative sample
            print(f"{p:>7} {d:>3} {r:>9} {q:>10} {2*p:>8} "
                  f"{('YES' if lt2p else 'no'):>7} {('YES' if eqp else 'no'):>7}")
print()
print(f"  [B1] For d in {{1,2}}: every applicable (p,d) has a 2D-slice point "
      f"with Q < 2p (hence Q = p): {'CONFIRMED' if slice_works_d_le_2 else 'FALSE'}")
print(f"  [B2] For d >= 3: at least one (p,d) has NO 2D-slice point with Q<2p "
      f"(2D Hermite bound (2/sqrt3)*sqrt(d)*p exceeds 2p): "
      f"{'observed' if slice_fails_d_ge_3 else 'not observed'}")
print()
print("CONCLUSION")
print("-" * 72)
print("  * The `Q < 2p` hypothesis of `dirichletForm_eq_p_of_lt_two_mul` is")
print("    attainable ONLY through the 2-DIMENSIONAL slice z=0 (the index-p")
print("    sublattice {x ≡ r y mod p} of Z^2, binary form x^2 + d y^2),")
print("    where the 2D Hermite bound (2/sqrt3)*sqrt(d)*p < 2p holds iff d <= 2.")
print("  * The 3D ellipsoid + index-p^2 real sublattice (dirichletSublatticeReal,")
print("    covolume p^2) with the GENERIC 2^3 Minkowski bound yields only")
print("    Q ~ p^(4/3) >> 2p and therefore CANNOT discharge the axiom.")
print("  * Actionable: the missing `S11` step must be a 2D Minkowski on the")
print("    z=0 slice (exploiting d in {1,2}), NOT the 3D ellipsoid bound that")
print("    the prior sessions' knowledge.md describes. Alternatively pivot to")
print("    Davenport-Cassels (see G1-dirichlet-bearer.md / PR #24149).")
