#!/usr/bin/env python3
"""
verify_slice_constructive_witness.py
====================================

Purpose: certify that the SOLE remaining open leaf of `dirichlet_key_lemma`
in `proofs/Proofs/ThreeSquares.lean` -- namely

  ThreeSquaresSlice.exists_slice_point_lt_two_mul
    (p d : ℕ) (hp : 0 < p) (hd : 0 < d) (hd2 : d ≤ 2) (r : ℤ) :
      ∃ x y : ℤ, (x, y) ≠ (0, 0) ∧ (p : ℤ) ∣ (x - r * y) ∧
        x ^ 2 + (d : ℤ) * y ^ 2 < 2 * p

-- admits an EXPLICIT, CONSTRUCTIVE witness, so its Lean proof need not port the
heavy measure-theoretic Minkowski machinery
(`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`)
down to two dimensions.

Background (researcher-11, G2-minkowski-2p-gap.md): the 3D index-p^2 ellipsoid
route cannot supply `Q < 2p` (generic 2^n Minkowski only gives Q ~ p^(4/3)).
The attainable route is the 2D slice z=0: the index-p sublattice
`L = {(x,y) ∈ ℤ² : p ∣ (x − r·y)}` with the binary form N(x,y)=x²+d·y². The
abstract claim is the 2D Minkowski/Hermite bound. This script shows the SAME
bound is realized CONSTRUCTIVELY by Lagrange–Gauss reduction of the explicit
sublattice basis {(p,0),(r,1)} under the d-weighted inner product -- which is
elementary (no measure theory) and terminates in a handful of steps.

Two things the prior cert (verify_minkowski_2p_gap.py) did NOT establish:
  1. It only scanned r = reduced sqrt(-d) mod p. The Lean leaf is stated for an
     ARBITRARY r:ℤ. Here we certify ALL residues r ∈ {0,...,p-1}.
  2. It used a brute-force window search, giving no algorithm. Here the witness
     is produced by a deterministic O(log p) reduction, the shape a Lean proof
     would induct on.

Checks (p < PMAX prime, d ∈ {1,2}, every r):
  [A] The reduced shortest vector v is NONZERO and lies in L (p ∣ v0 − r·v1).
  [B] N(v) < 2p  ==>  discharges exists_slice_point_lt_two_mul.
  [C] The worst-case ratio N(v)/p approaches the 2D Hermite ceiling
      gamma_2 * sqrt(d) = (2/√3)·√d, which is < 2 exactly for d ≤ 2
      (d=1: 1.1547, d=2: 1.6330); for d=3 it is 2.0000 -- the boundary that
      forces the `d ≤ 2` hypothesis.
  [D] Reduction terminates in a small bounded number of steps (O(log p)).

Run: python3 verify_slice_constructive_witness.py
"""

import math

PMAX = 2000


def primes_below(n):
    sieve = bytearray([1]) * n
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    return [i for i in range(2, n) if sieve[i]]


def norm(v, d):
    x, y = v
    return x * x + d * y * y


def dot(a, b, d):
    return a[0] * b[0] + d * a[1] * b[1]


def gauss_reduce(b1, b2, d):
    """Lagrange–Gauss 2D reduction under the d-weighted inner product
       <(x1,y1),(x2,y2)> = x1*x2 + d*y1*y2. Returns (b1,b2,steps) with b1 the
       shortest nonzero vector of the lattice spanned by the inputs."""
    steps = 0
    while True:
        if norm(b2, d) < norm(b1, d):
            b1, b2 = b2, b1
        n1 = norm(b1, d)
        if n1 == 0:
            return b1, b2, steps
        # closest-integer projection coefficient
        m = round(dot(b1, b2, d) / n1)
        if m == 0:
            return b1, b2, steps
        b2 = (b2[0] - m * b1[0], b2[1] - m * b1[1])
        steps += 1


def shortest_in_sublattice(p, d, r):
    """Constructive shortest vector of L = {(x,y): p | (x - r y)} under N(.,d).
       Basis: (p,0) and (r,1) (these generate L: x = r*y + p*k)."""
    s1, s2, steps = gauss_reduce((p, 0), (r, 1), d)
    v = s1 if norm(s1, d) <= norm(s2, d) else s2
    return v, steps


def main():
    primes = primes_below(PMAX)
    checked = 0
    bound_fail = 0
    membership_fail = 0
    zero_fail = 0
    worst_ratio = {1: 0.0, 2: 0.0}
    worst_at = {1: None, 2: None}
    max_steps = 0

    for p in primes:
        for d in (1, 2):
            for r in range(0, p):
                v, steps = shortest_in_sublattice(p, d, r)
                checked += 1
                max_steps = max(max_steps, steps)
                if v == (0, 0):
                    zero_fail += 1
                if (v[0] - r * v[1]) % p != 0:
                    membership_fail += 1
                q = norm(v, d)
                if not (q < 2 * p):
                    bound_fail += 1
                ratio = q / p
                if ratio > worst_ratio[d]:
                    worst_ratio[d] = ratio
                    worst_at[d] = (p, r, v, q)

    hermite = {d: (2.0 / math.sqrt(3.0)) * math.sqrt(d) for d in (1, 2, 3)}

    print("=" * 72)
    print("Constructive Q<2p witness via Lagrange–Gauss reduction")
    print(f"p prime < {PMAX}, d ∈ {{1,2}}, EVERY residue r ∈ [0,p)")
    print("=" * 72)
    print(f"triples checked .......... {checked}")
    print(f"[A] zero-vector failures . {zero_fail}   (must be 0)")
    print(f"[A] membership failures .. {membership_fail}   (p ∣ x−r·y; must be 0)")
    print(f"[B] N(v) ≥ 2p failures ... {bound_fail}   (must be 0)")
    print(f"[D] max reduction steps .. {max_steps}   (O(log p) termination)")
    print()
    print("[C] worst observed N(v)/p vs 2D Hermite ceiling (2/√3)·√d:")
    for d in (1, 2):
        print(f"    d={d}: worst {worst_ratio[d]:.5f}  ceiling {hermite[d]:.5f}"
              f"   at (p,r,v,N)={worst_at[d]}")
    print(f"    d=3 ceiling = {hermite[3]:.5f}  (= 2.0 exactly -> the boundary")
    print("         that forces the `d ≤ 2` hypothesis of the leaf lemma)")
    print()

    ok = (zero_fail == 0 and membership_fail == 0 and bound_fail == 0
          and all(worst_ratio[d] < 2.0 for d in (1, 2)))
    print("RESULT:", "ALL CHECKS PASS" if ok else "FAILURES PRESENT")
    print()
    print("INTERPRETATION")
    print("-" * 72)
    print("  exists_slice_point_lt_two_mul is realized by a DETERMINISTIC,")
    print("  measure-theory-free construction: Lagrange–Gauss reduction of the")
    print("  explicit basis {(p,0),(r,1)} of the index-p sublattice. The Lean")
    print("  proof can therefore induct on the reduction (a strictly decreasing")
    print("  norm well-order) and conclude N(reduced) ≤ (2/√3)·√d·p < 2p for")
    print("  d ∈ {1,2}, instead of porting the 3D Haar-measure Minkowski lemma")
    print("  to 2D. The d=3 ceiling hitting exactly 2.0 is the structural reason")
    print("  the leaf is stated only for d ≤ 2.")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
