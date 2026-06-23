#!/usr/bin/env python3
"""
Numerical verification for the PRIMAL completion of the spherical law of cosines
(SphericalLawOfCosinesOQ03Primal.lean).

The parent file proves  cos c = cos a cos b + <projA, projB>  but never identifies
<projA, projB> with sin a * sin b * cos C, so the textbook headline form is not
closed there. This script confirms the two facts the Lean completion relies on:

  (1) Cauchy-Schwarz precondition for cos_arccos:
        |<projA, projB>| <= ||projA|| * ||projB||           (must be <= 0 as a gap)
  (2) the completion identity:
        cos(angleC) * sin(a) * sin(b) = cos c - cos a cos b
      equivalently  cos c = cos a cos b + sin a sin b cos C.

Conventions (matching the parent SphericalLawOfCosines.lean):
  sideA = arc(B,C),  sideB = arc(A,C),  sideC = arc(A,B)
  projA = projectPerp A C,  projB = projectPerp B C
  ||projA|| = sin(sideB),   ||projB|| = sin(sideA)
  angleC = arccos( <projA,projB> / (||projA|| ||projB||) )
"""
import numpy as np

rng = np.random.default_rng(2024)


def rand_unit():
    v = rng.standard_normal(3)
    return v / np.linalg.norm(v)


def main():
    N = 300_000
    max_identity = 0.0
    max_cs_gap = 0.0          # |<projA,projB>| - ||projA||||projB||, must stay <= 0
    n_degenerate = 0

    for _ in range(N):
        A, B, C = rand_unit(), rand_unit(), rand_unit()
        cos_a = np.dot(B, C)   # cos(sideA), sideA = arc(B,C)
        cos_b = np.dot(A, C)   # cos(sideB), sideB = arc(A,C)
        cos_c = np.dot(A, B)   # cos(sideC), sideC = arc(A,B)

        projA = A - np.dot(A, C) * C
        projB = B - np.dot(B, C) * C
        nA, nB = np.linalg.norm(projA), np.linalg.norm(projB)
        if nA < 1e-9 or nB < 1e-9:
            n_degenerate += 1
            continue

        ip = np.dot(projA, projB)
        max_cs_gap = max(max_cs_gap, abs(ip) - nA * nB)

        q = np.clip(ip / (nA * nB), -1.0, 1.0)
        angleC = np.arccos(q)

        # ||projA|| = sin(sideB), ||projB|| = sin(sideA)
        sin_a = nB
        sin_b = nA
        lhs = np.cos(angleC) * sin_a * sin_b
        rhs = cos_c - cos_a * cos_b
        max_identity = max(max_identity, abs(lhs - rhs))

    print(f"samples (non-degenerate): {N - n_degenerate}, degenerate skipped: {n_degenerate}")
    print(f"(1) max Cauchy-Schwarz gap |<projA,projB>| - ||projA||||projB|| "
          f"(<= 0 required): {max_cs_gap:.3e}")
    print(f"(2) max |cos(angleC) sin a sin b - (cos c - cos a cos b)|: {max_identity:.3e}")

    ok = (max_cs_gap <= 1e-12) and (max_identity <= 1e-10)
    print("RESULT:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
