# Unified Curvature-Parametrized Law of Cosines

## Source
- **Proof**: law-of-cosines-oq-01 (`Spherical Law of Cosines`)
- **Category**: unification/generalization
- **Tractability**: tractable (7/10)

## Problem Description

Unify the Euclidean, spherical, and hyperbolic laws of cosines into a single curvature-parametrized formula:

  cs_K(c) = cs_K(a)·cs_K(b) + K·sn_K(a)·sn_K(b)·cos(C)

where K ∈ ℝ is the sectional curvature and:
- cs_K(r) = cos(√K·r) for K>0, cosh(√(-K)·r) for K<0, 1 for K=0
- sn_K(r) = sin(√K·r)/√K for K>0, sinh(√(-K)·r)/√(-K) for K<0, r for K=0

## Tags
geometry, trigonometry, spherical-geometry, hyperbolic-geometry, curvature, unification

## Related Gallery Proofs
- [Law of Cosines](../../../src/data/proofs/law-of-cosines/) — Euclidean case (K=0 limit)
- [Spherical Law of Cosines](../../../src/data/proofs/law-of-cosines-oq-01/) — K=1 special case
- [Hyperbolic Law of Cosines](../../../src/data/proofs/law-of-cosines-oq-03/) — K=-1 special case

## Status
COMPLETED (1 sorry remaining). Proof exists at proofs/Proofs/LawOfCosinesOQ05.lean (~270 lines, 0 axioms, 1 sorry: euclidean_limit_holds).
Gallery entry created at src/data/proofs/law-of-cosines-oq-01-oq-05/.

## Key Results Proved
- curvaturePythagorean: cs_K(r)² + K·sn_K(r)² = 1 (all K, 0 sorries)
- Recovery theorems: K=±1 give classical spherical/hyperbolic laws
- Algebraic equivalences: K>0 ↔ spherical at scaled sides; K<0 ↔ hyperbolic at scaled sides

## Open
- euclidean_limit_holds: K→0 Taylor expansion (requires Mathlib real analysis)
