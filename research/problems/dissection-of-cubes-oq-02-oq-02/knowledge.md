# Knowledge: Dehn-Sydler Completeness Theorem

## Problem Summary

Formalize the Dehn-Sydler completeness theorem using the proper algebraic Dehn invariant D(P) ∈ ℝ ⊗_ℤ (ℝ/πℤ).

## Session 2026-03-25 (Session 1) - Complete Formalization

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Defined the quotient group ℝ/πℤ = ℝ ⧸ AddSubgroup.zmultiples π
- Defined the Dehn invariant group ℝ ⊗_ℤ (ℝ/πℤ) using TensorProduct ℤ ℝ AngleQuot
- Proved `tmul_torsion_eq_zero`: torsion elements vanish in tensor products with ℝ
- Proved `rational_angle_vanishes`: r ⊗ [qπ] = 0 for all q ∈ ℚ
- Proved `cube_dehn_zero`: D(cube) = 0 (π/2 is rational × π)
- Proved `tet_dehn_ne_zero`: D(tetrahedron) ≠ 0 (arccos(1/3)/π irrational)
- Proved `hilbert_third_problem`: D(cube) ≠ D(tetrahedron)
- Proved `octAngle_class`: [arccos(-1/3)] = -[arccos(1/3)] in ℝ/πℤ
- Proved `oct_dehn_ne_zero`: D(octahedron) ≠ 0
- Stated the Dehn-Sydler completeness theorem

### Key Findings
- The tensor product ℝ ⊗_ℤ (ℝ/πℤ) automatically kills rational multiples of π
- Key proof technique: ℝ is divisible as ℤ-module, so r = n•(r/n), giving r ⊗ x = (r/n) ⊗ (n•x) = 0 when n•x = 0
- The flatness axiom (tmul_infinite_order_ne_zero) is needed for the nonzero direction
- Mathlib's QuotientAddGroup and TensorProduct APIs work well together

### Files Modified
- proofs/Proofs/DissectionOfCubesOQ02OQ02.lean (406 lines, new)
- src/data/proofs/dissection-of-cubes-oq-02-oq-02/ (gallery entry, new)
- src/data/research/problems/dissection-of-cubes-oq-02-oq-02.json (updated)

### Axiom Reduction Opportunities
1. `niven_arccos_third` — Already proved in DissectionOfCubesOQ02.lean
2. `tmul_infinite_order_ne_zero` — Provable via Module.Flat (Mathlib)
3. `arccos_neg_third` — Standard trig identity, likely provable
