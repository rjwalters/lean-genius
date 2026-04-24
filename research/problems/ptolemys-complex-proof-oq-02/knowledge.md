# Knowledge Base: ptolemys-complex-proof-oq-02

## Summary

**Status: COMPLETE** (2026-04-24)

Proved `sin(α+β) = sinα cosβ + cosα sinβ` via Ptolemy's theorem.

File: `proofs/Proofs/PtolemysComplexProofOQ02.lean` (351 lines, 0 sorries, 0 axioms)

---

## Session 2026-04-24 — Complete Proof

### Key Findings

- Quadrilateral `(1, exp(2αi), -1, exp(-2βi))` is Ptolemy's classical choice
- CCW order: angles 0 < 2α < π < 2π-2β < 2π
- Key diagonal: `‖exp(2αI) - exp(-2βI)‖ = 2sin(α+β)` encodes the output
- `nlinarith [sq_nonneg (x-c), sq_nonneg (x+c)]` extracts positive square roots
- `Complex.exp_pi_mul_I` and `Complex.exp_two_pi_mul_I` are the Mathlib APIs
- `rw [Complex.norm_eq_abs, Complex.sq_abs]` converts ‖z‖ to normSq

### Error Fixes Applied

1. Added `import Mathlib.Analysis.SpecialFunctions.Complex.Arg`
2. Fixed `exp_diff_factor` real/imag: `congr 1; ring` approach
3. Fixed `ptolemy_ratio_pos_of_ccw`: `lhs_eq` helper for exponential factoring
4. Fixed `ptolemy_iff_normalized`: removed unused `have key := mul_left_cancel₀`
5. Fixed `ptolemy_equality_for_concyclic`: `obtain ⟨_, hc1, hc2, hc3, hc4⟩`
6. Fixed OQ02: `rw [Complex.norm_eq_abs, Complex.sq_abs]` (4 occurrences)
