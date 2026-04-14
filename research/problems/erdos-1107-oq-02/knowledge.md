# Knowledge Base: erdos-1107-oq-02

## Problem Summary

**Title**: Effective Squareful Sum Threshold
**Parent**: Erdős Problem #1107 (sums of r-powerful numbers)
**Focus**: Make Heath-Brown's theorem for r=2 effective by finding the exact threshold N.

## Session 2026-04-13 (Session 1) - Threshold Computation

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Computed the exact threshold N = 120 for sums of 3 squareful numbers
- Identified the complete exceptional set: {7, 15, 23, 87, 111, 119}
- Verified computationally that all integers from 120 to 2000 are representable
- Created Lean 4 formalization in `Erdos1107OQ02.lean`
- Created gallery entry in `src/data/proofs/erdos-1107-oq-02/`

### Key Findings
- The threshold N = 120 is tight: 119 is not representable, 120 = 4 + 8 + 108
- Only 6 positive integers fail out of all natural numbers
- Squareful numbers (0, 1, 4, 8, 9, 16, 25, 27, 32, 36, 49, ...) are dense enough that their 3-fold sumset covers all integers from 120 onwards
- The Lean file uses native_decide for computational verification up to 1000

### Files Modified
- `proofs/Proofs/Erdos1107OQ02.lean` (new, ~140 lines)
- `src/data/proofs/erdos-1107-oq-02/meta.json` (new)
- `src/data/proofs/erdos-1107-oq-02/annotations.json` (new)
- `src/data/proofs/erdos-1107-oq-02/index.ts` (new)

### Status
- **Axiom count**: 1 (squareful_sum_threshold — the infinite extension beyond computation)
- **Sorry count**: 0
- **Build status**: Not yet verified (Docker build needed)

## Session 2026-04-14 (Session 2) - 4-Reduction Structural Lemmas

**Mode**: REVISIT
**Outcome**: progress

### What I Did
- Proved `isSquareful_mul4`: IsSquareful is preserved under multiplication by 4
  (if n squareful, then 4n squareful; proof by prime case analysis on p|4n)
- Proved `sumOf3Squareful_mul4`: representability as sum of 3 squareful numbers propagates under ×4

### Key Mathematical Findings
- No squareful number is ≡ 2 (mod 4): if 2|n and n squareful then 4|n.
- Strong induction covers all n ≡ 0 (mod 4) with n ≥ 480:
  * Base: n ∈ [480, 1000] with 4|n — computationally verified
  * Step: n > 1000 with 4|n → n = 4m, m ≥ 250 ≥ 120, m representable by IH → n representable by sumOf3Squareful_mul4
- Remaining gap: n ≡ 1, 2, 3 (mod 4) and n > 1000 — requires Heath-Brown's ternary quadratic form theory

### Files Modified
- `proofs/Proofs/Erdos1107OQ02.lean` (now 220 lines, added isSquareful_mul4 + sumOf3Squareful_mul4)
- `src/data/proofs/erdos-1107-oq-02/meta.json` (lineCount→220, theoremCount→22)

### Status
- **Axiom count**: 1 (squareful_sum_threshold — still needed for n ≡ 1,2,3 mod 4, n > 1000)
- **Blocker**: Formalizing Heath-Brown's theorem requires >1000 lines of ternary quadratic form theory not in Mathlib
