# Gauss Sum Squared Identity (elementary-quadratic-reciprocity-oq-01-oq-01-oq-01)

## Problem

Can the Gauss sum squared identity τ² = χ(-1)·p be fully proved in Lean 4,
filling in the key step of the Gauss sum proof of Quadratic Reciprocity?

## Session 2026-05-05 (Session 1) - Proof via gaussSum_sq

**Mode**: FRESH
**Outcome**: completed (0 sorries, 0 axioms)

### What I Did
- Identified problem as fresh (knowledge score 0, no prior work)
- Recognized overlap with `elementary-quadratic-reciprocity-oq-02-oq-01` (OQ02OQ01),
  which already proved this identity in a different parent context
- Adapted the OQ02OQ01 proof technique for the OQ01OQ01 pathway context
- Wrote `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ01OQ01.lean` (185 lines, 7 theorems)
- Created gallery entry `src/data/proofs/elementary-quadratic-reciprocity-oq-01-oq-01-oq-01/`

### Key Findings
- `gaussSum_sq` from `Mathlib.NumberTheory.GaussSum` directly gives τ² = χ(-1)·|ZMod p|
- The standard additive character `ZMod.stdAddChar` is primitive (ZMod.isPrimitive_stdAddChar)
- χ(-1) = (-1)^(p/2) via the first supplementary law (legendreSym.at_neg_one + χ₄_eq_neg_one_pow)
- Sign corollaries: p≡1(4) → τ²=p (Even.neg_one_pow); p≡3(4) → τ²=-p (Odd.neg_one_pow)
- The ℤ version (∃ τ:ℤ, τ²=±p) is mathematically false — ℂ is the correct domain

### Files Modified
- `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ01OQ01.lean` (new)
- `src/data/proofs/elementary-quadratic-reciprocity-oq-01-oq-01-oq-01/meta.json` (new)
- `src/data/proofs/elementary-quadratic-reciprocity-oq-01-oq-01-oq-01/annotations.json` (new)
- `src/data/proofs/elementary-quadratic-reciprocity-oq-01-oq-01-oq-01/index.ts` (new)
- `src/data/research/problems/elementary-quadratic-reciprocity-oq-01-oq-01-oq-01.json` (updated)

### Next Steps
- The natural follow-up is OQ01OQ01OQ02: formalize the Frobenius step τ^q ≡ (p/q)·τ (mod q)
- This requires cyclotomic field machinery (Mathlib.NumberTheory.Cyclotomic)
- GaussSum.frob_gauss_sum or similar Mathlib results may be applicable
