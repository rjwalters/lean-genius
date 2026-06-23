# Knowledge Base: leibniz-pi-oq-01-oq-01

**Problem**: Prove Machin formula from arctan addition formula
**Status**: COMPLETED
**Phase**: COMPLETED

## Problem Summary

Derive Machin's formula π/4 = 4·arctan(1/5) - arctan(1/239) step by step from the
arctan addition formula, without using Mathlib's pre-packaged
`four_mul_arctan_inv_5_sub_arctan_inv_239`.

## Session 2026-03-23 (Session 1) - Complete Proof

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Scouted Mathlib for arctan addition API: `Real.arctan_add`, `Real.arctan_neg`, `Real.arctan_one`
- Wrote `MachinFromAddition.lean` with step-by-step derivation
- Three applications of `arctan_add`:
  1. arctan(1/5) + arctan(1/5) = arctan(5/12) [xy = 1/25 < 1]
  2. arctan(5/12) + arctan(5/12) = arctan(120/119) [xy = 25/144 < 1]
  3. arctan(120/119) + arctan(-1/239) = arctan(1) [xy = -120/28441 < 1]
- Docker build passed: 0 sorries, 0 axioms, 79 lines
- Created gallery entry with meta.json, annotations.json, index.ts

### Key Findings
- The numerical coincidence 120*239 - 119 = 119*239 + 120 = 28561 = 169² makes the final step exact
- `norm_num` handles all rational arithmetic automatically
- `arctan_neg` converts subtraction to addition seamlessly
- The technique generalizes to any Machin-like formula

### Files Created
- `proofs/Proofs/MachinFromAddition.lean` - The proof
- `src/data/proofs/leibniz-pi-oq-01-oq-01/` - Gallery entry

### Next Steps
- None - proof is complete
