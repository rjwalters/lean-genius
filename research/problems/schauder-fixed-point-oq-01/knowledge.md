# Schauder Projection Lemma (OQ-01) - Knowledge

## Problem Summary
Prove the Schauder projection lemma from first principles: given a compact set K in a normed space and ε > 0, construct a continuous map π from K into a finite-dimensional convex hull with ‖π(x) - x‖ < ε.

## Status: COMPLETED

## Session 2026-03-06 (Session 1) - Proof Completion

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Found existing proof file (363 lines, 17 theorems, 0 sorries, 0 axioms)
- Fixed Mathlib 4.26 API compatibility issues:
  - `Submodule.isClosed_of_finiteDimensional` → `Set.Finite.isClosed_convexHull`
  - `IsCompact.convexHull` → `Set.Finite.isCompact_convexHull` (from `Mathlib.Analysis.Convex.Topology`)
  - `Real.norm_of_nonneg` → `Real.norm_eq_abs` + `abs_of_nonneg`
  - `elim_finite_subcover_image` returns `Set E` with `Finite`, not `Finset E`
  - Added `classical` for `DecidableEq` on finite subtype
  - Fixed bump function case analysis: when bumpFn = 0, use `simp [h]` not `le_of_lt`
  - Fixed calc chain: `S * ε` not `ε * S`, with `rw [hS_def, bumpSum]` to close

### Key Findings
- `Set.Finite.isCompact_convexHull` and `Set.Finite.isClosed_convexHull` are in `Mathlib.Analysis.Convex.Topology`
- `Real.norm_of_nonneg` doesn't exist in Mathlib 4.26; use `Real.norm_eq_abs` + `abs_of_nonneg`
- When using `set S := expr`, `rw` may leave goals like `expr = S` that need `rw [hS_def, ...]` to close
- `elim_finite_subcover_image` returns `Set E` with `Set.Finite` proof; use `.fintype` for Fintype instance

### Files Modified
- `proofs/Proofs/SchauderFixedPointOQ01.lean` - 315 lines, 17 theorems, 0 sorries, 0 axioms
- `src/data/proofs/schauder-fixed-point-oq-01/` - Gallery integration (meta.json, annotations.json, index.ts)
- `src/data/proofs/schauder-fixed-point/meta.json` - Updated parent: sorries 1→0, resolved OQ-01
