# Research State: fundamental-theorem-calculus-oq-01-incomplete-01

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-05-28 (researcher-1)
**Iteration**: 2

## Current Focus
De-axiomatizing the parent proof `FundamentalTheoremCalculusLebesgue.lean`.
Surveyed Mathlib's BV / Vitali / Stieltjes infrastructure and mapped the
concrete proof path for the two axioms and the Cantor `sorry` (see knowledge.md).

## Active Approach
Bottom-up: discharge `lebesgue_ftc_differentiable` via the chain
`AC ⟹ LocallyBoundedVariationOn ⟹ a.e. differentiable`. The linchpin is the
elementary lemma **AC ⟹ LocallyBoundedVariationOn** (partition into pieces of
length `< δ`; each contributes variation `< 1`).

## Completed This Iteration
- Added `ac_implies_continuousOn` (AC ⟹ `ContinuousOn`) — verified.
- Added `ac_on_subinterval` (AC localizes to subintervals) — verified.
- Mathlib infrastructure assessment + full de-axiomatization roadmap recorded.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- Mathlib source is not on the host filesystem (self-referential `proofs/.lake`
  symlink; Mathlib lives only in the Docker build volume). Exact API names for
  `eVariationOn` / BV decomposition must be confirmed via a Docker build before
  the AC⟹BV lemma can be committed.

## Next Action
Formalize **AC ⟹ LocallyBoundedVariationOn** (or `BoundedVariationOn F (Icc a b)`):
1. Confirm Mathlib names: `eVariationOn`, its iSup characterization,
   `eVariationOn.Icc_add_Icc`-style additivity, `BoundedVariationOn`,
   `LocallyBoundedVariationOn`, and the BV a.e.-differentiability lemma.
2. Prove the per-piece bound `eVariationOn F (Icc c d) ≤ 1` for `d - c < δ`.
3. Sum over a finite partition to bound `eVariationOn F (Icc a b)`.
4. Chain to a.e. differentiability and replace `lebesgue_ftc_differentiable`.
