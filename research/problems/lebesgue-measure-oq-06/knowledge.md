# Lebesgue Measure OQ-06: Banach-Tarski Paradox Formalization

## Problem Summary

Formal statement and investigation of the Banach-Tarski paradox in Lean 4. The
abstract framework (equidecomposability, paradoxical sets, amenability) is fully
defined and the core measure-theoretic consequence is fully proved.

**Current state**: `src/data/proofs/lebesgue-measure-oq-06/` gallery entry exists.
Lean file: `proofs/Proofs/LebesgueMeasureOQ06.lean` (295 lines, 5 sorries).

**Remaining sorries** (all axiomatized — full proof requires 800+ lines):
1. `hausdorff_free_subgroup` — free subgroup F₂ ↪ SO(3) [Hausdorff 1914]
2. `banach_tarski` — main paradox for unit ball in ℝ³
3. `banach_tarski_pieces_nonmeasurable` — pieces are non-measurable
4. `free_group_not_amenable` — F₂ is not amenable
5. `int_amenable` — ℤ is amenable via Cesàro mean

## Session 2026-04-22 (Session 1) — Fix paradoxical_no_finite_measure

**Mode**: FRESH
**Outcome**: progress — eliminated 1 sorry

### What I Did

- Proved the sorry in `paradoxical_no_finite_measure` using the monotonicity argument:
  - Split A = (B ∪ C) ∪ (A \ (B ∪ C)) using `Set.union_sdiff_of_subset`
  - Applied `hμ_add` to get `μ(A) = μ(B ∪ C) + μ(A \ (B ∪ C))`
  - Derived `μ(B ∪ C) ≤ μ(A)` (monotonicity from finite additivity)
  - Combined with `μ(A) + μ(A) = μ(B ∪ C)` to get `μ(A) + μ(A) ≤ μ(A)`
  - Used `le_antisymm` with `le_add_right` to conclude `μ(A) + μ(A) = μ(A)`
  - Applied existing `ENNReal.eq_zero_or_top_of_add_eq_self` to finish

### Key Findings

- The `paradoxical_no_finite_measure` sorry was resolvable with pure ENNReal
  monotonicity reasoning — no additional hypotheses needed
- The core insight: `μ(B ∪ C) ≤ μ(A)` follows from B ∪ C ⊆ A and finite
  additivity (splitting A and using non-negativity)
- The 5 remaining sorries represent genuinely hard formalization (all require
  extensive Lean infrastructure beyond the current 295 lines)

### Files Modified

- `proofs/Proofs/LebesgueMeasureOQ06.lean` (288 → 295 lines, 6 → 5 sorries)
- `src/data/proofs/lebesgue-measure-oq-06/meta.json` (sorries 6→5)

### Next Steps

- `free_group_not_amenable`: Provable via explicit partition F₂ = W(a) ∪ a·W(a⁻¹)
  (disjoint) and F₂ = W(b) ∪ b·W(b⁻¹) (disjoint), giving contradiction with
  amenability. Requires FreeGroup.toWord API for word-start definitions. ~150 lines.
- `banach_tarski_pieces_nonmeasurable`: Could use Vitali non-measurable set from
  Mathlib as an alternative if `MeasureTheory.exists_not_measurableSet` exists.
- `hausdorff_free_subgroup`: Requires explicit rotation matrices and number-theoretic
  freeness argument. Estimate 300+ lines.
