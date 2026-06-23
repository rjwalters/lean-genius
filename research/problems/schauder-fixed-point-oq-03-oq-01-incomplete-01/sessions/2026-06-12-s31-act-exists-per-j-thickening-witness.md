# S31 ACT — extract `exists_per_j_thickening_witness` helper

**Agent**: researcher-2
**Date**: 2026-06-12
**Phase**: ACT (Lean edit)
**File**: `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`
**Build**: Docker-verified clean (`Proofs.SchauderFixedPointOQ03OQ01`, **3074 jobs**, ✔) at Mathlib pin `2df2f0150c…`.

## What landed

Implements the S31 ACT bound by S30 PREP §3 / §6: extract the per-`j`
thickening-witness helper that isolates the `Classical.choose`-over-finset step
of the two-scale construction.

```lean
private lemma exists_per_j_thickening_witness {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (F : SetValuedMap (↥S) (↥S))
    (i_outer : ↥S)
    (ε : ℝ) (hε : 0 < ε)
    (T : Finset ↥S)
    (hT_in_U : ∀ j ∈ T, F j ⊆ Metric.thickening ε (F i_outer))
    (ysel_in : ↥S → ↥S)
    (hysel_in_F : ∀ j, ysel_in j ∈ F j) :
    ∃ zsel : ↥S → ↥S,
      (∀ j ∈ T, zsel j ∈ F i_outer) ∧
      (∀ j ∈ T, dist (Subtype.val (ysel_in j)) (Subtype.val (zsel j)) < ε)
```

Inserted immediately after `finsupport_nonempty` (line ~1018), alongside the
other finsupport helpers.

## Proof

For each `j ∈ T`: `ysel_in j ∈ F j ⊆ Metric.thickening ε (F i_outer)`, so
`Metric.mem_thickening_iff` yields `z ∈ F i_outer` with subtype-metric
`dist (ysel_in j) z < ε`; `Subtype.dist_eq` converts this to the ambient
`EuclideanSpace` distance `dist (↑(ysel_in j)) (↑z) < ε`. This gives the
pointwise existential `hex : ∀ j ∈ T, ∃ z, …`. The witness function is then
`fun j => if hj : j ∈ T then (hex j hj).choose else j` — the **identity junk
value** off `T` makes the total function `↥S → ↥S` without requiring
`Nonempty ↥S` (relevant because the lemma is stated without `hS_ne`). The two
conjuncts discharge by `dif_pos` + `Exists.choose_spec`.

## Bearers

- `Metric.mem_thickening_iff` (Mathlib, pinned SHA) — `x ∈ thickening δ E ↔ ∃ z ∈ E, dist x z < δ`.
- `Subtype.dist_eq` — subtype metric agrees with the ambient metric on values.
- `Exists.choose` / `Exists.choose_spec`, `dif_pos` — Lean core.

No new imports. `hε` is carried in the signature per the S30 PREP §3
paste-ready contract (the S32 two-scale chain passes it through uniformly),
though the proof itself does not consume it.

## Axiom / sorry delta

- **0 new axioms, 0 new sorries.** File still carries exactly the 2 standing
  axioms (`brouwer_unit_ball`, `approx_selection_exists`). `theoremCount`
  18 → 19; `lineCount` ~1479 → ~1530.

## Next steps (binds S32 ACT)

Assemble the two-scale `approx_selection_exists_proof` body (S30 PREP §2): outer
Lebesgue cover (`exists_lebesgue_subcover_for_uhc`, S29) + inner partition
(`exists_partition_subordinate_to_uhc_cover`, S18d), build `f x` and
`z x = ∑ⱼ ρ j x • zsel j ∈ F (i_outer x)` via
`convex_combination_of_partition_in_S` (S18a) with **this** helper supplying
`zsel`, and bound `dist (f x) (z x) < ε` term-by-term. That discharges
`axiom approx_selection_exists` (→ `approx_selection_exists_proof`), leaving only
`axiom brouwer_unit_ball`. Estimated ~80 LOC body (S30 PREP §3 estimate).
