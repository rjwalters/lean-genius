# S27 ACT — output-side graph-bound reduced to selected-value clustering

**Slug:** `schauder-fixed-point-oq-03-oq-01-incomplete-01`
**Researcher:** researcher-1
**Date:** 2026-05-28
**Phase:** ACT (0 functional sorries, 2 axioms unchanged)
**Iteration:** 30 (JSON `currentState.iteration: 29 → 30`, `attemptCounts.total: 29 → 30`)
**PR:** #20891 (continuation of the S26 branch `research/schauder-fp-s26-input-ball`)
**Predecessor:** S26 ACT (researcher-1, 2026-05-28) — input-ball clause propagation + `finsupport_center_within_input_ball` + `finsupport_nonempty`

---

## §1 What landed

One new private lemma in `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean:996`:

```lean
private lemma finsupport_combination_within_output_ball {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (ρ : PartitionOfUnity (↥S) (↥S) (Set.univ : Set ↥S))
    (x i : ↥S)
    (ysel : ↥S → EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hr : ∀ j ∈ ρ.finsupport x, dist (ysel j) (ysel i) ≤ r) :
    dist (∑ j ∈ ρ.finsupport x, ρ j x • ysel j) (ysel i) ≤ r
```

Proof is 4 LOC: `convex_closedBall (ysel i) r` is convex and (by `hr` +
`Metric.mem_closedBall`) contains every `ysel j` for `j ∈ ρ.finsupport x`,
so `convex_combination_of_partition_in_S` (S18a) puts the partition-weighted
sum in the ball, and `Metric.mem_closedBall.mp` extracts the distance bound.

Build-verified clean: `[3074/3074] Built (7.2s)` at pinned Mathlib SHA
`2df2f0150c`. No new imports — `convex_closedBall` / `Metric.mem_closedBall`
are reachable through the existing `InnerProductSpace.Projection` chain.
`lineCount 1369 → 1419`, `theoremCount 16 → 17`, axioms 2 (unchanged).

## §2 Why this matters — a simpler endgame than the S26 nextStep plan

The S26 nextStep for S27 routed the output conjunct
`dist (f x) (ysel i) < ε` through `Metric.thickening ε (F i)` plus the S22
nearest-point helper `exists_nearest_in_image_F`. This lemma shows that is
**unnecessary**:

- `IsGraphApproxSelection F f ε` (file line 532) needs
  `∃ x' y, dist x x' < ε ∧ y ∈ F x' ∧ dist (f x) y < ε`.
- Take `x' := i ∈ ρ.finsupport x` (exists by `finsupport_nonempty`),
  `y := ysel i`. Then `y ∈ F i` holds because `ysel` is a selection
  (`hysel_in_F`), and `dist x x' < ε` is S26's
  `finsupport_center_within_input_ball`.
- The third conjunct `dist (f x) (ysel i) < ε` now follows from this lemma
  **with no projection**, provided the selected values cluster:
  `∀ j ∈ ρ.finsupport x, dist (ysel j) (ysel i) < ε`.

So the entire output-side difficulty is now isolated in one statement about
the centers' selected values. The convex-combination obstacle is closed.

## §3 Sole remaining obstacle (S28 / next iteration)

Prove the **clustering**: for a common chosen `i`,
`∀ j ∈ ρ.finsupport x, dist (ysel j) (ysel i) < ε`.

This is where the genuine content lives and where the existing cover is too
weak: a single `U i` thickening controls `F x`, not the values `ysel j ∈ F j`
picked at the *other* centers `j`. The standard fix is a uniform /
Lebesgue-number refinement of the S18c cover so that all centers `x_j` with
`ρ j x > 0` share one neighborhood on which `F` is `ε`-thickening-controlled,
run at a calibrated `ε' := ε/2` (or `ε/3`). Once clustering holds, feed it to
`finsupport_combination_within_output_ball` (lean:996), then S28 packages
`theorem approx_selection_exists_proof` to replace `axiom
approx_selection_exists` and sync `axiomCount 2 → 1`.

## §4 Housekeeping note

Pre-existing deprecation warning (not introduced here): line 45
`import Mathlib.Analysis.InnerProductSpace.Projection` is deprecated in favor
of the split `Projection.{Basic,FiniteDimensional,Minimal,Reflection,Submodule}`
modules. Left untouched — out of scope for this research increment and would
churn imports on a build-clean file. Worth a separate mechanic pass.
