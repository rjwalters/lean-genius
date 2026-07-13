/-
# Erdős 1215, OQ-02 — monotonicity of the sublevel labyrinth in the level `C`

Companion to `Erdos1215UnitCircleRadius.lean` (radius sandwich, compactness) and
`Erdos1215UnitCircleArea.lean` (planar-area sandwich).  Those files pin the geometry of
the closed sublevel set

    `closedLevelSet P C = {z : ℂ | ‖P.eval z‖ ≤ C}`

for a **fixed** level `C`.  This file records how that region behaves as a function of the
level parameter `C` itself, together with the two canonical points it always contains:

* `closedLevelSet_mono` — the sublevel set is monotone increasing in `C`
  (`C₁ ≤ C₂ ⟹ closedLevelSet P C₁ ⊆ closedLevelSet P C₂`);
* `volume_closedLevelSet_mono` — hence its planar (Lebesgue) measure is monotone in `C`;
* `isRoot_mem_closedLevelSet` — every root of `P` lies in the sublevel set for `C ≥ 0`
  (there `‖P‖ = 0`);
* `zero_mem_closedLevelSet` — the origin lies in the sublevel set for `C ≥ 1`
  (a unit-circle polynomial has `P(0) = 1`, so `‖P(0)‖ = 1`);
* `closedLevelSet_nonempty` — so the sublevel set is nonempty for `C ≥ 1`;
* `levelSet_subset_closedLevelSet` — the open sublevel set `{‖P‖ < C}` of the Mac Lane
  problem sits inside the closed one `{‖P‖ ≤ C}`.

These are the monotone/membership structural facts underneath the fixed-`C` radius and area
sandwiches: as the level `C` rises the labyrinth region only grows, always containing the
roots (its "innermost" points) and, once `C ≥ 1`, the centre `0`.

All results are axiom-free / sorry-free.
-/

import Mathlib
import Proofs.Erdos1215UnitCircleRadius

open Complex Polynomial MeasureTheory

namespace Erdos1215UnitCircleMonotone

open Erdos1215UnitCircleRadius

/-- **The closed sublevel set is monotone increasing in the level `C`.** If `C₁ ≤ C₂` then
`{‖P‖ ≤ C₁} ⊆ {‖P‖ ≤ C₂}`: any `z` with `‖P.eval z‖ ≤ C₁ ≤ C₂` lies in the larger set.
So the Mac Lane labyrinth region only grows as the level rises. -/
theorem closedLevelSet_mono (P : ℂ[X]) {C₁ C₂ : ℝ} (h : C₁ ≤ C₂) :
    closedLevelSet P C₁ ⊆ closedLevelSet P C₂ := by
  intro z hz
  simp only [closedLevelSet, Set.mem_setOf_eq] at hz ⊢
  exact hz.trans h

/-- **The planar measure of the sublevel set is monotone in the level `C`.** Immediate from
`closedLevelSet_mono` and monotonicity of Lebesgue measure — the area of the labyrinth region
is a nondecreasing function of `C`. -/
theorem volume_closedLevelSet_mono (P : ℂ[X]) {C₁ C₂ : ℝ} (h : C₁ ≤ C₂) :
    volume (closedLevelSet P C₁) ≤ volume (closedLevelSet P C₂) :=
  measure_mono (closedLevelSet_mono P h)

/-- **Every root of `P` lies in the sublevel set (for `C ≥ 0`).** At a root `‖P.eval z‖ = 0 ≤ C`.
The roots are the "innermost" points of the labyrinth region — the sublevel set of the smallest
possible level `0` is exactly the root set. -/
theorem isRoot_mem_closedLevelSet {P : ℂ[X]} {z : ℂ} (hz : P.IsRoot z) {C : ℝ} (hC : 0 ≤ C) :
    z ∈ closedLevelSet P C := by
  simp only [closedLevelSet, Set.mem_setOf_eq]
  have hzero : P.eval z = 0 := hz
  rw [hzero, norm_zero]
  exact hC

/-- **The origin lies in the sublevel set (for `C ≥ 1`).** A unit-circle polynomial has
`P(0) = 1`, so `‖P.eval 0‖ = 1 ≤ C`.  The centre is captured as soon as the level reaches `1`. -/
theorem zero_mem_closedLevelSet {P : ℂ[X]} (h : Erdos1215.IsUnitCirclePolynomial P)
    {C : ℝ} (hC : 1 ≤ C) : (0 : ℂ) ∈ closedLevelSet P C := by
  simp only [closedLevelSet, Set.mem_setOf_eq]
  rw [h.1, norm_one]
  exact hC

/-- **The sublevel set is nonempty for `C ≥ 1`.** It contains the origin
(`zero_mem_closedLevelSet`). -/
theorem closedLevelSet_nonempty {P : ℂ[X]} (h : Erdos1215.IsUnitCirclePolynomial P)
    {C : ℝ} (hC : 1 ≤ C) : (closedLevelSet P C).Nonempty :=
  ⟨0, zero_mem_closedLevelSet h hC⟩

/-- **The open sublevel set sits inside the closed one.**  The Mac Lane path problem is stated
for the open region `levelSet P C = {‖P‖ < C}`; it is contained in the closed sublevel set
`{‖P‖ ≤ C}` on which the radius and area sandwiches are proved (`‖P‖ < C ⟹ ‖P‖ ≤ C`).  So every
confinement bound for the closed set restricts to the open one. -/
theorem levelSet_subset_closedLevelSet (P : ℂ[X]) (C : ℝ) :
    Erdos1215.levelSet P C ⊆ closedLevelSet P C := by
  intro z hz
  simp only [Erdos1215.levelSet, closedLevelSet, Set.mem_setOf_eq] at hz ⊢
  exact le_of_lt hz

end Erdos1215UnitCircleMonotone
