import Mathlib
import Proofs.BaireCategoryTheoremOQ01

/-!
# The Uniform Boundedness Principle from Baire's theorem

This file derives the **Banach–Steinhaus theorem** (the *Uniform Boundedness Principle*)
directly from the gallery Baire category theorem
(`BaireCategoryTheoremOQ01.baire_nonempty_interior`), rather than invoking Mathlib's
packaged `banach_steinhaus`.

The statement: if `g : ι → E →L[𝕜] F` is a family of bounded linear operators from a
**Banach** space `E` into a normed space `F` that is *pointwise bounded*
(`∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C`), then the operator norms are *uniformly bounded*
(`∃ C', ∀ i, ‖g i‖ ≤ C'`).

## The classical Baire argument

This is the textbook proof, and it is genuinely distinct from current Mathlib, whose
`banach_steinhaus` is deduced from the barrelled-space / equicontinuity framework
(`WithSeminorms.banach_steinhaus`). Here we run the original closed-set exhaustion:

* For each `n : ℕ` form the closed "sublevel" set `e n = ⋂ i, {x | ‖g i x‖ ≤ n}`.
* Pointwise boundedness makes `⋃ n, e n` the whole space.
* The **gallery Baire theorem** (category form) hands us an `m` with `interior (e m) ≠ ∅`,
  i.e. a ball `ball x ε` on which *every* `g i` is bounded by `m`.
* A translation-and-scaling (shell) estimate turns this local bound into the uniform
  operator-norm bound `‖g i‖ ≤ 2m / (ε/‖c‖)`.

## Main results

* `uniform_boundedness` — the Uniform Boundedness Principle.
* `uniform_boundedness_with_const` — the same with an explicit `‖g i x‖ ≤ C' * ‖x‖`
  equicontinuity-style bound.
* `exists_resonance_of_not_uniformly_bounded` — the contrapositive **resonance**
  statement: a family with unbounded operator norms must have a point of resonance,
  a single `x` at which `sup_i ‖g i x‖ = ∞`.

All results are fully machine-checked, no `sorry`, no extra axioms.
-/

namespace BaireCategoryTheoremOQ01OQ01

open Set Metric BaireCategoryTheoremOQ01

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Uniform Boundedness Principle (Banach–Steinhaus).** A pointwise-bounded family of
bounded linear operators from a Banach space into a normed space is uniformly bounded in
operator norm. Proved from the gallery Baire category theorem. -/
theorem uniform_boundedness {ι : Type*} {g : ι → E →L[𝕜] F}
    (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) : ∃ C', ∀ i, ‖g i‖ ≤ C' := by
  haveI : Nonempty E := ⟨0⟩
  -- The closed sublevel sets `e n = ⋂ i, {x | ‖g i x‖ ≤ n}`.
  set e : ℕ → Set E := fun n => ⋂ i : ι, {x : E | ‖g i x‖ ≤ n} with he
  have hc : ∀ n : ℕ, IsClosed (e n) := fun n =>
    isClosed_iInter fun i => isClosed_le (g i).cont.norm continuous_const
  -- Pointwise boundedness exhausts the whole space.
  have hU : (⋃ n : ℕ, e n) = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨C, hC⟩ := h x
    obtain ⟨m, hm⟩ := exists_nat_ge C
    exact mem_iUnion.2 ⟨m, mem_iInter.2 fun i => (hC i).trans hm⟩
  -- Baire: some `e m` has nonempty interior, hence contains a ball.
  obtain ⟨m, hmne⟩ := baire_nonempty_interior hc hU
  obtain ⟨x, hx⟩ := hmne
  obtain ⟨ε, ε_pos, hε⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  obtain ⟨c, hc1⟩ := NormedField.exists_one_lt_norm 𝕜
  have hcpos : (0 : ℝ) < ‖c‖ := zero_lt_one.trans hc1
  have εc_pos : 0 < ε / ‖c‖ := div_pos ε_pos hcpos
  -- Every operator is bounded by `m` on the ball.
  have ball_le : ∀ z ∈ ball x ε, ∀ i, ‖g i z‖ ≤ (m : ℝ) := by
    intro z hz i
    have hzm : z ∈ e m := interior_subset (hε hz)
    exact mem_iInter.1 hzm i
  -- The uniform constant.
  refine ⟨(m + m : ℝ) / (ε / ‖c‖), fun i => ?_⟩
  refine ContinuousLinearMap.opNorm_le_of_shell ε_pos ?_ hc1 ?_
  · exact div_nonneg (by positivity) εc_pos.le
  · intro y le_y y_lt
    -- `y` and `y + x` both lie in the ball, so `g i y = g i (y+x) - g i x` is small.
    have hyx : y + x ∈ ball x ε := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_right]; exact y_lt
    have hx0 : x ∈ ball x ε := mem_ball_self ε_pos
    have hmap : g i y = g i (y + x) - g i x := by rw [map_add]; abel
    have key : ‖g i y‖ ≤ (m + m : ℝ) := by
      rw [hmap]
      calc ‖g i (y + x) - g i x‖
          ≤ ‖g i (y + x)‖ + ‖g i x‖ := norm_sub_le _ _
        _ ≤ (m : ℝ) + m := add_le_add (ball_le _ hyx i) (ball_le _ hx0 i)
    -- The shell hypothesis `ε/‖c‖ ≤ ‖y‖` upgrades the flat bound to a proportional one.
    have step : (m + m : ℝ) ≤ (m + m : ℝ) / (ε / ‖c‖) * ‖y‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ εc_pos]
      exact mul_le_mul_of_nonneg_left le_y (by positivity)
    exact key.trans step

/-- The Uniform Boundedness Principle in *equicontinuity* form: there is a single constant
`C'` with `‖g i x‖ ≤ C' * ‖x‖` for every operator `i` and every point `x`. -/
theorem uniform_boundedness_with_const {ι : Type*} {g : ι → E →L[𝕜] F}
    (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) : ∃ C', 0 ≤ C' ∧ ∀ i, ∀ x, ‖g i x‖ ≤ C' * ‖x‖ := by
  obtain ⟨C', hC'⟩ := uniform_boundedness h
  refine ⟨max C' 0, le_max_right _ _, fun i x => ?_⟩
  calc ‖g i x‖ ≤ ‖g i‖ * ‖x‖ := (g i).le_opNorm x
    _ ≤ max C' 0 * ‖x‖ :=
        mul_le_mul_of_nonneg_right ((hC' i).trans (le_max_left _ _)) (norm_nonneg _)

/-- **Resonance (contrapositive of Banach–Steinhaus).** If the operator norms of a family
are *not* uniformly bounded, then the family cannot be pointwise bounded: there exists a
single point `x` of resonance at which `sup_i ‖g i x‖` is infinite (no finite `C` bounds
`‖g i x‖` over all `i`). -/
theorem exists_resonance_of_not_uniformly_bounded {ι : Type*} {g : ι → E →L[𝕜] F}
    (h : ¬ ∃ C', ∀ i, ‖g i‖ ≤ C') : ∃ x, ¬ ∃ C, ∀ i, ‖g i x‖ ≤ C := by
  by_contra hcon
  push_neg at hcon
  exact h (uniform_boundedness hcon)

end BaireCategoryTheoremOQ01OQ01
