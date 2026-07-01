/-
# Shapley-Folkman Refined: Excess Bounded by the Number of Non-Convex Summands (OQ04)

The base `shapley_folkman` lemma bounds the number of "excess" summands (those
requiring convexification, i.e. `xᵢ ∈ conv(Sᵢ) \ Sᵢ`) by the dimension `d` of
the ambient space. This is dimension-driven and completely ignores *how many* of
the summands were already convex.

This file proves the sharper **structural** bound

    excess ≤ min(d, #{i : Sᵢ is not convex}).

The mechanism is elementary but sharp: a convex summand `Sᵢ` satisfies
`conv(Sᵢ) = Sᵢ`, so *every* point of `conv(Sᵢ)` already lies in `Sᵢ` and such an
index can never be an excess index. Hence the excess set is always contained in
the set of non-convex indices — a fact that requires **no** finite-dimensionality
at all. Intersecting with the dimension bound yields the `min`.

## Main Results

1. `excessIndices_subset_nonConvex` — for ANY decomposition, the excess indices
   are a subset of the non-convex indices (holds in any real vector space).
2. `excess_card_le_nonConvex` — pure combinatorial corollary: excess count is at
   most the number of non-convex summands, with **no dimension hypothesis**.
3. `shapley_folkman_refined` — the headline `min(d, #nonConvex)` bound.
4. `sum_close_refined` — the `sum_close_to_convexHull` corollary, sharpened.
5. `convex_summands_hull_eq` — recovers the classical fact "the Minkowski sum of
   convex sets is convex" as the excess = 0 special case (all summands convex).
6. `shapley_folkman_starr_refined` — Starr's distance bound `dist ≤ (…)·δ`, with
   the dimension factor replaced by `min(d, #nonConvex)`.

## Why this is a genuine refinement

If a large economy has `n` agents but only `k` of them have non-convex feasible
sets, the aggregate is within `min(d, k)` — NOT `d` — of being exactly convex,
uniformly in `n`. When every agent is convex (`k = 0`) the aggregate is *exactly*
convex: there is no approximation error at all.
-/

import Mathlib
import Proofs.ShapleyFolkman

set_option linter.unusedVariables false

namespace ShapleyFolkmanOQ04

open Set Finset Pointwise ShapleyFolkman

-- Matches the base file: Classical decidability lets `Finset.filter` range over
-- arbitrary `Set`/`Convex` predicates without threading `DecidablePred` instances.
attribute [local instance] Classical.propDecidable

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

-- ============================================================
-- SECTION I: Non-convex indices and the subset lemma
-- ============================================================

/-- The indices whose summand set is **not** convex. Convex summands never
    contribute excess, so this set governs the refined bound. -/
noncomputable def nonConvexIndices {ι : Type*} (S : ι → Set E) (t : Finset ι) : Finset ι :=
  t.filter (fun i => ¬ Convex ℝ (S i))

/-- For a convex set `S`, every point of its convex hull already lies in `S`
    (`conv(S) = S`). This is the pointwise reason convex summands are "free". -/
lemma mem_of_convex {S : Set E} (hS : Convex ℝ S) {x : E}
    (hx : x ∈ convexHull ℝ S) : x ∈ S := by
  rwa [hS.convexHull_eq] at hx

/-- **Core structural lemma.** For *any* decomposition of `x`, every excess index
    is a non-convex index. Equivalently: if `Sᵢ` is convex then `i` is not an
    excess index. This holds in an arbitrary real vector space — no
    finite-dimensionality is used. -/
theorem excessIndices_subset_nonConvex {ι : Type*} [DecidableEq ι]
    {S : ι → Set E} {t : Finset ι} {x : E} (D : Decomposition S t x) :
    D.excessIndices ⊆ nonConvexIndices S t := by
  intro i hi
  -- `i ∈ excessIndices` unpacks to `i ∈ t` and `D.point i ∉ S i`.
  simp only [Decomposition.excessIndices, Finset.mem_filter] at hi
  obtain ⟨hit, hnot⟩ := hi
  -- The chosen point lies in `conv(Sᵢ)` because `i ∈ t`.
  have hmem : D.point i ∈ convexHull ℝ (S i) := D.mem_convexHull i hit
  -- If `Sᵢ` were convex, `D.point i` would land in `Sᵢ`, contradicting `hnot`.
  simp only [nonConvexIndices, Finset.mem_filter]
  refine ⟨hit, fun hconv => hnot (mem_of_convex hconv hmem)⟩

/-- **Dimension-free counting corollary.** The number of excess summands never
    exceeds the number of non-convex summands, in any real vector space. -/
theorem excess_card_le_nonConvex {ι : Type*} [DecidableEq ι]
    {S : ι → Set E} {t : Finset ι} {x : E} (D : Decomposition S t x) :
    D.excessIndices.card ≤ (nonConvexIndices S t).card :=
  Finset.card_le_card (excessIndices_subset_nonConvex D)

/-- Filter-level form of the subset lemma: for any family `f` with
    `f i ∈ conv(Sᵢ)`, the indices where `f i ∉ Sᵢ` are all non-convex indices.
    This avoids repackaging into a `Decomposition`. -/
theorem excessFilter_subset_nonConvex {ι : Type*} {S : ι → Set E} {t : Finset ι}
    {f : ι → E} (hf_mem : ∀ i ∈ t, f i ∈ convexHull ℝ (S i)) :
    t.filter (fun i => f i ∉ S i) ⊆ nonConvexIndices S t := by
  intro i hi
  simp only [Finset.mem_filter] at hi
  obtain ⟨hit, hnot⟩ := hi
  simp only [nonConvexIndices, Finset.mem_filter]
  exact ⟨hit, fun hconv => hnot (mem_of_convex hconv (hf_mem i hit))⟩

-- ============================================================
-- SECTION II: The refined Shapley-Folkman bound
-- ============================================================

/-- **Refined Shapley-Folkman Lemma.** Any point of `∑ conv(Sᵢ)` admits a
    decomposition whose excess count is bounded by `min(d, #nonConvex)`, where
    `d = dim E` and `#nonConvex` counts the non-convex summands.

    This strictly sharpens `shapley_folkman`: the excess is controlled by the
    *smaller* of the dimension and the number of genuinely non-convex sets. -/
theorem shapley_folkman_refined [FiniteDimensional ℝ E]
    {ι : Type*} [DecidableEq ι] {S : ι → Set E} {t : Finset ι}
    (hne : ∀ i ∈ t, (S i).Nonempty)
    {x : E} (hx : ∃ (f : ι → E), (∀ i ∈ t, f i ∈ convexHull ℝ (S i)) ∧
      (∀ i, i ∉ t → f i = 0) ∧ ∑ i ∈ t, f i = x) :
    ∃ (d : Decomposition S t x),
      d.excessIndices.card ≤ min (Module.finrank ℝ E) (nonConvexIndices S t).card := by
  obtain ⟨D, hD⟩ := shapley_folkman hne hx
  exact ⟨D, le_min hD (excess_card_le_nonConvex D)⟩

/-- **Refined "sum close to convex hull" corollary.** For a point in
    `conv(∑ Sᵢ)`, the summand decomposition needs convexification on at most
    `min(d, #nonConvex)` indices. -/
theorem sum_close_refined [FiniteDimensional ℝ E]
    {ι : Type*} [DecidableEq ι] {S : ι → Set E} {t : Finset ι}
    (hne : ∀ i ∈ t, (S i).Nonempty)
    {x : E} (hx : x ∈ convexHull ℝ (∑ i ∈ t, S i)) :
    ∃ (f : ι → E),
      (∀ i ∈ t, f i ∈ convexHull ℝ (S i)) ∧
      ∑ i ∈ t, f i = x ∧
      (t.filter (fun i => f i ∉ S i)).card
        ≤ min (Module.finrank ℝ E) (nonConvexIndices S t).card := by
  -- Base corollary gives the dimension bound; the filter-level subset lemma
  -- gives the non-convex bound. Take the minimum.
  obtain ⟨f, hf_mem, hf_sum, hf_excess⟩ := sum_close_to_convexHull hne hx
  exact ⟨f, hf_mem, hf_sum,
    le_min hf_excess (Finset.card_le_card (excessFilter_subset_nonConvex hf_mem))⟩

-- ============================================================
-- SECTION III: All-convex special case (classical Minkowski fact)
-- ============================================================

/-- When **every** summand is convex there are no non-convex indices. -/
lemma nonConvexIndices_eq_empty {ι : Type*} {S : ι → Set E} {t : Finset ι}
    (hconv : ∀ i ∈ t, Convex ℝ (S i)) :
    nonConvexIndices S t = ∅ := by
  simp only [nonConvexIndices]
  rw [Finset.filter_eq_empty_iff]
  intro i hi; simpa using hconv i hi

/-- **Minkowski sum of convex sets is convex — recovered as the excess = 0 case.**
    If all summands are convex, then `conv(∑ Sᵢ) = ∑ Sᵢ`: every point of the
    convex hull of the Minkowski sum already lies in the sum, with no
    convexification needed. -/
theorem convex_summands_hull_eq [FiniteDimensional ℝ E]
    {ι : Type*} [DecidableEq ι] {S : ι → Set E} {t : Finset ι}
    (hne : ∀ i ∈ t, (S i).Nonempty)
    (hconv : ∀ i ∈ t, Convex ℝ (S i))
    {x : E} (hx : x ∈ convexHull ℝ (∑ i ∈ t, S i)) :
    x ∈ ∑ i ∈ t, S i := by
  -- Refined corollary: excess ≤ #nonConvex = 0, so the decomposition sits in ∑ Sᵢ.
  obtain ⟨f, hf_mem, hf_sum, hf_excess⟩ := sum_close_refined hne hx
  -- `#nonConvex = 0`, so the excess filter is empty and every `f i ∈ S i`.
  have hcard0 : (t.filter (fun i => f i ∉ S i)).card = 0 := by
    rw [nonConvexIndices_eq_empty hconv, Finset.card_empty, Nat.min_zero,
      Nat.le_zero] at hf_excess
    exact hf_excess
  have hmem : ∀ i ∈ t, f i ∈ S i := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hcard0
    intro i hi; exact not_not.mp (hcard0 hi)
  rw [Set.mem_finset_sum]
  refine ⟨f, ?_, hf_sum⟩
  intro i hi
  exact hmem i hi

-- ============================================================
-- SECTION IV: Refined Starr distance bound (normed setting)
-- ============================================================

section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If `p ∈ conv(S)`, `q ∈ S`, and `S` has diameter `≤ δ`, then `dist p q ≤ δ`.
    (Local copy of the OQ03 distance lemma so this file stays self-contained.) -/
private lemma convexHull_dist_le_diam {S : Set F} {p q : F} {δ : ℝ}
    (hq : q ∈ S) (hdiam : ∀ s₁ ∈ S, ∀ s₂ ∈ S, dist s₁ s₂ ≤ δ)
    (hp : p ∈ convexHull ℝ S) : dist p q ≤ δ := by
  have hS_sub : S ⊆ Metric.closedBall q δ := fun s hs =>
    Metric.mem_closedBall.mpr (hdiam s hs q hq)
  have hsub := convexHull_min hS_sub (convex_closedBall q δ)
  exact Metric.mem_closedBall.mp (hsub hp)

/-- **Refined Shapley-Folkman-Starr Theorem.** Any point in `conv(∑ Sᵢ)` is
    within distance `min(d, #nonConvex) · δ` of the actual Minkowski sum, where
    `δ` bounds each summand's diameter. This sharpens `shapley_folkman_starr`
    (OQ03): the number of *non-convex* agents, not the ambient dimension, caps
    the aggregate non-convexity when the former is smaller. -/
theorem shapley_folkman_starr_refined [FiniteDimensional ℝ F]
    {ι : Type*} [DecidableEq ι] {S : ι → Set F} {t : Finset ι}
    (hne : ∀ i ∈ t, (S i).Nonempty)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hdiam : ∀ i ∈ t, ∀ s₁ ∈ S i, ∀ s₂ ∈ S i, dist s₁ s₂ ≤ δ)
    {x : F} (hx : x ∈ convexHull ℝ (∑ i ∈ t, S i)) :
    ∃ x' ∈ ∑ i ∈ t, S i,
      dist x x' ≤ (min (Module.finrank ℝ F) (nonConvexIndices S t).card : ℝ) * δ := by
  classical
  -- Refined decomposition: excess set `J` has card ≤ min(d, #nonConvex).
  obtain ⟨f, hf_mem, hf_sum, hf_excess⟩ := sum_close_refined hne hx
  set J := t.filter (fun i => f i ∉ S i) with hJ
  have hJ_sub : J ⊆ t := Finset.filter_subset _ _
  -- Replace each excess summand by a genuine point of its set.
  let g : ι → F := fun i => if h : i ∈ J then (hne i (hJ_sub h)).choose else f i
  have hg_J : ∀ j ∈ J, g j ∈ S j := fun j hj => by
    simp only [g, dif_pos hj]; exact (hne j (hJ_sub hj)).choose_spec
  have hg_notJ : ∀ i ∈ t, i ∉ J → g i ∈ S i := fun i hi hiJ => by
    simp only [g, dif_neg hiJ]
    simp only [hJ, Finset.mem_filter, hi, true_and, not_not] at hiJ
    exact hiJ
  have hx'_mem : ∑ i ∈ t, g i ∈ ∑ i ∈ t, S i := by
    rw [Set.mem_finset_sum]
    refine ⟨g, ?_, rfl⟩
    intro i hi
    by_cases hiJ : i ∈ J
    · exact hg_J i hiJ
    · exact hg_notJ i hi hiJ
  refine ⟨∑ i ∈ t, g i, hx'_mem, ?_⟩
  rw [← hf_sum]
  calc dist (∑ i ∈ t, f i) (∑ i ∈ t, g i)
      = ‖∑ i ∈ t, f i - ∑ i ∈ t, g i‖ := dist_eq_norm _ _
    _ = ‖∑ i ∈ t, (f i - g i)‖ := by rw [← Finset.sum_sub_distrib]
    _ = ‖∑ i ∈ J, (f i - g i)‖ := by
        congr 1; symm
        apply Finset.sum_subset hJ_sub
        intro i hi hiJ; simp only [g, dif_neg hiJ, sub_self]
    _ ≤ ∑ i ∈ J, ‖f i - g i‖ := norm_sum_le J _
    _ ≤ ∑ i ∈ J, δ := by
        apply Finset.sum_le_sum
        intro j hj
        rw [← dist_eq_norm]
        exact convexHull_dist_le_diam (hg_J j hj) (hdiam j (hJ_sub hj))
          (hf_mem j (hJ_sub hj))
    _ = J.card * δ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (min (Module.finrank ℝ F) (nonConvexIndices S t).card : ℝ) * δ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hf_excess) hδ

end Normed

end ShapleyFolkmanOQ04
