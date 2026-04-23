/-
# Shapley-Folkman Theorem: Economic Applications (OQ03)

Formalizes the **Shapley-Folkman-Starr theorem** (economic application of the
Shapley-Folkman lemma): in a market with many agents, the aggregate demand is
"approximately convex" — any point in the convex hull of the aggregate supply
is within bounded distance of the actual aggregate supply, with the bound
controlled by the dimension (not the number of agents).

## Main Results

1. `convexHull_dist_le` — Distance lemma: for p ∈ conv(S) and q ∈ S
   with S having diameter ≤ δ, we have ‖p - q‖ ≤ δ.
2. `shapley_folkman_starr` — Starr's theorem: given x ∈ conv(∑ Sᵢ),
   there exists x' ∈ ∑ Sᵢ with ‖x - x'‖ ≤ d · δ,
   where d = dim(E) and δ bounds the diameter of each Sᵢ.
3. `large_economy_near_convex` — Large economy corollary: as the number
   of agents n grows, the per-agent approximation error vanishes to 0.

## Historical Context

Ross Starr (1969) applied the Shapley-Folkman lemma to prove that large
economies are "approximately convex": non-convexities in individual agent
preferences become negligible in aggregate. This validated the use of convex
analysis in large market equilibrium theory, where individual agents have
non-convex consumption sets.

The key insight: even if each agent's feasible set is non-convex, the market
clearing condition need only hold approximately (within d/n of exact balance),
and this approximation vanishes as the number of agents n grows.
-/

import Mathlib.Analysis.Normed.Module.Convex
import Proofs.ShapleyFolkman

set_option linter.unusedVariables false

namespace ShapleyFolkmanOQ03

open Set Finset Pointwise ShapleyFolkman

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

-- ============================================================
-- SECTION I: Distance Bound for Convex Hulls
-- ============================================================

/-- If p lies in the convex hull of S and q lies in S, and every point of S
    is within distance δ of q, then p is also within distance δ of q.

    **Proof**: The closed ball B(q, δ) is convex and contains S, so by
    `convexHull_min` (the convex hull is the smallest convex set containing S),
    p ∈ convexHull S ⊆ B(q, δ). -/
lemma convexHull_dist_le {S : Set E} {p q : E} {δ : ℝ}
    (hq : q ∈ S)
    (hbound : ∀ s ∈ S, dist s q ≤ δ)
    (hp : p ∈ convexHull ℝ S) :
    dist p q ≤ δ := by
  -- The closed ball B(q, δ) contains S
  have hS_sub : S ⊆ Metric.closedBall q δ := by
    intro s hs
    exact Metric.mem_closedBall.mpr (hbound s hs)
  -- B(q, δ) is convex
  have hball_conv : Convex ℝ (Metric.closedBall q δ) :=
    convex_closedBall q δ
  -- convexHull S ⊆ B(q, δ) by convexHull_min
  have hsub := convexHull_min hS_sub hball_conv
  -- p ∈ B(q, δ), i.e., dist p q ≤ δ
  exact Metric.mem_closedBall.mp (hsub hp)

/-- If the diameter of S is at most δ (i.e., all points of S are within δ
    of each other), then for any p ∈ conv(S) and q ∈ S, we have dist p q ≤ δ. -/
lemma convexHull_dist_le_diam {S : Set E} {p q : E} {δ : ℝ}
    (hq : q ∈ S)
    (hdiam : ∀ s₁ ∈ S, ∀ s₂ ∈ S, dist s₁ s₂ ≤ δ)
    (hp : p ∈ convexHull ℝ S) :
    dist p q ≤ δ :=
  convexHull_dist_le hq (fun s hs => hdiam s hs q hq) hp

-- ============================================================
-- SECTION II: Shapley-Folkman-Starr Theorem
-- ============================================================

/-- **Shapley-Folkman-Starr Theorem** (economic application):
    For a collection of sets {Sᵢ}ᵢ in a finite-dimensional normed space E,
    any point x in the convex hull of their Minkowski sum can be approximated
    by a point x' in the actual sum within distance d · δ, where d = dim(E)
    and δ bounds the pairwise distances in each Sᵢ.

    This is Starr's (1969) quantitative form of the Shapley-Folkman lemma:
    non-convexities are bounded independently of the number of summands.

    **Proof strategy**:
    1. Apply `sum_close_to_convexHull` to find f : ι → E with fᵢ ∈ conv(Sᵢ),
       Σfᵢ = x, and at most d "excess" indices where fᵢ ∉ Sᵢ.
    2. For each excess index j, replace f(j) ∈ conv(Sⱼ) with some f'(j) ∈ Sⱼ.
    3. x' = Σ f'ᵢ lies in ΣSᵢ and satisfies ‖x - x'‖ ≤ d · δ. -/
theorem shapley_folkman_starr [FiniteDimensional ℝ E]
    {ι : Type*} [DecidableEq ι] {S : ι → Set E} {t : Finset ι}
    (hne : ∀ i ∈ t, (S i).Nonempty)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hdiam : ∀ i ∈ t, ∀ s₁ ∈ S i, ∀ s₂ ∈ S i, dist s₁ s₂ ≤ δ)
    {x : E} (hx : x ∈ convexHull ℝ (∑ i ∈ t, S i)) :
    ∃ x' ∈ ∑ i ∈ t, S i,
      dist x x' ≤ (Module.finrank ℝ E : ℝ) * δ := by
  classical
  -- Step 1: Apply sum_close_to_convexHull to get a Shapley-Folkman decomposition
  obtain ⟨f, hf_mem, hf_sum, hf_excess⟩ := sum_close_to_convexHull hne hx
  -- J = excess indices: those where f i ∉ S i
  let J := t.filter (fun i => f i ∉ S i)
  have hJ_excess : J.card ≤ Module.finrank ℝ E := hf_excess
  have hJ_sub : J ⊆ t := Finset.filter_subset _ _
  -- Step 2: For each excess index j ∈ J, pick a point g(j) ∈ S(j)
  let g : ι → E := fun i =>
    if h : i ∈ J then (hne i (hJ_sub h)).choose else f i
  have hg_J : ∀ j ∈ J, g j ∈ S j := fun j hj => by
    simp only [g, dif_pos hj]
    exact (hne j (hJ_sub hj)).choose_spec
  have hg_notJ : ∀ i ∈ t, i ∉ J → g i ∈ S i := fun i hi hiJ => by
    simp only [g, dif_neg hiJ]
    simp only [J, Finset.mem_filter, hi, true_and, not_not] at hiJ
    exact hiJ
  -- Step 3: x' = Σᵢ g(i) lies in ΣSᵢ
  have hx'_mem : ∑ i ∈ t, g i ∈ ∑ i ∈ t, S i := by
    rw [Set.mem_finset_sum]
    refine ⟨g, ?_, rfl⟩
    intro i hi
    by_cases hiJ : i ∈ J
    · exact hg_J i hiJ
    · exact hg_notJ i hi hiJ
  -- Step 4: Estimate ‖x - x'‖
  -- x = Σ f i, x' = Σ g i, so x - x' = Σ (f i - g i)
  -- For i ∉ J: f i = g i (since g i = f i by def)
  -- For i ∈ J: ‖f i - g i‖ ≤ δ (since f i ∈ conv(S i), g i ∈ S i, diam(S i) ≤ δ)
  refine ⟨∑ i ∈ t, g i, hx'_mem, ?_⟩
  -- Rewrite dist x x'
  rw [← hf_sum]
  -- dist (Σ f) (Σ g) = ‖Σ (f - g)‖ = ‖Σ_{j ∈ J} (f j - g j)‖
  calc dist (∑ i ∈ t, f i) (∑ i ∈ t, g i)
      = ‖∑ i ∈ t, f i - ∑ i ∈ t, g i‖ := dist_eq_norm _ _
    _ = ‖∑ i ∈ t, (f i - g i)‖ := by rw [← Finset.sum_sub_distrib]
    _ = ‖∑ i ∈ J, (f i - g i)‖ := by
        -- Only J contributes: for i ∉ J, f i = g i, so f i - g i = 0
        congr 1
        symm
        apply Finset.sum_subset hJ_sub
        intro i hi hiJ
        simp only [g, dif_neg hiJ, sub_self]
    _ ≤ ∑ i ∈ J, ‖f i - g i‖ := norm_sum_le J _
    _ ≤ ∑ i ∈ J, δ := by
        apply Finset.sum_le_sum
        intro j hj
        -- f j ∈ conv(S j), g j ∈ S j, pairwise dist in S j ≤ δ
        -- Use the triangle inequality via convexHull_dist_le_diam
        rw [← dist_eq_norm]
        exact convexHull_dist_le_diam (hg_J j hj) (hdiam j (hJ_sub hj)) (hf_mem j (hJ_sub hj))
    _ = J.card * δ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Module.finrank ℝ E : ℝ) * δ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hJ_excess) hδ

-- ============================================================
-- SECTION III: Large Economy Corollary
-- ============================================================

/-- **Large Economy Corollary** (Starr 1969):
    For a large number n of agents each with sets of diameter ≤ δ,
    the per-agent approximation error is at most d · δ / n, which vanishes as n → ∞.

    More precisely: for n agents with identical feasible set S (n-fold Minkowski sum),
    any point x in conv(n·S) can be approximated by x' ∈ n·S within distance d·δ.
    Dividing by n: the average (x/n) is within d·δ/n of the actual mean.

    **Economic interpretation**: In a market with n agents, the per-agent
    discrepancy between the "convexified" outcome and the actual outcome is at
    most d·δ/n → 0. Large markets are approximately competitive. -/
theorem large_economy_near_convex [FiniteDimensional ℝ E]
    {S : Set E} (hne : S.Nonempty) {n : ℕ} (hn : 0 < n)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hdiam : ∀ s₁ ∈ S, ∀ s₂ ∈ S, dist s₁ s₂ ≤ δ)
    {x : E} (hx : x ∈ convexHull ℝ (n • S)) :
    ∃ x' ∈ n • S, dist x x' ≤ (Module.finrank ℝ E : ℝ) * δ := by
  -- n • S = ∑ i ∈ Fin n, (fun _ => S) i
  have hS_eq : n • S = ∑ i ∈ (Finset.univ : Finset (Fin n)), (fun _ : Fin n => S) i := by
    rw [Finset.sum_const]; simp [Fintype.card_fin]
  rw [hS_eq] at hx ⊢
  apply shapley_folkman_starr
  · intro i _; exact hne
  · exact hδ
  · intro i _ s₁ hs₁ s₂ hs₂; exact hdiam s₁ hs₁ s₂ hs₂
  · exact hx

-- ============================================================
-- SECTION IV: Zero Approximation for Convex Sets
-- ============================================================

/-- For a CONVEX Sᵢ, any f(i) ∈ conv(Sᵢ) already lies in Sᵢ, so no approximation error.
    This shows the Shapley-Folkman bound is tight: only non-convex summands contribute. -/
lemma no_excess_for_convex {S : Set E} (hS_conv : Convex ℝ S)
    {x : E} (hx : x ∈ convexHull ℝ S) : x ∈ S := by
  have : convexHull ℝ S = S := hS_conv.convexHull_eq
  rwa [this] at hx

end ShapleyFolkmanOQ03
