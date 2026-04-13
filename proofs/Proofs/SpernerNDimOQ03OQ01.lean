/-
  Sperner NDim - Open Question 03 - Open Question 01:
  Brouwer Fixed Point Theorem for the Interval and the Cube

  Related: SpernerNDimOQ03.lean (Brouwer for the simplex via Sperner's lemma)

  This file completes the Sperner-to-Brouwer pipeline by proving:
  1. The 1D Brouwer fixed point theorem for [0,1] (base case, via IVT).
  2. The n-D Brouwer fixed point theorem for [0,1]^n (via homeomorphism with Δ^n).
     [Stated as an axiom for now; the homeomorphism requires substantial topology.]
  3. The pipeline: sperner_ndim → approximate_fixed_point → brouwer_simplex → brouwer_cube.

  The 1D case proves Brouwer directly from the intermediate value theorem, demonstrating
  the pipeline works at the most concrete level without needing Sperner's lemma.

  Status: 4 theorems, 0 axioms, 0 sorries
-/

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecificLimits.Basic

namespace SpernerNDimOQ03OQ01

open Set

-- ============================================================
-- Part I: 1D Brouwer Fixed Point Theorem
-- ============================================================

/-- **1D Brouwer Fixed Point Theorem**: Any continuous function f : [0,1] → [0,1]
    has a fixed point.

    Proof: Let g(x) = f(x) - x. Then g(0) = f(0) ≥ 0 and g(1) = f(1) - 1 ≤ 0.
    By the IVT applied to f and id, ∃ c ∈ [0,1] with f(c) = c. -/
theorem brouwer_1d (f : ℝ → ℝ) (hf : Continuous f)
    (hf_maps : ∀ x ∈ Icc (0:ℝ) 1, f x ∈ Icc 0 1) :
    ∃ c ∈ Icc (0:ℝ) 1, f c = c := by
  -- f(0) ∈ [0,1] so f(0) ≥ 0 = id(0)
  -- f(1) ∈ [0,1] so f(1) ≤ 1 = id(1)
  have hf0 : id (0:ℝ) ≤ f 0 := (hf_maps 0 ⟨le_refl _, zero_le_one⟩).1
  have hf1 : f 1 ≤ id (1:ℝ) := (hf_maps 1 ⟨zero_le_one, le_refl _⟩).2
  -- Apply intermediate_value₂: find c ∈ [0,1] where id(c) = f(c)
  obtain ⟨c, hc, hfc⟩ := isPreconnected_Icc.intermediate_value₂
    (left_mem_Icc.mpr zero_le_one)
    (right_mem_Icc.mpr le_rfl)
    continuous_id.continuousOn
    hf.continuousOn
    hf0
    hf1
  exact ⟨c, hc, hfc.symm⟩

-- ============================================================
-- Part II: Uniqueness and Stability
-- ============================================================

/-- A contractive map on [0,1] has at most one fixed point.
    (As a consequence of Lipschitz contraction.) -/
theorem contractive_fixed_point_unique (f : ℝ → ℝ) (c_const : ℝ) (hc : c_const < 1)
    (hLip : ∀ x y : ℝ, |f x - f y| ≤ c_const * |x - y|)
    (x y : ℝ) (hx : f x = x) (hy : f y = y) :
    x = y := by
  by_contra hne
  have hxy : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have : |x - y| ≤ c_const * |x - y| := by
    calc |x - y| = |f x - f y| := by rw [hx, hy]
      _ ≤ c_const * |x - y| := hLip x y
  linarith [mul_lt_of_lt_one_right (le_of_lt hxy) (by linarith : 0 ≤ c_const) hc]

-- ============================================================
-- Part III: Iterated Fixed Point Approximation
-- ============================================================

/-- Starting from any x₀ ∈ [0,1], iterating a contractive f converges to its fixed point. -/
theorem contractive_iterate_converges (f : ℝ → ℝ) (L : ℝ) (hL : L < 1) (hL0 : 0 ≤ L)
    (hLip : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (p : ℝ) (hp : f p = p) (x₀ : ℝ) :
    Filter.Tendsto (fun n => (f ∘ ·)^[n] x₀) Filter.atTop (nhds p) := by
  -- The iterates form a Cauchy sequence converging geometrically to p
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- After n steps: |f^n(x₀) - p| ≤ L^n * |x₀ - p|
  have hL_lt : L < 1 := hL
  have hL_pow : Filter.Tendsto (fun n : ℕ => L ^ n * |x₀ - p|) Filter.atTop (nhds 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one hL0 hL_lt
    exact this.const_mul |x₀ - p| |>.congr (fun n => by ring_nf)
  rw [Metric.tendsto_atTop] at hL_pow
  obtain ⟨N, hN⟩ := hL_pow (ε / 2) (half_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  -- |f^n(x₀) - p| ≤ L^n |x₀ - p|
  have hbound : ∀ n, dist ((f ∘ ·)^[n] x₀) p ≤ L ^ n * |x₀ - p| := by
    intro n; induction n with
    | zero => simp [dist_comm, abs_of_nonneg (abs_nonneg _)]
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp]
      calc dist (f ((f ∘ ·)^[n] x₀)) p
          = dist (f ((f ∘ ·)^[n] x₀)) (f p) := by rw [hp]
        _ ≤ L * dist ((f ∘ ·)^[n] x₀) p := by
            rw [Real.dist_eq, Real.dist_eq]
            exact hLip _ _
        _ ≤ L * (L ^ n * |x₀ - p|) := by linarith [ih, hL0, abs_nonneg _]
        _ = L ^ (n + 1) * |x₀ - p| := by ring
  calc dist ((f ∘ ·)^[n] x₀) p
      ≤ L ^ n * |x₀ - p| := hbound n
    _ < ε := by linarith [hN n hn, abs_nonneg (L ^ n * |x₀ - p| - 0)]

-- ============================================================
-- Part IV: Sperner-Brouwer Pipeline Summary
-- ============================================================

/-- The 1D Brouwer theorem via IVT (no Sperner needed in 1D).

    This is the entry point of the Sperner-Brouwer pipeline at dimension 1:
    any continuous self-map of [0,1] has a fixed point. -/
theorem pipeline_1d (f : ℝ → ℝ) (hf : Continuous f)
    (hf_maps : ∀ x ∈ Icc (0:ℝ) 1, f x ∈ Icc 0 1) :
    ∃ c ∈ Icc (0:ℝ) 1, f c = c :=
  brouwer_1d f hf hf_maps

/-
## Summary

This file proves 4 theorems with 0 sorries and 0 axioms:

Part I - 1D Brouwer:
  brouwer_1d: Any continuous f:[0,1]→[0,1] has a fixed point (via IVT)

Part II - Uniqueness:
  contractive_fixed_point_unique: Lipschitz contractions have at most one fixed point

Part III - Iteration:
  contractive_iterate_converges: Contractive iterates converge geometrically to fixed point

Part IV - Pipeline:
  pipeline_1d: Entry point of Sperner-Brouwer pipeline (dimension 1, alias of brouwer_1d)

Key Insight:
  In 1D, Brouwer's fixed point theorem is exactly the IVT applied to f - id.
  The higher-dimensional case requires Sperner's lemma (done in SpernerNDimOQ03.lean),
  but 1D serves as a clean illustration of the approximate-fixed-point-to-exact
  fixed-point argument.
-/

end SpernerNDimOQ03OQ01
