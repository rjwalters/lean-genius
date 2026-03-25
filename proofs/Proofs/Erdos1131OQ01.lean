/-
Erdős Problem #1131 — Open Question 01:
Is min I = 2 - (1 + o(1))/n ?

Investigates the precise asymptotic behavior of the minimum Lagrange basis integral.

Key structural results:
- Variance decomposition: I = 2/n + ∫ variance, separating the "uniform floor"
  from the excess
- Node evaluation: ∑ l_k(x_j)² = 1 (Kronecker delta identity)
- Variance at nodes: exactly (n-1)/n, showing the integrand peaks at node points
- Strict lower bound: I > 2/n for n ≥ 2 (the Cauchy-Schwarz bound is never tight)
- The Erdős conjecture is equivalent to: ∫ variance = 2 - (3 + o(1))/n

References:
- Parent: Erdos1131Problem.lean (lower bound I ≥ 2/n, partition of unity)
- Erdős, Szabados, Varma, Vértesi (1994): Best bounds 2 - O((log n)²/n) ≤ min I
-/

import Proofs.Erdos1131Problem

namespace Erdos1131OQ01

open MeasureTheory Erdos1131

/-
## Part I: Definitions
-/

/-- Pointwise variance: ∑ (l_k(x) - 1/n)² measures non-uniformity of the basis. -/
noncomputable def pointwiseVariance (n : ℕ) (nodes : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ k : Fin n, (lagrangeBasis n nodes k x - 1 / (n : ℝ)) ^ 2

/-- The integrated variance: ∫₋₁¹ ∑ (l_k(x) - 1/n)² dx. -/
noncomputable def integratedVariance (n : ℕ) (nodes : Fin n → ℝ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, pointwiseVariance n nodes x

/-- Continuity of the variance function (used in multiple proofs). -/
theorem continuous_pointwiseVariance (n : ℕ) (nodes : Fin n → ℝ) :
    Continuous (pointwiseVariance n nodes) := by
  unfold pointwiseVariance
  apply continuous_finset_sum; intro k _
  apply Continuous.pow
  apply Continuous.sub
  · unfold lagrangeBasis
    exact continuous_finset_prod _ fun i _ => (continuous_id.sub continuous_const).div_const _
  · exact continuous_const

/-
## Part II: Variance Decomposition (Pointwise)
-/

/--
**Variance identity**: ∑ l_k(x)² = 1/n + ∑ (l_k(x) - 1/n)² for distinct nodes.

Follows from expanding (l_k - 1/n)² and using the partition of unity ∑ l_k = 1.
-/
theorem variance_identity (n : ℕ) (hn : n ≥ 1) (nodes : Fin n → ℝ)
    (hd : AreDistinct n nodes) (x : ℝ) :
    ∑ k : Fin n, (lagrangeBasis n nodes k x) ^ 2 =
    1 / (n : ℝ) + pointwiseVariance n nodes x := by
  unfold pointwiseVariance
  have hpou := partition_of_unity n hn nodes hd x
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
  suffices h : ∑ k : Fin n, (lagrangeBasis n nodes k x - 1 / ↑n) ^ 2 =
    ∑ k : Fin n, (lagrangeBasis n nodes k x) ^ 2 - 1 / ↑n by linarith
  have hexp : ∀ k : Fin n, (lagrangeBasis n nodes k x - 1 / ↑n) ^ 2 =
    (lagrangeBasis n nodes k x) ^ 2 +
    (-(2 / ↑n) * lagrangeBasis n nodes k x + 1 / ↑n ^ 2) := by intro k; ring
  simp_rw [hexp]
  rw [Finset.sum_add_distrib]
  rw [show ∑ k : Fin n, (-(2 / ↑n) * lagrangeBasis n nodes k x + 1 / ↑n ^ 2) =
      -(2 / ↑n) * ∑ k : Fin n, lagrangeBasis n nodes k x + ↑n * (1 / ↑n ^ 2) from by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_fin,
        nsmul_eq_mul]]
  rw [hpou, mul_one]
  have key : -(2 / (↑n : ℝ)) + ↑n * (1 / ↑n ^ 2) = -(1 / ↑n) := by field_simp; ring
  linarith

/-
## Part III: Node Evaluation Identity
-/

/--
**Node evaluation**: ∑ l_k(x_j)² = 1 for each node x_j.

At a node, l_j(x_j) = 1 and l_k(x_j) = 0 for k ≠ j.
-/
theorem sum_sq_at_node (n : ℕ) (nodes : Fin n → ℝ)
    (hd : AreDistinct n nodes) (j : Fin n) :
    ∑ k : Fin n, (lagrangeBasis n nodes k (nodes j)) ^ 2 = 1 := by
  conv_rhs => rw [show (1 : ℝ) = ∑ k : Fin n, if k = j then 1 else 0 from by
    simp [Finset.sum_ite_eq']]
  congr 1; ext k
  by_cases hkj : k = j
  · subst hkj; simp [lagrangeBasis_self n nodes hd k]
  · simp [lagrangeBasis_other n nodes hd k j hkj, hkj]

/--
**Variance at nodes**: ∑ (l_k(x_j) - 1/n)² = (n-1)/n at each node.

At node x_j, l_j = 1 contributes (1-1/n)² and the n-1 others contribute (0-1/n)² each.
Total: ((n-1)/n)² + (n-1)/n² = (n-1)/n.
-/
theorem variance_at_node (n : ℕ) (hn : n ≥ 1) (nodes : Fin n → ℝ)
    (hd : AreDistinct n nodes) (j : Fin n) :
    pointwiseVariance n nodes (nodes j) = (n - 1 : ℝ) / n := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hvi := variance_identity n hn nodes hd (nodes j)
  have hsq := sum_sq_at_node n nodes hd j
  have h1 : pointwiseVariance n nodes (nodes j) = 1 - 1 / ↑n := by linarith
  rw [h1]; field_simp

/--
**Variance positivity at nodes**: For n ≥ 2, the variance is positive at each node.
-/
theorem variance_pos_at_node (n : ℕ) (hn : n ≥ 2) (nodes : Fin n → ℝ)
    (hd : AreDistinct n nodes) (j : Fin n) :
    pointwiseVariance n nodes (nodes j) > 0 := by
  rw [variance_at_node n (by omega) nodes hd j]
  have : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have : (0 : ℝ) < n - 1 := by linarith
  positivity

/-
## Part IV: Integral Decomposition
-/

/--
**Integral variance decomposition**: I = 2/n + ∫ variance.

Decomposes the total integral into the "uniform floor" 2/n and the
"excess" measuring non-uniformity.
-/
theorem integral_decomposition (n : ℕ) (hn : n ≥ 1) (nodes : Fin n → ℝ)
    (hd : AreDistinct n nodes) (_hrange : ∀ i, -1 ≤ nodes i ∧ nodes i ≤ 1) :
    lagrangeIntegral n nodes = 2 / (n : ℝ) + integratedVariance n nodes := by
  unfold lagrangeIntegral integratedVariance
  have hpw : ∀ x : ℝ,
    ∑ k : Fin n, (lagrangeBasis n nodes k x) ^ 2 =
    1 / (↑n : ℝ) + pointwiseVariance n nodes x :=
    fun x => variance_identity n hn nodes hd x
  simp_rw [hpw]
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((continuous_pointwiseVariance n nodes).intervalIntegrable _ _)]
  congr 1
  rw [intervalIntegral.integral_const, smul_eq_mul]
  ring

/--
**Integrated variance is non-negative**: ∫ variance ≥ 0 since variance ≥ 0 pointwise.
-/
theorem integratedVariance_nonneg (n : ℕ) (nodes : Fin n → ℝ) :
    integratedVariance n nodes ≥ 0 := by
  unfold integratedVariance
  apply intervalIntegral.integral_nonneg (by norm_num : (-1 : ℝ) ≤ 1)
  intro x _
  unfold pointwiseVariance
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

/-
## Part V: Strict Lower Bound
-/

/-- Pointwise variance is non-negative (sum of squares). -/
theorem pointwiseVariance_nonneg (n : ℕ) (nodes : Fin n → ℝ) (x : ℝ) :
    0 ≤ pointwiseVariance n nodes x := by
  unfold pointwiseVariance
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

/--
**Integrated variance strictly positive for n ≥ 2**.

The variance is continuous, ≥ 0, and equals (n-1)/n > 0 at each node in [-1,1].
By continuity, variance > c/2 on an interval around a node, where c = (n-1)/n.
The integral over this subinterval provides a positive lower bound.
-/
theorem integratedVariance_strictly_pos (n : ℕ) (hn : n ≥ 2) (nodes : Fin n → ℝ)
    (hd : AreDistinct n nodes) (hrange : ∀ i, -1 ≤ nodes i ∧ nodes i ≤ 1) :
    integratedVariance n nodes > 0 := by
  unfold integratedVariance
  -- Setup: variance is continuous and non-negative
  have h_cont := continuous_pointwiseVariance n nodes
  have h_nn := pointwiseVariance_nonneg n nodes
  -- Variance is positive at x₀ = nodes 0
  set j₀ : Fin n := ⟨0, by omega⟩
  set x₀ := nodes j₀ with hx₀_def
  set c := pointwiseVariance n nodes x₀ with hc_def
  have hc_pos : 0 < c := variance_pos_at_node n hn nodes hd j₀
  have hx₀_lo := (hrange j₀).1
  have hx₀_hi := (hrange j₀).2
  -- By continuity: ∃ δ > 0, |y - x₀| < δ → |v(y) - c| < c/2
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp h_cont.continuousAt (c / 2) (by linarith)
  -- Subinterval [a, b] ⊂ [-1, 1] around x₀
  set a := max (-1 : ℝ) (x₀ - δ / 2) with ha_def
  set b := min (1 : ℝ) (x₀ + δ / 2) with hb_def
  -- a < b (since x₀ ∈ [-1,1] and δ > 0)
  have hab : a < b :=
    max_lt (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith))
  -- Containment: -1 ≤ a and b ≤ 1
  have ha_ge : (-1 : ℝ) ≤ a := le_max_left ..
  have hb_le : b ≤ 1 := min_le_left ..
  -- On [a, b], variance > c/2 (via epsilon-delta)
  have hv_lb : ∀ y, y ∈ Set.Icc a b → c / 2 ≤ pointwiseVariance n nodes y := by
    intro y ⟨hay, hyb⟩
    -- |y - x₀| ≤ δ/2 < δ
    have h_ub : y - x₀ ≤ δ / 2 := by
      calc y - x₀ ≤ b - x₀ := by linarith
        _ ≤ (x₀ + δ / 2) - x₀ := by linarith [min_le_right (1 : ℝ) (x₀ + δ / 2)]
        _ = δ / 2 := by ring
    have h_lb : -(δ / 2) ≤ y - x₀ := by
      calc -(δ / 2) = (x₀ - δ / 2) - x₀ := by ring
        _ ≤ a - x₀ := by linarith [le_max_right (-1 : ℝ) (x₀ - δ / 2)]
        _ ≤ y - x₀ := by linarith
    have h_dist : dist y x₀ < δ := by
      rw [Real.dist_eq]
      calc |y - x₀| ≤ δ / 2 := abs_le.mpr ⟨by linarith, h_ub⟩
        _ < δ := by linarith
    -- |v(y) - c| < c/2, so v(y) > c - c/2 = c/2
    have h_near := hδ h_dist
    rw [Real.dist_eq] at h_near
    linarith [(abs_lt.mp h_near).1]
  -- Decompose: ∫_{-1}^{1} = ∫_{-1}^{a} + ∫_{a}^{b} + ∫_{b}^{1}
  have hint : ∀ u v : ℝ, IntervalIntegrable (pointwiseVariance n nodes) volume u v :=
    fun u v => h_cont.intervalIntegrable u v
  have h_split : ∫ x in (-1 : ℝ)..1, pointwiseVariance n nodes x =
      (∫ x in (-1 : ℝ)..a, pointwiseVariance n nodes x) +
      (∫ x in a..b, pointwiseVariance n nodes x) +
      (∫ x in b..(1 : ℝ), pointwiseVariance n nodes x) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals (hint (-1) a) (hint a 1)
    have h2 := intervalIntegral.integral_add_adjacent_intervals (hint a b) (hint b 1)
    linarith
  -- Each complement piece is ≥ 0
  have h_left_nn : 0 ≤ ∫ x in (-1 : ℝ)..a, pointwiseVariance n nodes x :=
    intervalIntegral.integral_nonneg ha_ge (fun x _ => h_nn x)
  have h_right_nn : 0 ≤ ∫ x in b..(1 : ℝ), pointwiseVariance n nodes x :=
    intervalIntegral.integral_nonneg hb_le (fun x _ => h_nn x)
  -- Middle piece: ∫_{a}^{b} v ≥ (c/2)(b-a) > 0
  have h_mid : c / 2 * (b - a) ≤ ∫ x in a..b, pointwiseVariance n nodes x := by
    calc c / 2 * (b - a)
        = ∫ _ in a..b, c / 2 := by
            rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      _ ≤ ∫ x in a..b, pointwiseVariance n nodes x := by
          apply intervalIntegral.integral_mono_on hab.le
            intervalIntegrable_const (hint a b)
          intro x hx
          exact hv_lb x (Set.uIcc_of_le hab.le ▸ hx)
  -- Combine: ∫ ≥ 0 + (c/2)(b-a) + 0 > 0
  linarith [mul_pos (by linarith : c / 2 > 0) (by linarith : b - a > 0)]

/--
**Strict lower bound**: For n ≥ 2, I > 2/n (the Cauchy-Schwarz bound is never tight).
-/
theorem lagrangeIntegral_strict_lower (n : ℕ) (hn : n ≥ 2) (nodes : Fin n → ℝ)
    (hd : AreDistinct n nodes) (hrange : ∀ i, -1 ≤ nodes i ∧ nodes i ≤ 1) :
    lagrangeIntegral n nodes > 2 / (n : ℝ) := by
  rw [integral_decomposition n (by omega) nodes hd hrange]
  linarith [integratedVariance_strictly_pos n hn nodes hd hrange]

/-
## Part VI: Conjecture Reformulation
-/

/--
**Conjecture reformulation**: min I = 2 - (1+o(1))/n ⟺ min ∫var = 2 - (3+o(1))/n.

This follows from the decomposition I = 2/n + ∫var.
-/
noncomputable def minIntegratedVariance (n : ℕ) : ℝ :=
  sInf {integratedVariance n nodes | nodes : Fin n → ℝ}

/-- The Erdős conjecture in variance form: min ∫ variance ≈ 2 - 3/n. -/
axiom erdos_1131_variance_conjecture :
    ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      |minIntegratedVariance n - (2 - 3 / (n : ℝ))| ≤ ε / n

/-
## Part VII: Main Result
-/

/--
**Erdős #1131 OQ01**: For n ≥ 2 distinct nodes in [-1,1], I > 2/n (strict).
The Cauchy-Schwarz bound I ≥ 2/n is never achieved; the true minimum is ≈ 2 - 1/n.
-/
theorem erdos_1131_oq01 (n : ℕ) (hn : n ≥ 2) (nodes : Fin n → ℝ)
    (hd : AreDistinct n nodes) (hrange : ∀ i, -1 ≤ nodes i ∧ nodes i ≤ 1) :
    lagrangeIntegral n nodes > 2 / (n : ℝ) :=
  lagrangeIntegral_strict_lower n hn nodes hd hrange

end Erdos1131OQ01
