/-
  Cauchy-Schwarz Equality: Exact Proportionality Constant
  Open Question: cauchy-schwarz-oq-04

  When |inner u v| = norm u * norm v, the vectors are proportional. This formalization
  proves the EXACT proportionality constant: u = (inner u v / norm v ^ 2) * v.

  This is the orthogonal projection coefficient -- the scalar c such that u = cv
  when Cauchy-Schwarz equality holds.

  References:
  - Cauchy (1821): original discrete inequality with equality case noted
  - Steele "The Cauchy-Schwarz Master Class" (2004): Chapter 2
  - CauchySchwarz.lean: base inequality and exists c, u = cv characterization
-/

import Mathlib

namespace CauchySchwarzOQ04

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- ============================================================================
-- Part I: The Orthogonal Projection Coefficient
-- ============================================================================

/-- The orthogonal projection coefficient of u onto v. -/
noncomputable def projCoeff (u v : E) : ℝ := ⟪u, v⟫_ℝ / ‖v‖ ^ 2

/-- The orthogonal projection of u onto v. -/
noncomputable def proj (u v : E) : E := projCoeff u v • v

/-- The projection coefficient satisfies inner u v = projCoeff u v * norm v ^ 2. -/
theorem projCoeff_mul_norm_sq (u v : E) (hv : v ≠ 0) :
    projCoeff u v * ‖v‖ ^ 2 = ⟪u, v⟫_ℝ := by
  unfold projCoeff
  exact div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv))

/-- The residual u - proj_v(u) is orthogonal to v. -/
theorem proj_orthogonal (u v : E) (hv : v ≠ 0) :
    ⟪u - proj u v, v⟫_ℝ = 0 := by
  unfold proj projCoeff
  rw [inner_sub_left, inner_smul_left]
  simp only [starRingEnd_apply, star_trivial, real_inner_self_eq_norm_sq]
  rw [div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv))]
  exact sub_self _

/-- The residual norm squared via Pythagoras. -/
theorem norm_sq_decomposition (u v : E) (hv : v ≠ 0) :
    ‖u‖ ^ 2 = (projCoeff u v) ^ 2 * ‖v‖ ^ 2 + ‖u - proj u v‖ ^ 2 := by
  have h_orth := proj_orthogonal u v hv
  have h_split : u = proj u v + (u - proj u v) := by abel
  conv_lhs => rw [h_split]
  rw [norm_add_sq_real]
  unfold proj
  rw [norm_smul, Real.norm_eq_abs]
  have h_cross : ⟪projCoeff u v • v, u - projCoeff u v • v⟫_ℝ = 0 := by
    rw [inner_smul_left]
    simp only [starRingEnd_apply, star_trivial]
    rw [show u - projCoeff u v • v = u - proj u v from rfl]
    rw [real_inner_comm, h_orth, mul_zero]
  rw [h_cross]
  nlinarith [sq_abs (projCoeff u v)]

-- ============================================================================
-- Part II: Exact Proportionality Constant in CS Equality
-- ============================================================================

/-- CS Equality gives exact proportionality constant (forward direction).

When |inner u v| = norm u * norm v and v is nonzero, then u = (inner u v / norm v ^ 2) * v. -/
theorem cs_equality_exact_constant (u v : E) (hv : v ≠ 0)
    (h : |⟪u, v⟫_ℝ| = ‖u‖ * ‖v‖) :
    u = projCoeff u v • v := by
  -- Show the residual norm is zero
  have h_decomp := norm_sq_decomposition u v hv
  have h_proj_sq : (projCoeff u v) ^ 2 * ‖v‖ ^ 2 = ‖u‖ ^ 2 := by
    unfold projCoeff
    have h_sq : ⟪u, v⟫_ℝ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
      rw [← sq_abs, h, mul_pow]
    have hv2 : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
    field_simp
    linarith [h_sq]
  have h_resid_sq : ‖u - proj u v‖ ^ 2 = 0 := by linarith
  have h_resid : u - proj u v = 0 := by
    rw [← norm_eq_zero]
    nlinarith [sq_nonneg ‖u - proj u v‖]
  unfold proj at h_resid
  exact sub_eq_zero.mp h_resid

/-- CS Equality: exact constant (reverse direction).

If u = (inner u v / norm v ^ 2) * v, then |inner u v| = norm u * norm v. -/
theorem cs_equality_of_exact_constant (u v : E) (hv : v ≠ 0)
    (h : u = projCoeff u v • v) :
    |⟪u, v⟫_ℝ| = ‖u‖ * ‖v‖ := by
  -- For any c, if u = c • v then |⟨u,v⟩| = |c| * ‖v‖² and ‖u‖ * ‖v‖ = |c| * ‖v‖²
  set c := projCoeff u v with hc_def
  rw [h, inner_smul_left]
  simp only [starRingEnd_apply, star_trivial, real_inner_self_eq_norm_sq]
  rw [norm_smul, Real.norm_eq_abs]
  rw [abs_mul, abs_of_nonneg (sq_nonneg ‖v‖), sq]
  ring

/-- CS Equality iff exact proportionality constant (full characterization).

For v nonzero: |inner u v| = norm u * norm v iff u = (inner u v / norm v ^ 2) * v. -/
theorem cs_equality_iff_exact_constant (u v : E) (hv : v ≠ 0) :
    |⟪u, v⟫_ℝ| = ‖u‖ * ‖v‖ ↔ u = projCoeff u v • v :=
  ⟨cs_equality_exact_constant u v hv, cs_equality_of_exact_constant u v hv⟩

-- ============================================================================
-- Part III: Properties of the Projection Coefficient
-- ============================================================================

/-- When u = c * v, the projection coefficient is c. -/
theorem projCoeff_of_smul (c : ℝ) (v : E) (hv : v ≠ 0) :
    projCoeff (c • v) v = c := by
  unfold projCoeff
  rw [inner_smul_left]
  simp only [starRingEnd_apply, star_trivial, real_inner_self_eq_norm_sq]
  rw [mul_div_cancel_right₀]
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)

/-- The projection coefficient of v onto v is 1. -/
theorem projCoeff_self (v : E) (hv : v ≠ 0) : projCoeff v v = 1 := by
  have : projCoeff ((1 : ℝ) • v) v = 1 := projCoeff_of_smul 1 v hv
  rwa [one_smul] at this

/-- projCoeff is additive in the first argument. -/
theorem projCoeff_add (u₁ u₂ v : E) :
    projCoeff (u₁ + u₂) v = projCoeff u₁ v + projCoeff u₂ v := by
  unfold projCoeff
  rw [inner_add_left, add_div]

/-- projCoeff scales linearly. -/
theorem projCoeff_smul (c : ℝ) (u v : E) :
    projCoeff (c • u) v = c * projCoeff u v := by
  unfold projCoeff
  rw [inner_smul_left]
  simp only [starRingEnd_apply, star_trivial, mul_div_assoc]

-- ============================================================================
-- Part IV: CS Equality and the Residual Norm
-- ============================================================================

/-- CS equality holds iff the residual is zero. -/
theorem cs_equality_iff_zero_residual (u v : E) (hv : v ≠ 0) :
    |⟪u, v⟫_ℝ| = ‖u‖ * ‖v‖ ↔ u - proj u v = 0 := by
  rw [cs_equality_iff_exact_constant u v hv]
  exact ⟨fun h => sub_eq_zero.mpr (by unfold proj; exact h),
         fun h => by unfold proj at h; exact sub_eq_zero.mp h⟩

-- ============================================================================
-- Part V: Geometric Interpretation
-- ============================================================================

/-- If inner u v > 0 (vectors in "same direction"), then projCoeff > 0. -/
theorem projCoeff_pos_of_inner_pos (u v : E) (hv : v ≠ 0)
    (h : 0 < ⟪u, v⟫_ℝ) : 0 < projCoeff u v := by
  unfold projCoeff
  exact div_pos h (pow_pos (norm_pos_iff.mpr hv) 2)

/-- If inner u v < 0 (vectors in "opposite directions"), then projCoeff < 0. -/
theorem projCoeff_neg_of_inner_neg (u v : E) (hv : v ≠ 0)
    (h : ⟪u, v⟫_ℝ < 0) : projCoeff u v < 0 := by
  unfold projCoeff
  exact div_neg_of_neg_of_pos h (pow_pos (norm_pos_iff.mpr hv) 2)

/-- CS equality with positive inner product: u and v point in the same direction. -/
theorem cs_equality_same_direction (u v : E) (hv : v ≠ 0)
    (h_eq : ⟪u, v⟫_ℝ = ‖u‖ * ‖v‖) (hu : u ≠ 0) :
    0 < projCoeff u v := by
  apply projCoeff_pos_of_inner_pos u v hv
  rw [h_eq]
  exact mul_pos (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv)

/-- CS equality with negative inner product: u and v point in opposite directions. -/
theorem cs_equality_opposite_direction (u v : E) (hv : v ≠ 0)
    (h_eq : ⟪u, v⟫_ℝ = -(‖u‖ * ‖v‖)) (hu : u ≠ 0) :
    projCoeff u v < 0 := by
  apply projCoeff_neg_of_inner_neg u v hv
  rw [h_eq]
  linarith [mul_pos (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv)]

-- ============================================================================
-- Part VI: Connection to Existing Cauchy-Schwarz Equality Result
-- ============================================================================

/-- Bridge: the existential "exists c, u = cv" from CauchySchwarz.lean has c = projCoeff u v. -/
theorem existential_constant_is_projCoeff (u v : E) (hv : v ≠ 0)
    (c : ℝ) (h : u = c • v) : c = projCoeff u v := by
  have h2 := projCoeff_of_smul c v hv
  rw [← h] at h2
  exact h2.symm

-- ============================================================================
-- Part VII: Finite-Dimensional / Finite Sum Version
-- ============================================================================

open Finset in
/-- Finite sum version of exact constant.

For sequences a, b : Fin n -> R with b nonzero:
If (sum a_i*b_i)^2 = (sum a_i^2)(sum b_i^2), then a_i = (sum a_j*b_j / sum b_j^2) * b_i. -/
theorem finite_sum_exact_constant {n : ℕ} (a b : Fin n → ℝ)
    (hb : ∃ k, b k ≠ 0)
    (h : (∑ i, a i * b i) ^ 2 = (∑ i, a i ^ 2) * (∑ i, b i ^ 2)) :
    ∀ i, a i = (∑ j, a j * b j) / (∑ j, b j ^ 2) * b i := by
  obtain ⟨k, hbk⟩ := hb
  -- All cross-terms vanish: a_i * b_j = a_j * b_i
  have h_cross : ∀ i j : Fin n, a i * b j = a j * b i := by
    intro i j
    have h_deficit : (∑ x, a x ^ 2) * (∑ x, b x ^ 2) - (∑ x, a x * b x) ^ 2 = 0 := by
      linarith
    suffices h_sum_zero : ∑ p : Fin n, ∑ q : Fin n, (a p * b q - a q * b p) ^ 2 = 0 by
      have h_outer_nn : ∀ p ∈ univ, (0 : ℝ) ≤ ∑ q : Fin n, (a p * b q - a q * b p) ^ 2 :=
        fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
      have h_inner_zero := (sum_eq_zero_iff_of_nonneg h_outer_nn).mp h_sum_zero i (mem_univ i)
      have h_inner_nn : ∀ q ∈ univ, (0 : ℝ) ≤ (a i * b q - a q * b i) ^ 2 :=
        fun _ _ => sq_nonneg _
      have := (sum_eq_zero_iff_of_nonneg h_inner_nn).mp h_inner_zero j (mem_univ j)
      have := sq_eq_zero_iff.mp this
      linarith
    -- Lagrange identity: double sum = 2 * deficit
    have h_lagrange : ∑ p : Fin n, ∑ q : Fin n, (a p * b q - a q * b p) ^ 2 =
        2 * ((∑ x, a x ^ 2) * (∑ x, b x ^ 2) - (∑ x, a x * b x) ^ 2) := by
      simp_rw [sub_sq]
      simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      have ha : ∑ p : Fin n, ∑ q : Fin n, (a p * b q) ^ 2 =
          (∑ p, a p ^ 2) * (∑ q, b q ^ 2) := by
        simp_rw [mul_pow, ← mul_sum, ← sum_mul]
      have hc : ∑ p : Fin n, ∑ q : Fin n, (a q * b p) ^ 2 =
          (∑ q, a q ^ 2) * (∑ p, b p ^ 2) := by
        rw [sum_comm]
        simp_rw [mul_pow, ← mul_sum, ← sum_mul]
      have hb2 : ∑ p : Fin n, ∑ q : Fin n, 2 * (a p * b q) * (a q * b p) =
          2 * (∑ p, a p * b p) ^ 2 := by
        simp_rw [sq, sum_mul, mul_sum]
        congr 1; ext p; congr 1; ext q; ring
      rw [ha, hc, hb2]; ring
    rw [h_lagrange, h_deficit, mul_zero]
  -- Now use cross-term vanishing to get the ratio
  intro i
  have hb_sq_pos : 0 < ∑ j, b j ^ 2 := by
    apply sum_pos'
    · intro j _; exact sq_nonneg _
    · exact ⟨k, mem_univ k, by positivity⟩
  have hb_sq_ne : (∑ j, b j ^ 2) ≠ 0 := ne_of_gt hb_sq_pos
  -- a_i = (a_k / b_k) * b_i from cross-terms
  have h_ai : a i = a k / b k * b i := by
    have h_ik := h_cross i k
    field_simp
    linarith
  -- a_k / b_k = sum(a*b) / sum(b^2)
  have h_sum_eq : ∑ j, a j * b j = (a k / b k) * ∑ j, b j ^ 2 := by
    rw [mul_sum]
    congr 1; ext j
    have h_jk := h_cross j k
    have : a j = a k * b j / b k := by
      field_simp
      linarith
    rw [this]; ring
  have h_ratio : a k / b k = (∑ j, a j * b j) / (∑ j, b j ^ 2) := by
    rw [h_sum_eq, mul_div_cancel_right₀ _ hb_sq_ne]
  rw [h_ai, h_ratio]

-- ============================================================================
-- Part VIII: Examples
-- ============================================================================

/-- Example: for u = 3v, projCoeff u v = 3. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) (hv : v ≠ 0) : projCoeff ((3 : ℝ) • v) v = 3 :=
  projCoeff_of_smul 3 v hv

/-- Example: projCoeff v v = 1. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) (hv : v ≠ 0) : projCoeff v v = 1 :=
  projCoeff_self v hv

#check cs_equality_exact_constant
#check cs_equality_iff_exact_constant
#check finite_sum_exact_constant

end CauchySchwarzOQ04
