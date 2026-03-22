/-
Cauchy-Schwarz Equality for Complex Inner Product Spaces

Open Question (cauchy-schwarz-oq-01-oq-01):
"Can the equality characterization (‖⟪u,v⟫_ℂ‖ = ‖u‖·‖v‖ ↔ u and v are linearly
dependent) be stated and proved for complex inner product spaces?"

Answer: YES — proved via orthogonal decomposition. For v ≠ 0, write
u = c·v + w where c = ⟪v,u⟫/⟪v,v⟫ and w ⊥ v. Equality in Cauchy-Schwarz
forces ‖w‖ = 0, hence u = c·v.

This file formalizes:
1. Backward direction: scalar multiple → CS equality (direct computation)
2. Orthogonal projection lemma: the residual u − (⟪v,u⟫/⟪v,v⟫)·v ⊥ v
3. Forward direction: CS equality → scalar multiple (via Pythagoras)
4. Main iff theorem for complex and uniform RCLike inner product spaces
5. Edge cases: v = 0, both zero, symmetry

References:
- Mathlib: norm_inner_le_norm, inner_self_eq_norm_sq_to_K
- Schwarz (1885), Bunyakovsky (1859)
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

open scoped InnerProductSpace

namespace CauchySchwarzOQ01OQ01

-- ============================================================
-- PART I: Backward Direction (scalar multiple → equality)
-- ============================================================

/-- If u = c • v, then Cauchy-Schwarz holds with equality.
    Works for any RCLike field 𝕜 (covers both ℝ and ℂ). -/
theorem cs_equality_of_smul {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (v : E) (c : 𝕜) : ‖⟪c • v, v⟫_𝕜‖ = ‖c • v‖ * ‖v‖ := by
  rw [inner_smul_left, inner_self_eq_norm_sq_to_K, norm_mul, norm_smul]
  simp only [starRingEnd_apply, norm_star, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg v)]
  ring

-- ============================================================
-- PART II: Orthogonal Projection Lemma
-- ============================================================

/-- The residual u − (⟪v,u⟫/⟪v,v⟫)·v is orthogonal to v.
    This is the fundamental orthogonal decomposition property. -/
theorem inner_projection_residual_eq_zero {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (u v : E) (hv : v ≠ 0) :
    ⟪u - (⟪v, u⟫_𝕜 / ⟪v, v⟫_𝕜) • v, v⟫_𝕜 = 0 := by
  have hvv : ⟪v, v⟫_𝕜 ≠ 0 := by
    intro h; exact hv (inner_self_eq_zero.mp h)
  simp only [inner_sub_left, inner_smul_left, map_div₀, inner_conj_symm]
  field_simp
  ring

-- ============================================================
-- PART III: Forward Direction (equality → scalar multiple)
-- ============================================================

/-- Cauchy-Schwarz equality implies linear dependence.
    If ‖⟪u, v⟫_𝕜‖ = ‖u‖·‖v‖ and v ≠ 0, then u is a scalar multiple of v.

    Proof: Let c = ⟪v,u⟫/⟪v,v⟫ and w = u − c·v.
    - w ⊥ v (from Part II)
    - ‖u‖² = ‖w‖² + ‖c·v‖² (Pythagoras)
    - ‖⟪u,v⟫‖ = ‖c‖·‖v‖² (from orthogonality + computation)
    - Equality forces ‖w‖ = 0, so u = c·v. -/
theorem cs_equality_implies_smul {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (u v : E) (hv : v ≠ 0) (h : ‖⟪u, v⟫_𝕜‖ = ‖u‖ * ‖v‖) :
    ∃ c : 𝕜, u = c • v := by
  -- Define projection coefficient and residual
  set c := ⟪v, u⟫_𝕜 / ⟪v, v⟫_𝕜 with hc_def
  -- Step 1: The residual w = u - c·v is orthogonal to v
  have hortho : ⟪u - c • v, v⟫_𝕜 = 0 :=
    inner_projection_residual_eq_zero u v hv
  -- Step 2: ⟪u−c·v, c·v⟫ = 0 (linearity of inner product)
  have hortho_cv : ⟪u - c • v, c • v⟫_𝕜 = 0 := by
    rw [inner_smul_right, hortho, mul_zero]
  -- Step 3: Pythagoras: ‖u‖² = ‖u−c·v‖² + ‖c·v‖²
  have hpyth : ‖u‖ ^ 2 = ‖u - c • v‖ ^ 2 + ‖c • v‖ ^ 2 := by
    have hsplit : u = (u - c • v) + c • v := by abel
    conv_lhs => rw [hsplit]
    rw [norm_add_sq (𝕜 := 𝕜), hortho_cv, map_zero]
    ring
  -- Step 4: Compute ‖⟪u,v⟫‖ = ‖c‖ · ‖v‖²
  have hinner_val : ‖⟪u, v⟫_𝕜‖ = ‖c‖ * ‖v‖ ^ 2 := by
    have hsplit : u = (u - c • v) + c • v := by abel
    conv_lhs => rw [hsplit]
    rw [inner_add_left, hortho, zero_add, inner_smul_left, inner_self_eq_norm_sq_to_K,
      norm_mul]
    simp only [starRingEnd_apply, norm_star, norm_pow, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg v)]
  -- Step 5: From equality, derive ‖c‖·‖v‖ = ‖u‖
  have hv_ne : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hcv_norm : ‖c‖ * ‖v‖ = ‖u‖ := by
    have h1 : ‖c‖ * ‖v‖ ^ 2 = ‖u‖ * ‖v‖ := by linarith [hinner_val]
    have h2 : ‖c‖ * ‖v‖ * ‖v‖ = ‖u‖ * ‖v‖ := by rw [sq] at h1; linarith
    exact mul_right_cancel₀ hv_ne h2
  -- Step 6: ‖u − c·v‖ = 0
  have hres_zero : ‖u - c • v‖ = 0 := by
    have hcv_sq : ‖c • v‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [norm_smul, hcv_norm]
    have : ‖u - c • v‖ ^ 2 = 0 := by linarith [hpyth]
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  -- Step 7: u = c·v
  exact ⟨c, sub_eq_zero.mp (norm_eq_zero.mp hres_zero)⟩

-- ============================================================
-- PART IV: Main Equivalence Theorems
-- ============================================================

/-- **Complex Cauchy-Schwarz Equality** (main theorem).
    ‖⟪u, v⟫_ℂ‖ = ‖u‖·‖v‖ iff u and v are ℂ-linearly dependent. -/
theorem cauchy_schwarz_eq_iff_complex {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u v : E) (hv : v ≠ 0) :
    ‖⟪u, v⟫_ℂ‖ = ‖u‖ * ‖v‖ ↔ ∃ c : ℂ, u = c • v := by
  constructor
  · exact cs_equality_implies_smul u v hv
  · rintro ⟨c, rfl⟩
    exact cs_equality_of_smul v c

/-- **Uniform Cauchy-Schwarz Equality** for any RCLike field 𝕜.
    Covers both ℝ and ℂ simultaneously. -/
theorem cauchy_schwarz_eq_iff {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (u v : E) (hv : v ≠ 0) :
    ‖⟪u, v⟫_𝕜‖ = ‖u‖ * ‖v‖ ↔ ∃ c : 𝕜, u = c • v := by
  constructor
  · exact cs_equality_implies_smul u v hv
  · rintro ⟨c, rfl⟩
    exact cs_equality_of_smul v c

-- ============================================================
-- PART V: Edge Cases and Symmetry
-- ============================================================

/-- When v = 0, CS equality holds trivially (both sides are 0) -/
theorem cs_equality_zero_right {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (u : E) : ‖⟪u, (0 : E)⟫_𝕜‖ = ‖u‖ * ‖(0 : E)‖ := by
  simp [inner_zero_right, norm_zero, mul_zero]

/-- When u = 0, CS equality holds trivially -/
theorem cs_equality_zero_left {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (v : E) : ‖⟪(0 : E), v⟫_𝕜‖ = ‖(0 : E)‖ * ‖v‖ := by
  simp [inner_zero_left, norm_zero, zero_mul]

/-- Symmetric version: ‖⟪u,v⟫‖ = ‖u‖·‖v‖ ↔ ∃ c, v = c • u (for u ≠ 0) -/
theorem cauchy_schwarz_eq_iff_symm {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (u v : E) (hu : u ≠ 0) :
    ‖⟪u, v⟫_𝕜‖ = ‖u‖ * ‖v‖ ↔ ∃ c : 𝕜, v = c • u := by
  have hnorm_swap : ‖⟪u, v⟫_𝕜‖ = ‖⟪v, u⟫_𝕜‖ := by
    conv_lhs => rw [← RCLike.norm_conj, inner_conj_symm]
  rw [hnorm_swap, mul_comm]
  exact cauchy_schwarz_eq_iff v u hu

-- ============================================================
-- PART VI: Summary
-- ============================================================

/-- Summary: CS equality works uniformly for both ℝ and ℂ -/
theorem cauchy_schwarz_equality_works_for_complex :
    -- Complex version
    (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      (u v : E) (hv : v ≠ 0),
      ‖⟪u, v⟫_ℂ‖ = ‖u‖ * ‖v‖ ↔ ∃ c : ℂ, u = c • v) ∧
    -- Uniform RCLike version
    (∀ {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
       [InnerProductSpace 𝕜 E] (u v : E) (hv : v ≠ 0),
      ‖⟪u, v⟫_𝕜‖ = ‖u‖ * ‖v‖ ↔ ∃ c : 𝕜, u = c • v) :=
  ⟨fun u v hv => cauchy_schwarz_eq_iff_complex u v hv,
   fun u v hv => cauchy_schwarz_eq_iff u v hv⟩

end CauchySchwarzOQ01OQ01
