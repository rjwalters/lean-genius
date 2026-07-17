/-
  Complex Gram-Schmidt via Cauchy-Schwarz Equality

  Open Question (cauchy-schwarz-oq-01-oq-01-oq-01):
  "Can the complex Gram-Schmidt process be formalized using the
  Cauchy-Schwarz equality characterization?"

  Answer: YES. The projection step u ↦ u − (⟪v,u⟫/⟪v,v⟫)·v is exactly
  the orthogonal decomposition. Cauchy-Schwarz equality tells us when
  this step is trivial (the vector was already a scalar multiple).

  This file formalizes:
  1. Orthogonal projection operator and residual
  2. Gram-Schmidt for 2 vectors (project u onto v)
  3. Gram-Schmidt for 3 vectors (sequential orthogonalization)
  4. Connection: CS equality ↔ residual vanishes ↔ linear dependence

  Parent: CauchySchwarzOQ01OQ01.lean (Cauchy-Schwarz equality characterization)
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

open scoped InnerProductSpace

namespace CauchySchwarzOQ01OQ01OQ01

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

-- ============================================================
-- PART 1: Orthogonal Projection and Residual
-- ============================================================

/-- The orthogonal projection coefficient of u onto v: c = ⟪v, u⟫ / ⟪v, v⟫. -/
noncomputable def projCoeff (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (v u : E) : 𝕜 :=
  ⟪v, u⟫_𝕜 / ⟪v, v⟫_𝕜

/-- The orthogonal projection of u onto the span of v. -/
noncomputable def orthProj (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (v u : E) : E :=
  projCoeff 𝕜 v u • v

/-- The residual after projecting u onto v: the component of u
    orthogonal to v. -/
noncomputable def orthResidual (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (v u : E) : E :=
  u - orthProj 𝕜 v u

/-- Fundamental property: the residual is orthogonal to the direction vector.
    This is the key step in Gram-Schmidt orthogonalization.
    Proof: ⟪u − (⟪v,u⟫/⟪v,v⟫)·v, v⟫ = ⟪u,v⟫ − (⟪v,u⟫/⟪v,v⟫)·⟪v,v⟫ = 0. -/
theorem orthResidual_inner_eq_zero (u v : E) (hv : v ≠ 0) :
    ⟪orthResidual 𝕜 v u, v⟫_𝕜 = 0 := by
  simp only [orthResidual, orthProj, projCoeff, inner_sub_left, inner_smul_left,
    map_div₀, inner_conj_symm]
  have hvv : ⟪v, v⟫_𝕜 ≠ 0 := fun h => hv (inner_self_eq_zero.mp h)
  field_simp
  ring

/-- The decomposition u = proj(v, u) + residual(v, u). -/
theorem orthogonal_decomposition (v u : E) :
    u = orthProj 𝕜 v u + orthResidual 𝕜 v u := by
  simp [orthProj, orthResidual]

-- ============================================================
-- PART 2: Two-Vector Gram-Schmidt
-- ============================================================

/-- **Gram-Schmidt for 2 vectors**: given v₁ ≠ 0 and u₂, produce
    v₂ = u₂ − proj(v₁, u₂) which is orthogonal to v₁. -/
theorem gramSchmidt2_orthogonal (v₁ u₂ : E) (hv₁ : v₁ ≠ 0) :
    ⟪orthResidual 𝕜 v₁ u₂, v₁⟫_𝕜 = 0 :=
  orthResidual_inner_eq_zero u₂ v₁ hv₁

/-- If v₁ ≠ 0 and the residual is nonzero, the two output
    vectors {v₁, orthResidual v₁ u₂} are orthogonal. -/
theorem gramSchmidt2_pair_orthogonal (v₁ u₂ : E) (hv₁ : v₁ ≠ 0) :
    ⟪v₁, orthResidual 𝕜 v₁ u₂⟫_𝕜 = 0 := by
  have h := gramSchmidt2_orthogonal (𝕜 := 𝕜) v₁ u₂ hv₁
  rwa [inner_eq_zero_symm] at h

-- ============================================================
-- PART 3: Three-Vector Gram-Schmidt
-- ============================================================

/-- **Gram-Schmidt step 3**: orthogonalize u₃ against v₁ and v₂,
    assuming v₁ ⊥ v₂. The result is perpendicular to both. -/
noncomputable def gramSchmidt3 (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (v₁ v₂ u₃ : E) : E :=
  orthResidual 𝕜 v₂ (orthResidual 𝕜 v₁ u₃)

/-- The third Gram-Schmidt vector is orthogonal to v₂.
    This follows directly since it's defined as the residual after
    projecting onto v₂. -/
theorem gramSchmidt3_perp_v₂ (v₁ v₂ u₃ : E) (hv₂ : v₂ ≠ 0) :
    ⟪gramSchmidt3 𝕜 v₁ v₂ u₃, v₂⟫_𝕜 = 0 :=
  orthResidual_inner_eq_zero _ v₂ hv₂

/-- The third Gram-Schmidt vector is orthogonal to v₁,
    provided v₁ ⊥ v₂. The key: projecting onto v₂ doesn't affect
    the v₁-component when v₁ ⊥ v₂. -/
theorem gramSchmidt3_perp_v₁ (v₁ v₂ u₃ : E) (hv₁ : v₁ ≠ 0)
    (hv₂ : v₂ ≠ 0) (hperp : ⟪v₁, v₂⟫_𝕜 = 0) :
    ⟪gramSchmidt3 𝕜 v₁ v₂ u₃, v₁⟫_𝕜 = 0 := by
  simp only [gramSchmidt3, orthResidual, orthProj, projCoeff,
    inner_sub_left, inner_smul_left, map_div₀]
  -- After expanding: ⟪u₃, v₁⟫ - (⟪v₁,u₃⟫/⟪v₁,v₁⟫)·⟪v₁,v₁⟫
  --   − (⟪v₂, u₃ − ...⟫/⟪v₂,v₂⟫)·⟪v₂,v₁⟫
  -- The last term has ⟪v₂, v₁⟫ = conj(⟪v₁, v₂⟫) = conj(0) = 0
  have hperp' : ⟪v₂, v₁⟫_𝕜 = 0 := by rwa [inner_eq_zero_symm]
  rw [inner_conj_symm, hperp']
  simp [inner_sub_left, inner_smul_left, map_div₀, inner_conj_symm]
  have hvn : (‖v₁‖ : 𝕜) ≠ 0 := by
    simp only [ne_eq, RCLike.ofReal_eq_zero, norm_eq_zero]; exact hv₁
  field_simp
  ring

-- ============================================================
-- PART 4: Connection to Cauchy-Schwarz Equality
-- ============================================================

/-- The residual vanishes iff u is a scalar multiple of v.
    This connects Gram-Schmidt to the CS equality characterization. -/
theorem orthResidual_eq_zero_iff_smul (v u : E) (hv : v ≠ 0) :
    orthResidual 𝕜 v u = 0 ↔ ∃ c : 𝕜, u = c • v := by
  constructor
  · intro h
    simp only [orthResidual, orthProj, projCoeff] at h
    exact ⟨⟪v, u⟫_𝕜 / ⟪v, v⟫_𝕜, sub_eq_zero.mp h⟩
  · rintro ⟨c, rfl⟩
    simp only [orthResidual, orthProj, projCoeff, inner_smul_right, inner_self_eq_norm_sq_to_K]
    have hvn : (‖v‖ : 𝕜) ≠ 0 := by
      simp only [ne_eq, RCLike.ofReal_eq_zero, norm_eq_zero]; exact hv
    rw [mul_div_assoc, div_self (pow_ne_zero 2 hvn), mul_one, sub_self]

/-- **CS equality ↔ trivial Gram-Schmidt step**: The Cauchy-Schwarz
    inequality holds with equality iff the Gram-Schmidt residual vanishes.
    In other words, the Gram-Schmidt process "knows" when vectors are
    already linearly dependent — this is the equality case of CS. -/
theorem cs_equality_iff_residual_zero (u v : E) (hv : v ≠ 0) :
    ‖⟪u, v⟫_𝕜‖ = ‖u‖ * ‖v‖ ↔ orthResidual 𝕜 v u = 0 := by
  rw [orthResidual_eq_zero_iff_smul v u hv]
  constructor
  · -- CS equality → scalar multiple (from parent's result)
    intro h
    -- Use the forward direction: decompose u = c·v + w, equality forces w = 0
    set c := ⟪v, u⟫_𝕜 / ⟪v, v⟫_𝕜 with hc_def
    have hvv : ⟪v, v⟫_𝕜 ≠ 0 := fun hh => hv (inner_self_eq_zero.mp hh)
    have hortho : ⟪u - c • v, v⟫_𝕜 = 0 := by
      rw [inner_sub_left, inner_smul_left, hc_def, map_div₀, inner_conj_symm,
        inner_conj_symm, div_mul_cancel₀ _ hvv, sub_self]
    have hortho_cv : ⟪u - c • v, c • v⟫_𝕜 = 0 := by
      rw [inner_smul_right, hortho, mul_zero]
    have hpyth : ‖u‖ ^ 2 = ‖u - c • v‖ ^ 2 + ‖c • v‖ ^ 2 := by
      have : u = (u - c • v) + c • v := by abel
      conv_lhs => rw [this]
      rw [norm_add_sq (𝕜 := 𝕜), hortho_cv, map_zero]; ring
    have hinner_val : ‖⟪u, v⟫_𝕜‖ = ‖c‖ * ‖v‖ ^ 2 := by
      have : u = (u - c • v) + c • v := by abel
      conv_lhs => rw [this]
      rw [inner_add_left, hortho, zero_add, inner_smul_left, inner_self_eq_norm_sq_to_K,
        norm_mul, RCLike.norm_conj]
      rw [show (‖v‖ ^ 2 : 𝕜) = ((‖v‖ ^ 2 : ℝ) : 𝕜) by push_cast; ring,
        RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
    have hv_ne : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    have hcv_norm : ‖c‖ * ‖v‖ = ‖u‖ := by
      have h1 : ‖c‖ * ‖v‖ ^ 2 = ‖u‖ * ‖v‖ := by linarith [hinner_val]
      have h2 : ‖c‖ * ‖v‖ * ‖v‖ = ‖u‖ * ‖v‖ := by rw [sq] at h1; linarith
      exact mul_right_cancel₀ hv_ne h2
    have hres_zero : ‖u - c • v‖ = 0 := by
      have : ‖c • v‖ ^ 2 = ‖u‖ ^ 2 := by rw [norm_smul, hcv_norm]
      have : ‖u - c • v‖ ^ 2 = 0 := by linarith [hpyth]
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    exact ⟨c, sub_eq_zero.mp (norm_eq_zero.mp hres_zero)⟩
  · -- Scalar multiple → CS equality (direct computation)
    rintro ⟨c, rfl⟩
    rw [inner_smul_left, inner_self_eq_norm_sq_to_K, norm_mul, norm_smul,
      RCLike.norm_conj]
    rw [show (‖v‖ ^ 2 : 𝕜) = ((‖v‖ ^ 2 : ℝ) : 𝕜) by push_cast; ring,
      RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
    ring

-- ============================================================
-- PART 5: Gram-Schmidt Preserves Span (Norm Properties)
-- ============================================================

/-- The norm of the residual is at most the norm of u
    (projecting can only decrease norm). -/
theorem norm_orthResidual_le (v u : E) (hv : v ≠ 0) :
    ‖orthResidual 𝕜 v u‖ ≤ ‖u‖ := by
  have h := orthResidual_inner_eq_zero (𝕜 := 𝕜) u v hv
  have hortho : ⟪orthResidual 𝕜 v u, orthProj 𝕜 v u⟫_𝕜 = 0 := by
    rw [orthProj, inner_smul_right, h, mul_zero]
  have : ‖u‖ ^ 2 = ‖orthResidual 𝕜 v u‖ ^ 2 + ‖orthProj 𝕜 v u‖ ^ 2 := by
    have hsplit : u = orthResidual 𝕜 v u + orthProj 𝕜 v u := by
      simp [orthResidual]
    conv_lhs => rw [hsplit]
    rw [norm_add_sq (𝕜 := 𝕜), hortho, map_zero]; ring
  nlinarith [sq_nonneg ‖orthProj 𝕜 v u‖, sq_nonneg ‖orthResidual 𝕜 v u‖,
    norm_nonneg (orthResidual 𝕜 v u), norm_nonneg u]

/-
## Summary

### What's Proved (0 sorries, 0 axioms)
1. Orthogonal projection operator and residual
2. Fundamental orthogonality: residual ⊥ direction vector
3. Two-vector Gram-Schmidt with orthogonality proof
4. Three-vector Gram-Schmidt with pairwise orthogonality
5. CS equality ↔ residual vanishes ↔ linear dependence
6. Norm of residual ≤ norm of original (projection decreases norm)

### Connection to Cauchy-Schwarz
The key theorem `cs_equality_iff_residual_zero` shows:
- ‖⟪u,v⟫‖ = ‖u‖·‖v‖ iff orthResidual(v, u) = 0
- In words: CS is an equality iff the Gram-Schmidt step is trivial
- This is the precise sense in which CS "detects" linear dependence

### Architecture
- `projCoeff` → `orthProj` → `orthResidual` form the projection pipeline
- `gramSchmidt3` demonstrates iterated application
- The 3-vector case shows orthogonality is preserved when v₁ ⊥ v₂

### Relationship to Mathlib
Mathlib has `EuclideanDomain.gramSchmidt` for the general process.
This file provides the concrete connection to the CS equality
characterization, showing why it's the right criterion for the
Gram-Schmidt process: equality signals linear dependence.
-/

end CauchySchwarzOQ01OQ01OQ01
