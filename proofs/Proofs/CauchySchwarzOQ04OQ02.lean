/-
  Cauchy-Schwarz Equality: the rank-one projection is Mathlib's orthogonal (star) projection
  Open Question: cauchy-schwarz-oq-04-oq-02

  The parent entry (cauchy-schwarz-oq-04) hand-rolls a one-dimensional projection
      projCoeff u v = ⟪u, v⟫ / ‖v‖²,     proj u v = projCoeff u v • v
  and proves, by ad-hoc computation, that the residual u − proj u v is orthogonal to v,
  the Pythagorean split ‖u‖² = (projCoeff u v)²‖v‖² + ‖u − proj u v‖², and that Cauchy–
  Schwarz equality forces u = proj u v.

  This entry answers the parent's open question: *connect the projection coefficient to
  Mathlib's orthogonal projection for Hilbert subspaces.* The central bridge

      proj u v = (ℝ ∙ v).starProjection u

  identifies the ad-hoc rank-one map with the genuine orthogonal projection onto the line
  `ℝ ∙ v` (`starProjection` is Mathlib's `E`-valued orthogonal projection; the subspace-valued
  `orthogonalProjection` coerces to it). Once this identity is in place, every property the parent
  proved by hand becomes a specialization of Mathlib's general Hilbert-space projection theory:

    * the residual lies in the orthogonal complement `(ℝ ∙ v)ᗮ`  (not merely ⟂ v);
    * the projection lands in `ℝ ∙ v` and fixes exactly the elements of the line;
    * Cauchy–Schwarz equality ⟺ `u ∈ ℝ ∙ v` ⟺ `(ℝ ∙ v).starProjection u = u`;
    * Bessel `‖(ℝ ∙ v).starProjection u‖ ≤ ‖u‖` recovers the Cauchy–Schwarz bound.

  Mathlib records the singleton projection only through `starProjection_singleton` with argument
  order ⟪v, u⟫; the parent's coefficient uses ⟪u, v⟫, so the bridge is the real-symmetry
  `real_inner_comm` reconciliation, after which the two theories coincide.

  References:
  - Steele, "The Cauchy-Schwarz Master Class" (2004), Ch. 2 (projection viewpoint)
  - Mathlib.Analysis.InnerProductSpace.Projection.Basic (`starProjection_singleton`)
  - Parent: CauchySchwarzOQ04.lean (ad-hoc `projCoeff` / `proj`)
-/

import Mathlib

namespace CauchySchwarzOQ04OQ02

open scoped InnerProductSpace RealInnerProductSpace
open Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- ============================================================================
-- Part I: The parent's ad-hoc rank-one projection
-- ============================================================================

/-- The orthogonal projection coefficient of `u` onto `v` (matches the parent entry). -/
noncomputable def projCoeff (u v : E) : ℝ := ⟪u, v⟫_ℝ / ‖v‖ ^ 2

/-- The rank-one projection of `u` onto the line spanned by `v` (matches the parent). -/
noncomputable def proj (u v : E) : E := projCoeff u v • v

-- ============================================================================
-- Part II: The bridge to Mathlib's orthogonal projection
-- ============================================================================

/-- **Central bridge.** The parent's ad-hoc rank-one map `proj u v` is exactly Mathlib's
orthogonal projection of `u` onto the line `ℝ ∙ v`. The only discrepancy between the two
definitions is the argument order of the real inner product, reconciled by `real_inner_comm`. -/
theorem proj_eq_starProjection (u v : E) :
    proj u v = (ℝ ∙ v).starProjection u := by
  rw [starProjection_singleton, proj, projCoeff, real_inner_comm]
  simp only [RCLike.ofReal_real_eq_id, id_eq]

/-- The projection coefficient is the coordinate of `(ℝ ∙ v).starProjection u` along `v`. -/
theorem starProjection_eq_projCoeff_smul (u v : E) :
    (ℝ ∙ v).starProjection u = projCoeff u v • v := by
  rw [← proj_eq_starProjection]; rfl

-- ============================================================================
-- Part III: Consequences inherited from Mathlib's projection theory
-- ============================================================================

/-- The projection lands in the line `ℝ ∙ v`. -/
theorem proj_mem_span (u v : E) : proj u v ∈ (ℝ ∙ v) := by
  rw [proj_eq_starProjection]; exact starProjection_apply_mem _ u

/-- **Residual lies in the orthogonal complement.** The parent proved only `⟪u − proj u v, v⟫ = 0`;
via the bridge the residual lies in the full complement `(ℝ ∙ v)ᗮ`, i.e. is orthogonal to *every*
element of the line, not just to `v`. -/
theorem residual_mem_orthogonal (u v : E) :
    u - proj u v ∈ (ℝ ∙ v)ᗮ := by
  rw [proj_eq_starProjection]
  exact sub_starProjection_mem_orthogonal u

/-- Recovers the parent's orthogonality `⟪u − proj u v, v⟫ = 0` from the complement membership. -/
theorem residual_inner_eq_zero (u v : E) : ⟪u - proj u v, v⟫_ℝ = 0 := by
  have h := residual_mem_orthogonal u v
  rw [Submodule.mem_orthogonal] at h
  have := h v (Submodule.mem_span_singleton_self v)
  rwa [real_inner_comm] at this

/-- The projection fixes exactly the elements already on `ℝ ∙ v`. -/
theorem proj_of_mem_span {u v : E} (hu : u ∈ (ℝ ∙ v)) : proj u v = u := by
  rw [proj_eq_starProjection]; exact starProjection_eq_self_iff.mpr hu

-- ============================================================================
-- Part IV: Cauchy-Schwarz equality as a projection statement
-- ============================================================================

/-- **Cauchy–Schwarz equality ⟺ collinearity ⟺ projection fixes `u`.** The parent obtained the
forward implication (equality ⟹ `u = proj u v`) by an explicit residual-norm computation. Here the
formulations are unified through the orthogonal-projection bridge: `u` is fixed by the projection
onto `ℝ ∙ v` exactly when `u` lies on the line. -/
theorem proj_fixes_iff_mem_span (u v : E) :
    proj u v = u ↔ u ∈ (ℝ ∙ v) := by
  rw [proj_eq_starProjection]; exact starProjection_eq_self_iff

-- ============================================================================
-- Part V: Norm identities (Bessel and Pythagoras via Mathlib)
-- ============================================================================

/-- The norm of the projection in closed form. -/
theorem norm_proj (u v : E) : ‖proj u v‖ = |projCoeff u v| * ‖v‖ := by
  rw [proj, norm_smul, Real.norm_eq_abs]

/-- **Bessel / Cauchy–Schwarz bound.** The projection never lengthens `u`; specialized to the
line this *is* the Cauchy–Schwarz inequality `|⟪u, v⟫| ≤ ‖u‖ ‖v‖`. -/
theorem norm_proj_le (u v : E) : ‖proj u v‖ ≤ ‖u‖ := by
  rw [proj_eq_starProjection]
  exact (ℝ ∙ v).norm_starProjection_apply_le u

/-- **Pythagoras via Mathlib.** `‖u‖² = ‖proj u v‖² + ‖u − proj u v‖²`: the projection and the
residual are orthogonal, so the norm splits. This is the parent's `norm_sq_decomposition`, now a
direct consequence of the residual lying in `(ℝ ∙ v)ᗮ`. -/
theorem norm_sq_split (u v : E) :
    ‖u‖ ^ 2 = ‖proj u v‖ ^ 2 + ‖u - proj u v‖ ^ 2 := by
  have horth : ⟪proj u v, u - proj u v⟫_ℝ = 0 := by
    have hmem := residual_mem_orthogonal u v
    rw [Submodule.mem_orthogonal] at hmem
    exact hmem (proj u v) (proj_mem_span u v)
  have hpyth := norm_add_sq_real (proj u v) (u - proj u v)
  rw [horth] at hpyth
  have huv : proj u v + (u - proj u v) = u := by abel
  rw [huv] at hpyth
  linarith [hpyth]

/-- Cauchy–Schwarz equality forces `u` to be fixed by the projection (parent's forward direction,
re-derived through the bridge). The residual norm is squeezed to zero via the Pythagorean split. -/
theorem cs_equality_proj_fixes (u v : E) (hv : v ≠ 0)
    (h : |⟪u, v⟫_ℝ| = ‖u‖ * ‖v‖) : proj u v = u := by
  have hvne : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  -- The projection has the same norm as `u`.
  have hnp : ‖proj u v‖ = ‖u‖ := by
    rw [norm_proj]
    unfold projCoeff
    rw [abs_div, h, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖v‖ ^ 2)]
    field_simp
  -- Pythagoras then forces the residual to vanish.
  have hsplit := norm_sq_split u v
  rw [hnp] at hsplit
  have hz : ‖u - proj u v‖ ^ 2 = 0 := by linarith
  have hzero : u - proj u v = 0 := by
    have : ‖u - proj u v‖ = 0 := by nlinarith [norm_nonneg (u - proj u v)]
    rwa [norm_eq_zero] at this
  exact (sub_eq_zero.mp hzero).symm

-- ============================================================================
-- Part VI: Concrete sanity check over the base field ℝ
-- ============================================================================

/-- A concrete instance over `E = ℝ` (with `⟪x, y⟫ = x·y`): projecting `6` onto the line `ℝ ∙ 3`
returns `6`, since every real already lies on that line. -/
example : proj (6 : ℝ) 3 = 6 := by
  apply proj_of_mem_span
  rw [Submodule.mem_span_singleton]
  exact ⟨2, by norm_num⟩
