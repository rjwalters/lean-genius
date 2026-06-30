/-
  Cauchy-Schwarz for Finite Families: The Gram Determinant Criterion
  Open Question: cauchy-schwarz-oq-06-oq-01

  The parent entry (cauchy-schwarz-oq-06) characterized the EQUALITY case of the
  Cauchy-Schwarz inequality for a PAIR `{x, y}`: equality `‖⟪x, y⟫‖ = ‖x‖ · ‖y‖`
  holds iff the pair is linearly DEPENDENT.  This file lifts that dichotomy from
  two vectors to an arbitrary FINITE family `v : n → E`, replacing the scalar
  Cauchy-Schwarz gap by the **Gram determinant**:

      det (Gram v) = 0   ↔   the family `{vᵢ}` is linearly DEPENDENT,

  equivalently `det (Gram v) ≠ 0 ↔ {vᵢ}` is linearly independent, where the Gram
  matrix is `Gᵢⱼ = ⟪vᵢ, vⱼ⟫`.  For `n = 2` the Gram determinant is exactly
  `‖x‖² ‖y‖² − ‖⟪x, y⟫‖²`, the squared Cauchy-Schwarz gap, so the parent's
  equality case is the two-dimensional slice of this statement.

  Strategy — two short bridges over Mathlib's `Matrix.gram` API:

  * Independence ⟹ det ≠ 0.  `posDef_gram_of_linearIndependent` makes the Gram
    matrix positive definite; a positive-definite matrix over a field is a unit
    (`Matrix.PosDef.isUnit`), so its determinant is a unit and therefore nonzero.

  * Dependence ⟹ det = 0.  A nontrivial vanishing combination `∑ cᵢ vᵢ = 0` is a
    *nonzero null vector* of the Gram matrix: `(G *ᵥ c) j = ⟪vⱼ, ∑ cᵢ vᵢ⟫ = 0`
    by linearity of the inner product in its second slot.  A matrix with a
    nonzero kernel vector has zero determinant
    (`Matrix.exists_mulVec_eq_zero_iff`).

  These combine into the biconditionals
  `gram_det_ne_zero_iff_linearIndependent` and
  `gram_det_eq_zero_iff_not_linearIndependent`.

  References:
  - J. P. Gram, "Über die Entwicklung reeller Functionen in Reihen…" (1883):
    the Gram determinant / Gramian.
  - Horn & Johnson, "Matrix Analysis" (2nd ed., 2013), §7.2 (Gram matrices).
  - Mathlib `Mathlib/Analysis/InnerProductSpace/GramMatrix.lean`:
    `Matrix.gram`, `Matrix.posSemidef_gram`,
    `Matrix.posDef_gram_iff_linearIndependent`.
-/

import Mathlib

namespace CauchySchwarzOQ06OQ01

open scoped InnerProductSpace ComplexOrder
open Matrix

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {n : Type*} [Fintype n] [DecidableEq n]

-- ============================================================================
-- Part I: Linear independence ⟹ nonvanishing Gram determinant
-- ============================================================================

/-- **Independence ⟹ nonsingular Gram matrix.** If a finite family `v` is linearly
independent then its Gram matrix is positive definite, hence a unit, hence has a
nonzero determinant. -/
theorem gram_det_ne_zero_of_linearIndependent
    {v : n → E} (h : LinearIndependent 𝕜 v) :
    (gram 𝕜 v).det ≠ 0 := by
  have hpd : (gram 𝕜 v).PosDef := posDef_gram_of_linearIndependent h
  have hunit : IsUnit (gram 𝕜 v).det := (isUnit_iff_isUnit_det _).mp hpd.isUnit
  exact hunit.ne_zero

-- ============================================================================
-- Part II: Linear dependence ⟹ vanishing Gram determinant
-- ============================================================================

omit [DecidableEq n] in
/-- The Gram matrix sends a coefficient vector `c` to the vector of inner products
of each `vⱼ` with the combination `∑ cᵢ vᵢ`. This is the linearity-of-the-inner-
product computation underlying the kernel argument. -/
theorem gram_mulVec_apply (v : n → E) (c : n → 𝕜) (j : n) :
    (gram 𝕜 v *ᵥ c) j = ⟪v j, ∑ k, c k • v k⟫_𝕜 := by
  simp only [mulVec, dotProduct, gram_apply, inner_sum, inner_smul_right]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **Dependence ⟹ singular Gram matrix.** If a finite family `v` is linearly
dependent, a nontrivial vanishing combination is a nonzero kernel vector of the
Gram matrix, so the determinant vanishes. -/
theorem gram_det_eq_zero_of_not_linearIndependent
    {v : n → E} (h : ¬ LinearIndependent 𝕜 v) :
    (gram 𝕜 v).det = 0 := by
  obtain ⟨c, hsum, i, hi⟩ := Fintype.not_linearIndependent_iff.mp h
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨c, fun hc => hi (by simp [hc]), ?_⟩
  funext j
  rw [Pi.zero_apply, gram_mulVec_apply, hsum, inner_zero_right]

-- ============================================================================
-- Part III: The Gram determinant dichotomy
-- ============================================================================

/-- **Gram determinant criterion (nonvanishing form).** A finite family of vectors
in an inner-product space is linearly independent iff its Gram determinant is
nonzero. The classical `n = 2` Gram determinant `‖x‖²‖y‖² − ‖⟪x,y⟫‖²` recovers
the parent's pairwise equality case. -/
theorem gram_det_ne_zero_iff_linearIndependent {v : n → E} :
    (gram 𝕜 v).det ≠ 0 ↔ LinearIndependent 𝕜 v := by
  refine ⟨fun hdet => ?_, gram_det_ne_zero_of_linearIndependent⟩
  by_contra hli
  exact hdet (gram_det_eq_zero_of_not_linearIndependent hli)

/-- **Gram determinant criterion (vanishing form).** A finite family of vectors in
an inner-product space is linearly DEPENDENT iff its Gram determinant vanishes —
the finite-family generalization of the Cauchy-Schwarz equality case. -/
theorem gram_det_eq_zero_iff_not_linearIndependent {v : n → E} :
    (gram 𝕜 v).det = 0 ↔ ¬ LinearIndependent 𝕜 v := by
  rw [← not_ne_iff (a := (gram 𝕜 v).det), gram_det_ne_zero_iff_linearIndependent]

end CauchySchwarzOQ06OQ01
