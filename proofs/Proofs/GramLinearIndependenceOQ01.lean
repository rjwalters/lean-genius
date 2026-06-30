import Mathlib

/-!
# The Gram matrix, positive definiteness, and the Gramian determinant criterion

For a finite family of vectors `v : n → E` in an inner product space over `𝕜` (`ℝ` or
`ℂ`), the **Gram matrix** `gram 𝕜 v` has entries `⟪v i, v j⟫`. Mathlib proves the
headline characterisation

* `Matrix.posDef_gram_iff_linearIndependent` : `gram 𝕜 v` is positive definite **iff**
  the family `v` is linearly independent,

together with the structural facts that a Gram matrix is always Hermitian
(`isHermitian_gram`) and positive semidefinite (`posSemidef_gram`). This file re-exports
those (hence the `mathlib` badge on the headline) and then derives the genuine content
absent from Mathlib: the classical **Gramian determinant test**.

The Gram determinant `det (gram 𝕜 v)` (the *Gramian*) is the standard numerical witness
for linear independence. We prove:

* `gram_det_nonneg` — the Gramian is always `≥ 0` (it is the determinant of a positive
  semidefinite matrix);
* `gram_mulVec_eq_zero_of_dependent` — a linear dependence `∑ gⱼ • vⱼ = 0` is exactly a
  null vector of the Gram matrix (`gram 𝕜 v *ᵥ g = 0`), the elementary kernel identity
  `(gram 𝕜 v *ᵥ g) i = ⟪v i, ∑ gⱼ • vⱼ⟫`;
* `gram_det_eq_zero_of_not_linearIndependent` — a dependent family has a **singular** Gram
  matrix (Gramian `= 0`), obtained from the kernel identity via
  `Matrix.exists_mulVec_eq_zero_iff`;
* `linearIndependent_iff_gram_det_pos` — `v` is linearly independent **iff** its Gramian
  is strictly positive;
* the corollaries `gram_det_eq_zero_iff_not_linearIndependent` (Gramian vanishes iff
  dependent) and `linearIndependent_iff_gram_det_ne_zero`.

Everything is stated over an arbitrary `RCLike` field `𝕜`, so it applies uniformly to real
and complex inner product spaces. All results are fully machine-checked with no `sorry`
and no extra axioms.
-/

namespace GramLinearIndependenceOQ01

open Matrix RCLike
open scoped ComplexOrder InnerProductSpace

variable {𝕜 E n : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype n] [DecidableEq n]

/-! ## Re-exported Mathlib facts -/

/-- **Gram positive-definiteness criterion** (Mathlib `posDef_gram_iff_linearIndependent`):
the Gram matrix of `v` is positive definite iff `v` is linearly independent. -/
theorem posDef_gram_iff_linearIndependent (v : n → E) :
    (gram 𝕜 v).PosDef ↔ LinearIndependent 𝕜 v :=
  Matrix.posDef_gram_iff_linearIndependent

/-- A Gram matrix is always Hermitian. -/
theorem gram_isHermitian (v : n → E) : (gram 𝕜 v).IsHermitian :=
  Matrix.isHermitian_gram 𝕜 v

/-- A Gram matrix is always positive semidefinite. -/
theorem gram_posSemidef (v : n → E) : (gram 𝕜 v).PosSemidef :=
  Matrix.posSemidef_gram 𝕜 v

/-! ## The Gramian determinant test (new content) -/

/-- The **Gramian** (Gram determinant) is always nonnegative: it is the determinant of a
positive semidefinite matrix. -/
theorem gram_det_nonneg (v : n → E) : 0 ≤ (gram 𝕜 v).det :=
  (Matrix.posSemidef_gram 𝕜 v).det_nonneg

/-- **Kernel identity.** A linear dependence `∑ j, g j • v j = 0` is precisely a null
vector of the Gram matrix. The proof is the one-line computation
`(gram 𝕜 v *ᵥ g) i = ⟪v i, ∑ j, g j • v j⟫`, using that the inner product is linear in
its second argument. -/
theorem gram_mulVec_eq_zero_of_dependent {v : n → E} {g : n → 𝕜}
    (hg : ∑ i, g i • v i = 0) : gram 𝕜 v *ᵥ g = 0 := by
  funext i
  have key : (gram 𝕜 v *ᵥ g) i = ⟪v i, ∑ j, g j • v j⟫_𝕜 := by
    simp only [mulVec, dotProduct, Matrix.gram_apply, inner_sum, inner_smul_right]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [Pi.zero_apply, key, hg, inner_zero_right]

/-- A linearly **dependent** family has a singular Gram matrix: its Gramian vanishes. -/
theorem gram_det_eq_zero_of_not_linearIndependent {v : n → E}
    (h : ¬ LinearIndependent 𝕜 v) : (gram 𝕜 v).det = 0 := by
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp h
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  exact ⟨g, fun hgz => hi (by rw [hgz]; rfl), gram_mulVec_eq_zero_of_dependent hg⟩

/-- **Gramian determinant criterion.** A finite family of vectors is linearly independent
iff its Gram determinant is strictly positive. -/
theorem linearIndependent_iff_gram_det_pos (v : n → E) :
    LinearIndependent 𝕜 v ↔ 0 < (gram 𝕜 v).det := by
  constructor
  · intro h
    exact ((posDef_gram_iff_linearIndependent v).mpr h).det_pos
  · intro h
    by_contra hni
    rw [gram_det_eq_zero_of_not_linearIndependent hni] at h
    exact lt_irrefl 0 h

/-- The Gramian vanishes **iff** the family is linearly dependent. -/
theorem gram_det_eq_zero_iff_not_linearIndependent (v : n → E) :
    (gram 𝕜 v).det = 0 ↔ ¬ LinearIndependent 𝕜 v := by
  constructor
  · intro h hli
    have hpos := (linearIndependent_iff_gram_det_pos v).mp hli
    rw [h] at hpos
    exact lt_irrefl 0 hpos
  · exact gram_det_eq_zero_of_not_linearIndependent

/-- Linear independence is equivalent to a nonzero Gramian. -/
theorem linearIndependent_iff_gram_det_ne_zero (v : n → E) :
    LinearIndependent 𝕜 v ↔ (gram 𝕜 v).det ≠ 0 := by
  rw [Ne, gram_det_eq_zero_iff_not_linearIndependent, not_not]

end GramLinearIndependenceOQ01
