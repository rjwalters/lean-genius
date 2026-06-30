import Mathlib

/-!
# The `k`-dimensional content: `√(det gram v)` as a product of Gram–Schmidt heights

For a finite family of vectors `v : Fin n → F` in a real inner product space `F`, the
grandparent entry `gram-linear-independence-iff-oq-01` proved the **Gramian criterion**
(`det (gram ℝ v) ≥ 0`, with equality iff `v` is dependent), and the sibling entry
`…-oq-01-oq-02` identified `√(det gram v)` with the parallelepiped volume in the **square**
case, where the vectors *fill* the ambient space (`finrank ℝ F = n`).

This entry removes the `finrank = n` hypothesis, supplying the genuinely
`k`-**dimensional** content of `n` vectors sitting inside a possibly larger space.  The key
identity is the Gram–Schmidt factorization of the Gramian:

> **`det_gram_eq_prod_gramSchmidt_norm_sq`** :
> `det (gram ℝ v) = ∏ i, ‖gramSchmidt ℝ v i‖²`.

Writing `gᵢ = gramSchmidt ℝ v i` for the orthogonalized family, the number `‖gᵢ‖` is the
*height* of `vᵢ` above the span of the earlier vectors (the perpendicular distance), so the
content

> **`content_eq_prod_gramSchmidt_norm`** :
> `√(det gram v) = ∏ i, ‖gramSchmidt ℝ v i‖`

is exactly the iterated *base × height* volume of the parallelepiped — valid in any
dimension, no spanning hypothesis required.  This is the orthogonalization / exterior-power
picture of the Gramian that the parent's third open question asks for.

## Proof

Let `C` be the lower-unitriangular *change-of-basis* matrix expressing each `vᵢ` in the
orthogonal family `g` (`vᵢ = ∑ⱼ Cᵢⱼ gⱼ`, read off from `gramSchmidt_def''`), and let
`D = diagonal (‖gⱼ‖²)`.  Orthogonality of `g` gives the matrix factorization
`gram ℝ v = C · D · Cᵀ`, whence
`det (gram ℝ v) = (det C)² · det D = 1² · ∏ ‖gⱼ‖²`, since `det C = 1` (unitriangular).

## Main results

* `det_gram_eq_prod_gramSchmidt_norm_sq` — the Gram–Schmidt factorization of the Gramian.
* `content_eq_prod_gramSchmidt_norm` — content `= ∏ heights`.
* `content_nonneg`, `content_sq` — basic shape of the content.
* `content_pos_iff_linearIndependent`, `content_eq_zero_iff` — geometric independence test.

All results hold with **no** assumption relating `n` to `finrank ℝ F`, and are fully
machine-checked with no `sorry` and no extra axioms.
-/

namespace GramLinearIndependenceOQ01OQ03

open InnerProductSpace Matrix Finset
open scoped RealInnerProductSpace

noncomputable section

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The coefficient of `gⱼ = gramSchmidt ℝ v j` in the expansion of `vᵢ`.  On the diagonal
it is `1`, strictly below the diagonal (`j < i`) it is the Gram–Schmidt projection
coefficient, and strictly above the diagonal it vanishes. -/
def coeff (v : Fin n → F) (i j : Fin n) : ℝ :=
  if j < i then ⟪gramSchmidt ℝ v j, v i⟫_ℝ / ‖gramSchmidt ℝ v j‖ ^ 2
  else if j = i then 1 else 0

/-- The lower-unitriangular change-of-basis matrix `C` with `vᵢ = ∑ⱼ Cᵢⱼ gⱼ`. -/
def Cmat (v : Fin n → F) : Matrix (Fin n) (Fin n) ℝ := Matrix.of (coeff v)

/-- The diagonal matrix `D = diagonal (‖gⱼ‖²)` of squared Gram–Schmidt norms. -/
def Dmat (v : Fin n → F) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun j => ‖gramSchmidt ℝ v j‖ ^ 2)

@[simp] theorem coeff_self (v : Fin n → F) (i : Fin n) : coeff v i i = 1 := by
  simp [coeff]

theorem coeff_eq_zero_of_lt (v : Fin n → F) {i j : Fin n} (hij : i < j) :
    coeff v i j = 0 := by
  unfold coeff
  rw [if_neg (not_lt.2 hij.le), if_neg hij.ne']

/-- Each input vector is the prescribed combination of the orthogonalized family. -/
theorem v_eq_sum_coeff (v : Fin n → F) (i : Fin n) :
    v i = ∑ j, coeff v i j • gramSchmidt ℝ v j := by
  -- expand the left-hand `v i` via the Gram–Schmidt projection formula
  conv_lhs => rw [gramSchmidt_def'' ℝ v i]
  -- restrict the universal sum to `Iic i`, the support of `coeff v i ·`
  rw [← Finset.sum_subset (Finset.subset_univ (Iic i))]
  · rw [← Iio_insert, Finset.sum_insert (by simp), coeff_self, one_smul]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j < i := Finset.mem_Iio.1 hj
    simp only [coeff, if_pos hji, RCLike.ofReal_real_eq_id, id_eq]
  · intro j _ hj
    have hlt : i < j := by
      by_contra hle
      exact hj (Finset.mem_Iic.2 (not_lt.1 hle))
    rw [coeff_eq_zero_of_lt v hlt, zero_smul]

/-- The Gram-matrix factorization `gram ℝ v = C · D · Cᵀ`. -/
theorem gram_eq_cmat_dmat (v : Fin n → F) :
    gram ℝ v = Cmat v * Dmat v * (Cmat v)ᵀ := by
  ext i k
  -- the matrix product `(C · D · Cᵀ) i k` as an explicit sum
  have hrhs : (Cmat v * Dmat v * (Cmat v)ᵀ) i k
      = ∑ j, coeff v i j * coeff v k j * ‖gramSchmidt ℝ v j‖ ^ 2 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Cmat, Dmat, Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply]
    ring
  rw [gram_apply, hrhs]
  conv_lhs => rw [v_eq_sum_coeff v i, v_eq_sum_coeff v k]
  rw [sum_inner]
  -- expand each outer term and collapse the inner sum by orthogonality
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left, inner_sum, Finset.mul_sum, Finset.sum_eq_single j]
  · rw [real_inner_smul_right, real_inner_self_eq_norm_sq]; ring
  · intro l _ hl
    rw [real_inner_smul_right, gramSchmidt_orthogonal ℝ v (Ne.symm hl), mul_zero, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem det_Cmat (v : Fin n → F) : (Cmat v).det = 1 := by
  have htri : (Cmat v).BlockTriangular OrderDual.toDual := by
    intro i j hij
    rw [OrderDual.toDual_lt_toDual] at hij
    simp only [Cmat, Matrix.of_apply]
    exact coeff_eq_zero_of_lt v hij
  rw [Matrix.det_of_lowerTriangular (Cmat v) htri]
  refine Finset.prod_eq_one fun i _ => ?_
  simp [Cmat]

theorem det_Dmat (v : Fin n → F) :
    (Dmat v).det = ∏ i, ‖gramSchmidt ℝ v i‖ ^ 2 := by
  rw [Dmat, Matrix.det_diagonal]

/-- **Gram–Schmidt factorization of the Gramian.**  The Gram determinant of any finite
family of vectors equals the product of the squared norms of its Gram–Schmidt
orthogonalization — the squared `k`-dimensional content, with no spanning hypothesis. -/
theorem det_gram_eq_prod_gramSchmidt_norm_sq (v : Fin n → F) :
    (gram ℝ v).det = ∏ i, ‖gramSchmidt ℝ v i‖ ^ 2 := by
  rw [gram_eq_cmat_dmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    det_Cmat, det_Dmat, one_mul, mul_one]

/-! ## The Gramian criterion (re-derived locally from Mathlib)

These two facts are the grandparent entry `gram-linear-independence-iff-oq-01`, reproved
inline here so the file depends only on Mathlib. -/

/-- The Gramian is always nonnegative (determinant of a positive semidefinite matrix). -/
theorem gram_det_nonneg (v : Fin n → F) : 0 ≤ (gram ℝ v).det :=
  (Matrix.posSemidef_gram ℝ v).det_nonneg

/-- A family is linearly independent iff its Gramian is strictly positive. -/
theorem linearIndependent_iff_gram_det_pos (v : Fin n → F) :
    LinearIndependent ℝ v ↔ 0 < (gram ℝ v).det := by
  constructor
  · intro h
    exact ((Matrix.posDef_gram_iff_linearIndependent (v := v)).mpr h).det_pos
  · intro h
    by_contra hni
    obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hni
    have hker : gram ℝ v *ᵥ g = 0 := by
      funext j
      have key : (gram ℝ v *ᵥ g) j = ⟪v j, ∑ l, g l • v l⟫_ℝ := by
        simp only [mulVec, dotProduct, Matrix.gram_apply, inner_sum, inner_smul_right]
        exact Finset.sum_congr rfl fun l _ => mul_comm _ _
      rw [Pi.zero_apply, key, hg, inner_zero_right]
    have hdet0 : (gram ℝ v).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      exact ⟨g, fun hgz => hi (by rw [hgz]; rfl), hker⟩
    rw [hdet0] at h
    exact lt_irrefl 0 h

/-! ## The content as a product of heights -/

/-- The `k`-dimensional **content** (volume) of the parallelepiped spanned by `v`, defined
as `√(det gram v)`. -/
def content (v : Fin n → F) : ℝ := Real.sqrt (gram ℝ v).det

theorem content_nonneg (v : Fin n → F) : 0 ≤ content v := Real.sqrt_nonneg _

theorem content_sq (v : Fin n → F) : content v ^ 2 = (gram ℝ v).det := by
  rw [content, Real.sq_sqrt (gram_det_nonneg v)]

/-- **Content as a product of Gram–Schmidt heights.**  `√(det gram v) = ∏ ‖gᵢ‖`, the
iterated base × height volume. -/
theorem content_eq_prod_gramSchmidt_norm (v : Fin n → F) :
    content v = ∏ i, ‖gramSchmidt ℝ v i‖ := by
  rw [content, det_gram_eq_prod_gramSchmidt_norm_sq, Finset.prod_pow]
  exact Real.sqrt_sq (Finset.prod_nonneg fun i _ => norm_nonneg _)

/-- The content is strictly positive exactly when the family is linearly independent. -/
theorem content_pos_iff_linearIndependent (v : Fin n → F) :
    0 < content v ↔ LinearIndependent ℝ v := by
  rw [content, Real.sqrt_pos]
  exact (linearIndependent_iff_gram_det_pos v).symm

/-- The content vanishes exactly when the family is linearly dependent. -/
theorem content_eq_zero_iff (v : Fin n → F) :
    content v = 0 ↔ ¬ LinearIndependent ℝ v := by
  rw [← content_pos_iff_linearIndependent]
  constructor
  · intro h; rw [h]; exact lt_irrefl 0
  · intro h
    rcases (content_nonneg v).lt_or_eq with hlt | heq
    · exact absurd hlt h
    · exact heq.symm

end

end GramLinearIndependenceOQ01OQ03
