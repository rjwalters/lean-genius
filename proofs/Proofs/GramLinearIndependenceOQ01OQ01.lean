import Mathlib

/-!
# Hadamard's determinant inequality for Gram matrices

For a finite family of vectors `v : ι → E` in an inner product space `E` over `𝕜`
(`ℝ` or `ℂ`) that fills the whole space (`finrank 𝕜 E = card ι`), the **Gramian**
`det (gram 𝕜 v)` is bounded above by the product of the squared norms:

* `hadamard_inequality` — **Hadamard's inequality**
  `det (gram 𝕜 v) ≤ ∏ i, ‖v i‖²` (the determinant is a nonnegative real, compared in
  `𝕜` via the `ComplexOrder`);
* `re_gram_det_le_prod_norm_sq` — the same bound stated for the real part, avoiding any
  order on `𝕜`.

Geometrically the Gramian is the squared volume of the parallelepiped spanned by the
`v i`, and Hadamard's inequality says this volume is largest, for fixed edge lengths,
exactly when the edges are mutually orthogonal — the **equality case**:

* `gram_det_of_orthogonal` — a pairwise orthogonal family attains equality
  `det (gram 𝕜 v) = ∏ i, ⟪v i, v i⟫ = ∏ i, ‖v i‖²`;
* `hadamard_eq_iff_orthogonal` — for a **linearly independent** family, equality holds
  **iff** the vectors are pairwise orthogonal.

The proof routes through Mathlib's Gram–Schmidt orthonormal basis
`e := gramSchmidtOrthonormalBasis`. Writing `B` for the (upper-triangular) coordinate
matrix `B i j = ⟪e i, v j⟫`, two facts drive everything:

* `gram 𝕜 v = Bᴴ * B`  (completeness of the orthonormal basis), hence
  `det (gram 𝕜 v) = ‖det B‖²`;
* `det B = ∏ i, ⟪e i, v i⟫`  (Mathlib's `gramSchmidtOrthonormalBasis_det`: the matrix is
  triangular), while Bessel's identity `‖v j‖² = ∑ i, ‖⟪e i, v j⟫‖²` forces each diagonal
  factor `‖⟪e i, v i⟫‖² ≤ ‖v i‖²`, with equality only when the off-diagonal coordinates
  vanish.

Hadamard's inequality is absent from Mathlib (which has the Gram–Schmidt machinery but
not this determinant bound). All results are machine-checked with no `sorry` and no extra
axioms. This extends `gram-linear-independence-iff-oq-01`, which established positive
(semi)definiteness and the Gramian linear-independence criterion.
-/

namespace GramLinearIndependenceOQ01OQ01

open Matrix RCLike Finset Module InnerProductSpace
open scoped ComplexOrder InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
variable [FiniteDimensional 𝕜 E]

/-! ## The coordinate matrix `B i j = ⟪e i, v j⟫` -/

/-- The coordinate matrix of `v` in the Gram–Schmidt orthonormal basis has entries
`B i j = ⟪e i, v j⟫`. -/
theorem coordMatrix_apply (h : finrank 𝕜 E = Fintype.card ι) (v : ι → E) (i j : ι) :
    (gramSchmidtOrthonormalBasis h v).toBasis.toMatrix v i j = ⟪(gramSchmidtOrthonormalBasis h v) i, v j⟫_𝕜 := by
  rw [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply]

/-- **Key factorisation.** The Gram matrix is `Bᴴ * B`, where `B` is the coordinate
matrix in the Gram–Schmidt orthonormal basis. This is just completeness of the basis:
`⟪v i, v j⟫ = ∑ k, ⟪v i, e k⟫ * ⟪e k, v j⟫`. -/
theorem gram_eq_conjTranspose_mul (h : finrank 𝕜 E = Fintype.card ι) (v : ι → E) :
    Matrix.gram 𝕜 v = ((gramSchmidtOrthonormalBasis h v).toBasis.toMatrix v)ᴴ * (gramSchmidtOrthonormalBasis h v).toBasis.toMatrix v := by
  ext i j
  rw [Matrix.gram_apply, Matrix.mul_apply,
    ← OrthonormalBasis.sum_inner_mul_inner (gramSchmidtOrthonormalBasis h v) (v i) (v j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_apply, coordMatrix_apply, coordMatrix_apply, star_def,
    inner_conj_symm]

/-! ## The determinant is `‖det B‖²` -/

/-- The determinant of the coordinate matrix is the product of the diagonal inner
products (the matrix is triangular). -/
theorem coordMatrix_det (h : finrank 𝕜 E = Fintype.card ι) (v : ι → E) :
    ((gramSchmidtOrthonormalBasis h v).toBasis.toMatrix v).det = ∏ i, ⟪(gramSchmidtOrthonormalBasis h v) i, v i⟫_𝕜 := by
  rw [← Basis.det_apply, gramSchmidtOrthonormalBasis_det]

/-- The Gramian equals the squared norm of the determinant of the coordinate matrix,
which (the matrix being triangular) is `‖∏ i, ⟪e i, v i⟫‖²`. -/
theorem gram_det_eq (h : finrank 𝕜 E = Fintype.card ι) (v : ι → E) :
    (Matrix.gram 𝕜 v).det = ((‖∏ i, ⟪(gramSchmidtOrthonormalBasis h v) i, v i⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
  rw [gram_eq_conjTranspose_mul h v, Matrix.det_mul, Matrix.det_conjTranspose,
    coordMatrix_det h v, star_def, RCLike.conj_mul]
  push_cast
  ring

/-! ## Bessel's identity bounds each diagonal factor -/

/-- Bessel: the squared diagonal coordinate is at most the squared norm,
`‖⟪e i, v i⟫‖² ≤ ‖v i‖²`, since it is one term of the Parseval sum
`‖v i‖² = ∑ k, ‖⟪e k, v i⟫‖²`. -/
theorem abs_inner_sq_le_norm_sq (h : finrank 𝕜 E = Fintype.card ι) (v : ι → E) (i : ι) :
    ‖⟪(gramSchmidtOrthonormalBasis h v) i, v i⟫_𝕜‖ ^ 2 ≤ ‖v i‖ ^ 2 := by
  rw [← OrthonormalBasis.sum_sq_norm_inner_right (gramSchmidtOrthonormalBasis h v) (v i)]
  exact Finset.single_le_sum (f := fun k => ‖⟪(gramSchmidtOrthonormalBasis h v) k, v i⟫_𝕜‖ ^ 2)
    (fun k _ => sq_nonneg _) (Finset.mem_univ i)

/-! ## Hadamard's inequality -/

/-- The real number underlying the Gramian, `‖det B‖² = ∏ i, ‖⟪e i, v i⟫‖²`, is bounded
by the product of squared norms. This is the analytic heart of Hadamard's inequality. -/
theorem norm_det_sq_le_prod_norm_sq (h : finrank 𝕜 E = Fintype.card ι) (v : ι → E) :
    ‖∏ i, ⟪(gramSchmidtOrthonormalBasis h v) i, v i⟫_𝕜‖ ^ 2 ≤ ∏ i, ‖v i‖ ^ 2 := by
  rw [norm_prod, ← Finset.prod_pow]
  exact Finset.prod_le_prod (fun i _ => sq_nonneg _)
    (fun i _ => abs_inner_sq_le_norm_sq h v i)

/-- **Hadamard's inequality.** The Gramian is at most the product of the squared norms.
Both sides are nonnegative reals; the inequality is stated in `𝕜` via the `ComplexOrder`. -/
theorem hadamard_inequality (h : finrank 𝕜 E = Fintype.card ι) (v : ι → E) :
    (Matrix.gram 𝕜 v).det ≤ ((∏ i, ‖v i‖ ^ 2 : ℝ) : 𝕜) := by
  rw [gram_det_eq h v, RCLike.ofReal_le_ofReal]
  exact norm_det_sq_le_prod_norm_sq h v

/-- **Hadamard's inequality**, real-part form (no order on `𝕜` required). -/
theorem re_gram_det_le_prod_norm_sq (h : finrank 𝕜 E = Fintype.card ι) (v : ι → E) :
    RCLike.re (Matrix.gram 𝕜 v).det ≤ ∏ i, ‖v i‖ ^ 2 := by
  rw [gram_det_eq h v, RCLike.ofReal_re]
  exact norm_det_sq_le_prod_norm_sq h v

/-! ## Equality for orthogonal families -/

omit [LocallyFiniteOrderBot ι] [WellFoundedLT ι] [FiniteDimensional 𝕜 E] in
/-- A **pairwise orthogonal** family has a diagonal Gram matrix, so the Gramian is exactly
the product of the diagonal entries `⟪v i, v i⟫`. (No dimension hypothesis is needed.) -/
theorem gram_det_of_orthogonal {v : ι → E} (hv : Pairwise (⟪v ·, v ·⟫_𝕜 = 0)) :
    (Matrix.gram 𝕜 v).det = ∏ i, ⟪v i, v i⟫_𝕜 := by
  rw [show Matrix.gram 𝕜 v = Matrix.diagonal (fun i => ⟪v i, v i⟫_𝕜) from ?_,
    Matrix.det_diagonal]
  ext i j
  rcases eq_or_ne i j with rfl | hij
  · simp [Matrix.gram_apply]
  · rw [Matrix.gram_apply, Matrix.diagonal_apply_ne _ hij, hv hij]

omit [LocallyFiniteOrderBot ι] [WellFoundedLT ι] [FiniteDimensional 𝕜 E] in
/-- Orthogonal version with squared norms: `det (gram 𝕜 v) = ∏ i, ‖v i‖²` in `𝕜`. -/
theorem gram_det_of_orthogonal_norm {v : ι → E} (hv : Pairwise (⟪v ·, v ·⟫_𝕜 = 0)) :
    (Matrix.gram 𝕜 v).det = ((∏ i, ‖v i‖ ^ 2 : ℝ) : 𝕜) := by
  rw [gram_det_of_orthogonal hv]
  push_cast
  exact Finset.prod_congr rfl fun i _ => inner_self_eq_norm_sq_to_K (v i)

/-! ## Equality iff orthogonal (linearly independent families) -/

/-- For a linearly independent family of full size, each Gram–Schmidt diagonal inner
product `⟪e i, v i⟫` is nonzero: their product is the determinant `e.det v`, a unit
because `v` is a basis. -/
theorem inner_diag_ne_zero (h : finrank 𝕜 E = Fintype.card ι) {v : ι → E}
    (hv : LinearIndependent 𝕜 v) (i : ι) : ⟪(gramSchmidtOrthonormalBasis h v) i, v i⟫_𝕜 ≠ 0 := by
  haveI : Nonempty ι := ⟨i⟩
  have hspan : Submodule.span 𝕜 (Set.range v) = ⊤ := by
    rw [← coe_basisOfLinearIndependentOfCardEqFinrank hv h.symm]
    exact (basisOfLinearIndependentOfCardEqFinrank hv h.symm).span_eq
  have hunit : IsUnit ((gramSchmidtOrthonormalBasis h v).toBasis.det v) :=
    (Basis.is_basis_iff_det _).mp ⟨hv, hspan⟩
  have hprod : ∏ k, ⟪(gramSchmidtOrthonormalBasis h v) k, v k⟫_𝕜 ≠ 0 := by
    rw [← coordMatrix_det h v]
    rw [Basis.det_apply] at hunit
    exact hunit.ne_zero
  exact fun hi => hprod (Finset.prod_eq_zero (Finset.mem_univ i) hi)

/-- In the equality case, each diagonal factor is sharp: `‖⟪e i, v i⟫‖² = ‖v i‖²`.
If some factor were strict, the product would be strictly smaller (all factors positive
by `inner_diag_ne_zero`), contradicting equality. -/
theorem diag_sq_eq_of_hadamard_eq (h : finrank 𝕜 E = Fintype.card ι) {v : ι → E}
    (hv : LinearIndependent 𝕜 v)
    (heq : ‖∏ i, ⟪(gramSchmidtOrthonormalBasis h v) i, v i⟫_𝕜‖ ^ 2 = ∏ i, ‖v i‖ ^ 2) (i : ι) :
    ‖⟪(gramSchmidtOrthonormalBasis h v) i, v i⟫_𝕜‖ ^ 2 = ‖v i‖ ^ 2 := by
  rw [norm_prod, ← Finset.prod_pow] at heq
  by_contra hne
  have hlt : ∏ k, ‖⟪(gramSchmidtOrthonormalBasis h v) k, v k⟫_𝕜‖ ^ 2 < ∏ k, ‖v k‖ ^ 2 :=
    Finset.prod_lt_prod
      (fun k _ => pow_pos (norm_pos_iff.mpr (inner_diag_ne_zero h hv k)) 2)
      (fun k _ => abs_inner_sq_le_norm_sq h v k)
      ⟨i, Finset.mem_univ i, lt_of_le_of_ne (abs_inner_sq_le_norm_sq h v i) hne⟩
  exact absurd heq (ne_of_lt hlt)

/-- Diagonal sharpness forces the off-diagonal coordinates to vanish:
`⟪e k, v i⟫ = 0` for `k ≠ i`. (One term of Bessel's sum already accounts for the whole
norm, so the rest must be zero.) -/
theorem coord_off_diag_eq_zero (h : finrank 𝕜 E = Fintype.card ι) {v : ι → E}
    (hsharp : ∀ i, ‖⟪(gramSchmidtOrthonormalBasis h v) i, v i⟫_𝕜‖ ^ 2 = ‖v i‖ ^ 2) {k i : ι} (hki : k ≠ i) :
    ⟪(gramSchmidtOrthonormalBasis h v) k, v i⟫_𝕜 = 0 := by
  have hsum := OrthonormalBasis.sum_sq_norm_inner_right (gramSchmidtOrthonormalBasis h v) (v i)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hsharp i] at hsum
  have herase : ∑ x ∈ univ.erase i, ‖⟪(gramSchmidtOrthonormalBasis h v) x, v i⟫_𝕜‖ ^ 2 = 0 := by
    linarith
  have hz : ‖⟪(gramSchmidtOrthonormalBasis h v) k, v i⟫_𝕜‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp herase k
      (Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩)
  exact norm_eq_zero.mp (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hz)

/-- Diagonal sharpness implies pairwise orthogonality of `v`. -/
theorem orthogonal_of_diag_sq_eq (h : finrank 𝕜 E = Fintype.card ι) {v : ι → E}
    (hsharp : ∀ i, ‖⟪(gramSchmidtOrthonormalBasis h v) i, v i⟫_𝕜‖ ^ 2 = ‖v i‖ ^ 2) :
    Pairwise (⟪v ·, v ·⟫_𝕜 = 0) := by
  intro i j hij
  rw [← OrthonormalBasis.sum_inner_mul_inner (gramSchmidtOrthonormalBasis h v) (v i) (v j)]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases eq_or_ne k i with rfl | hki
  · -- k = i ≠ j, so the second factor ⟪e k, v j⟫ = 0
    rw [coord_off_diag_eq_zero h hsharp hij, mul_zero]
  · -- k ≠ i, so the first factor ⟪v i, e k⟫ = conj ⟪e k, v i⟫ = 0
    rw [← inner_conj_symm, coord_off_diag_eq_zero h hsharp hki, map_zero, zero_mul]

/-- **Hadamard equality case.** For a linearly independent family of full size, the
Gramian equals the product of squared norms **iff** the vectors are pairwise orthogonal. -/
theorem hadamard_eq_iff_orthogonal (h : finrank 𝕜 E = Fintype.card ι) {v : ι → E}
    (hv : LinearIndependent 𝕜 v) :
    (Matrix.gram 𝕜 v).det = ((∏ i, ‖v i‖ ^ 2 : ℝ) : 𝕜) ↔ Pairwise (⟪v ·, v ·⟫_𝕜 = 0) := by
  constructor
  · intro hd
    rw [gram_det_eq h v, RCLike.ofReal_inj] at hd
    exact orthogonal_of_diag_sq_eq h (diag_sq_eq_of_hadamard_eq h hv hd)
  · exact gram_det_of_orthogonal_norm

/-! ## Concrete corollaries on `EuclideanSpace` -/

/-- **Hadamard's inequality on `EuclideanSpace`.** For any family of `n` vectors in
`EuclideanSpace 𝕜 (Fin n)`, the Gramian is at most the product of the squared norms — the
dimension hypothesis is automatic. -/
theorem hadamard_inequality_euclidean {n : ℕ} (v : Fin n → EuclideanSpace 𝕜 (Fin n)) :
    (Matrix.gram 𝕜 v).det ≤ ((∏ i, ‖v i‖ ^ 2 : ℝ) : 𝕜) :=
  hadamard_inequality (by rw [finrank_euclideanSpace_fin, Fintype.card_fin]) v

/-- **Hadamard equality case on `EuclideanSpace`.** A linearly independent family of `n`
vectors in `EuclideanSpace 𝕜 (Fin n)` attains the Hadamard bound iff it is orthogonal. -/
theorem hadamard_eq_iff_orthogonal_euclidean {n : ℕ} {v : Fin n → EuclideanSpace 𝕜 (Fin n)}
    (hv : LinearIndependent 𝕜 v) :
    (Matrix.gram 𝕜 v).det = ((∏ i, ‖v i‖ ^ 2 : ℝ) : 𝕜) ↔ Pairwise (⟪v ·, v ·⟫_𝕜 = 0) :=
  hadamard_eq_iff_orthogonal (by rw [finrank_euclideanSpace_fin, Fintype.card_fin]) hv

end GramLinearIndependenceOQ01OQ01
