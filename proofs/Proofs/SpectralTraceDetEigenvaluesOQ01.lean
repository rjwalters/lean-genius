import Mathlib

/-!
# Trace and determinant from the eigenvalues (spectral symmetric functions)

For a square matrix `A : Matrix n n K` over a field `K`, the roots of the characteristic
polynomial `A.charpoly` are the **eigenvalues** of `A`, counted with algebraic
multiplicity. Mathlib proves the two headline spectral identities (hence the `mathlib`
badge on them):

* `Matrix.trace_eq_sum_roots_charpoly` — over an algebraically closed field, the trace is
  the **sum** of the eigenvalues;
* `Matrix.det_eq_prod_roots_charpoly` — and the determinant is their **product**.

We re-export those two under eigenvalue-flavoured names and then derive the genuine
content absent from Mathlib for the characteristic polynomial:

* `card_eigenvalues_eq_dim` — over an algebraically closed field there are exactly
  `Fintype.card n` eigenvalues counted with multiplicity (the multiset of roots has the
  same cardinality as the dimension of the space);
* `charpoly_coeff_eq_esymm_eigenvalues` — **Vieta for eigenvalues**: every coefficient of
  the characteristic polynomial is, up to sign, an elementary symmetric function of the
  eigenvalues. Trace (`k = n - 1`) and determinant (`k = 0`) are the two extreme cases of
  this single statement;
* `det_eq_zero_iff_zero_mem_spectrum` — over **any** field, a matrix is singular iff `0`
  is an eigenvalue (`0 ∈ spectrum K A`); equivalently
  `isUnit_det_iff_zero_not_mem_spectrum`, a matrix is invertible iff `0` is not an
  eigenvalue.

The closing examples illustrate the headline identities on the concrete `2 × 2` complex
matrix `!![1, 2; 3, 4]`: its eigenvalues are the irrational numbers `(5 ± √33)/2`, yet
their sum is `5` and their product is `-2` — read off the trace and determinant without
ever computing the eigenvalues themselves.

All results are fully machine-checked with no `sorry` and no extra axioms.
-/

namespace SpectralTraceDetEigenvaluesOQ01

open Matrix Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {K : Type*} [Field K]

/-- The eigenvalues of `A`, counted with algebraic multiplicity: the multiset of roots of
the characteristic polynomial.  (A reducible alias for `A.charpoly.roots`.) -/
noncomputable abbrev eigenvalues (A : Matrix n n K) : Multiset K := A.charpoly.roots

/-! ### The headline identities (re-exported from Mathlib) -/

/-- Over an algebraically closed field, the **trace is the sum of the eigenvalues**
(counted with multiplicity).  This is `Matrix.trace_eq_sum_roots_charpoly`. -/
theorem trace_eq_sum_eigenvalues [IsAlgClosed K] (A : Matrix n n K) :
    A.trace = (eigenvalues A).sum :=
  A.trace_eq_sum_roots_charpoly

/-- Over an algebraically closed field, the **determinant is the product of the
eigenvalues** (counted with multiplicity).  This is `Matrix.det_eq_prod_roots_charpoly`. -/
theorem det_eq_prod_eigenvalues [IsAlgClosed K] (A : Matrix n n K) :
    A.det = (eigenvalues A).prod :=
  A.det_eq_prod_roots_charpoly

/-! ### Genuine content beyond Mathlib -/

/-- Over an algebraically closed field, a matrix has exactly `Fintype.card n` eigenvalues
counted with algebraic multiplicity: the eigenvalue multiset has cardinality equal to the
dimension of the space. -/
theorem card_eigenvalues_eq_dim [IsAlgClosed K] (A : Matrix n n K) :
    Multiset.card (eigenvalues A) = Fintype.card n := by
  rw [eigenvalues, (splits_iff_card_roots).1 (IsAlgClosed.splits A.charpoly),
    charpoly_natDegree_eq_dim]

/-- **Vieta's formulas for the eigenvalues.**  Over an algebraically closed field, the
`k`-th coefficient of the characteristic polynomial is, up to the sign `(-1) ^ (n - k)`,
the `(n - k)`-th elementary symmetric polynomial of the eigenvalues, where `n` is the
dimension.  The two extreme cases are the headline identities above: `k = n - 1` recovers
the trace (sum, `esymm 1`) and `k = 0` recovers the determinant (product, `esymm n`). -/
theorem charpoly_coeff_eq_esymm_eigenvalues [IsAlgClosed K] (A : Matrix n n K)
    {k : ℕ} (hk : k ≤ Fintype.card n) :
    A.charpoly.coeff k =
      (-1) ^ (Fintype.card n - k) * (eigenvalues A).esymm (Fintype.card n - k) := by
  have hdeg : A.charpoly.natDegree = Fintype.card n := charpoly_natDegree_eq_dim A
  have hk' : k ≤ A.charpoly.natDegree := hdeg ▸ hk
  rw [Polynomial.coeff_eq_esymm_roots_of_splits (IsAlgClosed.splits A.charpoly) hk',
    A.charpoly_monic.leadingCoeff, one_mul, hdeg]

/-- **Singular ⟺ zero is an eigenvalue**, over an arbitrary field.  A matrix has vanishing
determinant exactly when `0` lies in its spectrum (equivalently, `0` is a root of the
characteristic polynomial). -/
theorem det_eq_zero_iff_zero_mem_spectrum (A : Matrix n n K) :
    A.det = 0 ↔ (0 : K) ∈ spectrum K A := by
  rw [det_eq_sign_charpoly_coeff, mul_eq_zero, mem_spectrum_iff_isRoot_charpoly,
    Polynomial.IsRoot.def, ← coeff_zero_eq_eval_zero]
  have hne : ((-1 : K)) ^ Fintype.card n ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  simp [hne]

/-- **Invertible ⟺ zero is not an eigenvalue**, over an arbitrary field. -/
theorem isUnit_det_iff_zero_not_mem_spectrum (A : Matrix n n K) :
    IsUnit A.det ↔ (0 : K) ∉ spectrum K A := by
  rw [isUnit_iff_ne_zero, ne_eq, det_eq_zero_iff_zero_mem_spectrum]

/-! ### A concrete `2 × 2` illustration over `ℂ`

The matrix `!![1, 2; 3, 4]` has characteristic polynomial `X² - 5X - 2`, whose roots are
`(5 ± √33)/2` — irrational.  Nevertheless the spectral identities give their sum and
product immediately from the (rational) trace and determinant. -/

/-- The sum of the two (irrational) eigenvalues of `!![1, 2; 3, 4]` is `5`. -/
theorem sum_eigenvalues_example :
    (eigenvalues (!![(1 : ℂ), 2; 3, 4])).sum = 5 := by
  rw [← trace_eq_sum_eigenvalues, Matrix.trace_fin_two]
  norm_num

/-- The product of the two (irrational) eigenvalues of `!![1, 2; 3, 4]` is `-2`. -/
theorem prod_eigenvalues_example :
    (eigenvalues (!![(1 : ℂ), 2; 3, 4])).prod = -2 := by
  rw [← det_eq_prod_eigenvalues, Matrix.det_fin_two]
  norm_num

/-- There are exactly two eigenvalues (counted with multiplicity) of `!![1, 2; 3, 4]`. -/
theorem card_eigenvalues_example :
    Multiset.card (eigenvalues (!![(1 : ℂ), 2; 3, 4])) = 2 := by
  rw [card_eigenvalues_eq_dim]
  simp

end SpectralTraceDetEigenvaluesOQ01

#print axioms SpectralTraceDetEigenvaluesOQ01.charpoly_coeff_eq_esymm_eigenvalues
#print axioms SpectralTraceDetEigenvaluesOQ01.det_eq_zero_iff_zero_mem_spectrum
#print axioms SpectralTraceDetEigenvaluesOQ01.card_eigenvalues_eq_dim
#print axioms SpectralTraceDetEigenvaluesOQ01.sum_eigenvalues_example
#print axioms SpectralTraceDetEigenvaluesOQ01.prod_eigenvalues_example
