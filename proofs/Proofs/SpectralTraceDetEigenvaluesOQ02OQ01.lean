import Mathlib

/-!
# The Frobenius trace form is a genuine inner product

This entry answers the first open question recorded with the parent entry
[`spectral-trace-det-eigenvalues-oq-02`] (cyclic invariance of the trace):

> Prove the trace form `tr(Aᵀ · B) = Σ Aᵢⱼ Bᵢⱼ` is a *genuine* inner product — the
> Frobenius / Hilbert–Schmidt inner product — on the space of real matrices.

The point is that Mathlib does **not** equip `Matrix m n ℝ` with an inner product (nor
even a default norm: its Frobenius norm lives in the *scoped* `def`s
`Matrix.frobeniusNormedAddCommGroup` etc., deliberately kept out of instance resolution to
avoid a norm diamond against the sup-norm).  So the inner-product structure is genuinely
content to build, not a re-export.

We define
`frobInner A B := (Aᵀ * B).trace`
and prove the full slate of inner-product axioms from first principles:

* `frobInner_eq_sum` — the entrywise formula `⟪A, B⟫ = Σᵢⱼ Aᵢⱼ Bᵢⱼ`;
* `frobInner_comm` — **symmetry** `⟪A, B⟫ = ⟪B, A⟫`;
* `frobInner_add_left` / `frobInner_add_right`,
  `frobInner_smul_left` / `frobInner_smul_right` — **bilinearity**;
* `frobInner_self_eq_sum_sq` — `⟪A, A⟫ = Σᵢⱼ Aᵢⱼ²`, the squared **Frobenius norm**;
* `frobInner_self_nonneg` — positive semidefiniteness `0 ≤ ⟪A, A⟫`;
* `frobInner_self_eq_zero_iff` — **positive definiteness** `⟪A, A⟫ = 0 ↔ A = 0`.

These are then packaged into the bundled Mathlib certificate
`frobCore : InnerProductSpace.Core ℝ (Matrix m n ℝ)`, whose mere existence *is* the formal
statement that the Frobenius form is a genuine real inner product.  (The `Core` is the right
certificate here precisely because `Matrix m n ℝ` carries no norm instance — one cannot even
*state* `InnerProductSpace ℝ (Matrix m n ℝ)` without first committing to a norm, which is the
very diamond Mathlib avoids; `InnerProductSpace.ofCore frobCore` would manufacture that norm.)
We close by recording that the norm this inner product induces is exactly the Frobenius norm
`√(Σ Aᵢⱼ²)` (`frob_sqrt_self_eq_frobenius_norm`).

Singular-value content (relating the norm to `Σ σᵢ²`) is left out of scope, as flagged in
the open question.

All results are fully machine-checked with no `sorry` and no extra axioms.
-/

namespace SpectralTraceDetEigenvaluesOQ02OQ01

open Matrix Finset

variable {m n : Type*} [Fintype m] [Fintype n]

/-- The **Frobenius (Hilbert–Schmidt) inner product** of two real matrices,
`⟪A, B⟫ = tr(Aᵀ · B)`. -/
def frobInner (A B : Matrix m n ℝ) : ℝ := (Aᵀ * B).trace

/-- The entrywise formula: `⟪A, B⟫ = Σᵢⱼ Aᵢⱼ Bᵢⱼ`. -/
theorem frobInner_eq_sum (A B : Matrix m n ℝ) :
    frobInner A B = ∑ i, ∑ j, A i j * B i j := by
  unfold frobInner
  simp only [trace, diag_apply, mul_apply, transpose_apply]
  rw [Finset.sum_comm]

/-- **Symmetry** of the Frobenius inner product. -/
theorem frobInner_comm (A B : Matrix m n ℝ) : frobInner A B = frobInner B A := by
  simp only [frobInner_eq_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/-! ### Bilinearity -/

/-- Additivity in the first argument. -/
theorem frobInner_add_left (A B C : Matrix m n ℝ) :
    frobInner (A + B) C = frobInner A C + frobInner B C := by
  simp only [frobInner_eq_sum, Matrix.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/-- Additivity in the second argument. -/
theorem frobInner_add_right (A B C : Matrix m n ℝ) :
    frobInner A (B + C) = frobInner A B + frobInner A C := by
  rw [frobInner_comm, frobInner_add_left, frobInner_comm A B, frobInner_comm A C]

/-- Homogeneity in the first argument. -/
theorem frobInner_smul_left (r : ℝ) (A B : Matrix m n ℝ) :
    frobInner (r • A) B = r * frobInner A B := by
  simp only [frobInner_eq_sum, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

/-- Homogeneity in the second argument. -/
theorem frobInner_smul_right (r : ℝ) (A B : Matrix m n ℝ) :
    frobInner A (r • B) = r * frobInner A B := by
  rw [frobInner_comm, frobInner_smul_left, frobInner_comm A B]

/-! ### Positive definiteness -/

/-- The induced quadratic form is the squared Frobenius norm `Σᵢⱼ Aᵢⱼ²`. -/
theorem frobInner_self_eq_sum_sq (A : Matrix m n ℝ) :
    frobInner A A = ∑ i, ∑ j, (A i j) ^ 2 := by
  simp only [frobInner_eq_sum, sq]

/-- **Positive semidefiniteness**: `0 ≤ ⟪A, A⟫`. -/
theorem frobInner_self_nonneg (A : Matrix m n ℝ) : 0 ≤ frobInner A A := by
  rw [frobInner_self_eq_sum_sq]
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))

/-- **Positive definiteness**: `⟪A, A⟫ = 0 ↔ A = 0`. -/
theorem frobInner_self_eq_zero_iff (A : Matrix m n ℝ) :
    frobInner A A = 0 ↔ A = 0 := by
  rw [frobInner_self_eq_sum_sq]
  constructor
  · intro h
    ext i j
    have hi : ∀ i ∈ Finset.univ, (0 : ℝ) ≤ ∑ j, (A i j) ^ 2 :=
      fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have h1 : ∑ j, (A i j) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hi).1 h i (Finset.mem_univ i)
    have hj : ∀ j ∈ Finset.univ, (0 : ℝ) ≤ (A i j) ^ 2 := fun j _ => sq_nonneg _
    have h2 : (A i j) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hj).1 h1 j (Finset.mem_univ j)
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
  · intro h
    subst h
    simp

/-! ### The bundled inner-product certificate -/

/-- The Frobenius form, packaged as a Mathlib `InnerProductSpace.Core` over `ℝ`.  Its very
existence certifies that `frobInner` satisfies *all* the inner-product axioms: Hermitian
symmetry, positive semidefiniteness, additivity and homogeneity in the first slot, and
positive definiteness. -/
noncomputable def frobCore : InnerProductSpace.Core ℝ (Matrix m n ℝ) where
  inner := frobInner
  conj_inner_symm x y := by
    simp only [RCLike.conj_to_real]
    exact frobInner_comm y x
  re_inner_nonneg x := by
    simpa only [RCLike.re_to_real] using frobInner_self_nonneg x
  add_left x y z := frobInner_add_left x y z
  smul_left x y r := by
    simp only [RCLike.conj_to_real]
    exact frobInner_smul_left r x y
  definite x hx := (frobInner_self_eq_zero_iff x).1 hx

/-- The norm any inner-product space attaches to `⟪·,·⟫` is `√⟪A, A⟫`; here that is the
**Frobenius norm** `√(Σᵢⱼ Aᵢⱼ²)`.  We record the radicand identity directly, independent of
the inner-product-space norm plumbing. -/
theorem frob_sqrt_self_eq_frobenius_norm (A : Matrix m n ℝ) :
    Real.sqrt (frobInner A A) = Real.sqrt (∑ i, ∑ j, (A i j) ^ 2) := by
  rw [frobInner_self_eq_sum_sq]

/-! ### Sanity checks -/

/-- Over `ℝ`, `⟪A, A⟫` for the `2×2` matrix `![![3, 4], ![0, 0]]` is `9 + 16 = 25`. -/
example : frobInner (![![(3 : ℝ), 4], ![0, 0]] : Matrix (Fin 2) (Fin 2) ℝ)
    (![![(3 : ℝ), 4], ![0, 0]]) = 25 := by
  simp [frobInner_eq_sum, Fin.sum_univ_succ]
  norm_num

/-- Symmetry, on a concrete pair. -/
example (A B : Matrix (Fin 2) (Fin 3) ℝ) : frobInner A B = frobInner B A :=
  frobInner_comm A B

end SpectralTraceDetEigenvaluesOQ02OQ01
