/-
  Hilbert 17 — the Gram core for "PSD quadratic forms are sums of squares".

  This file proves, with **zero axioms**, the matrix-level engine behind the
  axiom `quadratic_psd_is_sos_aux` in `Hilbert17SumOfSquares.lean`:

      a positive semidefinite real matrix `M` makes its quadratic form
      `x ↦ xᵀ M x` an honest **sum of squares of linear forms**.

  Concretely, with `S = √M` (the PSD square root, which is symmetric over ℝ),

      x ⬝ᵥ (M *ᵥ x) = ∑ i, ((S *ᵥ x) i)²,

  and each `(S *ᵥ x) i = ∑ j, S i j * x j` is a linear form in `x`.  This is the
  Gram / Cholesky route: `M PSD ⟺ M = Sᵀ S`, hence `xᵀ M x = ‖S x‖²`.

  What is NOT done here (the remaining multi-session "bridge"): connecting an
  arbitrary `Q : MvPolynomial (Fin n) ℝ` of `totalDegree = 2` to its symmetric
  coefficient matrix `M` and back to `IsSumOfSquaresMvPolynomial`.  That
  coefficient-extraction / homogenisation step is the genuine Mathlib gap noted
  in `research/problems/hilbert-17-oq-03/knowledge.md`; this file supplies the
  algebraic heart that any such bridge will call.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic

namespace Hilbert17

open Matrix
open scoped MatrixOrder

variable {n : ℕ}

/-- **Real PSD ⟹ symmetric Gram factorization.**

    A positive semidefinite real matrix `M` factors as `M = Sᵀ * S` where
    `S = √M` is symmetric (`Sᵀ = S`).  Over ℝ the conjugate transpose is the
    transpose, so the Hermitian square root is genuinely symmetric. -/
theorem sqrt_transpose_eq_self {M : Matrix (Fin n) (Fin n) ℝ}
    (_hM : M.PosSemidef) :
    (CFC.sqrt M)ᵀ = CFC.sqrt M := by
  have h : (CFC.sqrt M)ᴴ = CFC.sqrt M := ((CFC.sqrt_nonneg M).posSemidef).isHermitian
  rwa [conjTranspose_eq_transpose_of_trivial] at h

/-- `M = Sᵀ * S` with `S = √M`, the real Gram factorization of a PSD matrix. -/
theorem posSemidef_eq_transpose_mul_sqrt {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) :
    (CFC.sqrt M)ᵀ * CFC.sqrt M = M := by
  rw [sqrt_transpose_eq_self hM]
  exact CFC.sqrt_mul_sqrt_self M

/-- **The Gram core: a PSD matrix's quadratic form is a sum of squares.**

    For a positive semidefinite real matrix `M`, the quadratic form
    `x ⬝ᵥ (M *ᵥ x) = xᵀ M x` equals `∑ i, ((√M *ᵥ x) i)²`, an explicit sum of
    squares of the linear forms `x ↦ (√M *ᵥ x) i = ∑ j, (√M) i j * x j`. -/
theorem posSemidef_quadratic_isSumSq {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) (x : Fin n → ℝ) :
    x ⬝ᵥ (M *ᵥ x) = ∑ i, ((CFC.sqrt M *ᵥ x) i) ^ 2 := by
  set S := CFC.sqrt M with hSdef
  have hsymm : Sᵀ = S := sqrt_transpose_eq_self hM
  have hfac : Sᵀ * S = M := posSemidef_eq_transpose_mul_sqrt hM
  calc
    x ⬝ᵥ (M *ᵥ x)
        = x ⬝ᵥ ((Sᵀ * S) *ᵥ x) := by rw [hfac]
    _   = x ⬝ᵥ (Sᵀ *ᵥ (S *ᵥ x)) := by rw [← mulVec_mulVec]
    _   = (x ᵥ* Sᵀ) ⬝ᵥ (S *ᵥ x) := by rw [dotProduct_mulVec]
    _   = (S *ᵥ x) ⬝ᵥ (S *ᵥ x) := by rw [vecMul_transpose]
    _   = ∑ i, ((S *ᵥ x) i) ^ 2 := by rw [dotProduct]; simp [pow_two]

/-- **Packaged existence form.** Every PSD real matrix `M` admits a real matrix
    `B` (namely `B = √M`) such that the quadratic form `xᵀ M x` is the sum of
    squares of the linear forms given by the rows of `B`. -/
theorem posSemidef_exists_sumSq {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ,
      ∀ x : Fin n → ℝ, x ⬝ᵥ (M *ᵥ x) = ∑ i, ((B *ᵥ x) i) ^ 2 :=
  ⟨CFC.sqrt M, fun x => posSemidef_quadratic_isSumSq hM x⟩

open MvPolynomial in
/-- **Homogeneous quadratic-forms case of Hilbert's PSD = SOS, fully verified.**

    For a positive semidefinite real matrix `M`, the homogeneous degree-2
    polynomial `Q_M = ∑ i j, M i j · Xᵢ Xⱼ` is an honest polynomial sum of
    squares: `Q_M = ∑ k, (∑ j, (√M) k j · Xⱼ)²`.  The witnesses are the linear
    forms given by the rows of `√M`.

    This is exactly `IsSumOfSquaresMvPolynomial Q_M` (the existence form below),
    proved with zero axioms.  It is the homogeneous heart of
    `quadratic_psd_is_sos_aux`; the remaining gap is the reduction of an
    *arbitrary* `totalDegree = 2` polynomial to this matrix-given form. -/
theorem posSemidef_matrixQuadratic_isSumSq {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) :
    ∃ (m : ℕ) (q : Fin m → MvPolynomial (Fin n) ℝ),
      (∑ i, ∑ j, C (M i j) * X i * X j) = ∑ k, q k ^ 2 := by
  refine ⟨n, fun k => ∑ j, C (CFC.sqrt M k j) * X j, ?_⟩
  apply MvPolynomial.funext
  intro x
  have key := posSemidef_quadratic_isSumSq hM x
  simp only [dotProduct, mulVec] at key
  simp only [map_sum, map_mul, map_pow, eval_C, eval_X]
  rw [← key]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

end Hilbert17
