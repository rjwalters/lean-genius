import Mathlib

/-!
# Power sums of the eigenvalues: `trace(Aᵏ) = Σ λᵢᵏ`

This file extends the spectral symmetric-function identities of
`SpectralTraceDetEigenvaluesOQ01` (trace = sum of eigenvalues, determinant = product of
eigenvalues, Vieta for every charpoly coefficient) to the **power sums**.

For a square matrix `A : Matrix n n K` the eigenvalues, counted with algebraic
multiplicity, are the roots `A.charpoly.roots` of the characteristic polynomial. The
parent established `trace A = (eigenvalues A).sum`, the first power sum `p₁`. Here we prove
the general power-sum identity for **diagonalizable** matrices:
```
trace (Aᵏ) = ((eigenvalues A).map (· ^ k)).sum = Σ λᵢᵏ.
```

## Why diagonalizable?

The identity `trace(Aᵏ) = Σ λᵢᵏ` holds for *every* matrix over an algebraically closed
field, but the general proof requires the spectral-mapping theorem **with multiplicity**:
the eigenvalues of `Aᵏ` are exactly the `k`-th powers of the eigenvalues of `A` (counted
with multiplicity). That fact is equivalent to triangularizing `A`, and Mathlib does not
expose a matrix triangularization `A = P · T · P⁻¹` with `T` upper triangular (only the
endomorphism-level generalized-eigenspace decomposition in
`Mathlib.LinearAlgebra.Eigenspace.Triangularizable`). See the `IsDiagonalizable` predicate
below for the hypothesis we use instead.

For a diagonalizable matrix `A = P · diagonal d · P⁻¹` the argument is elementary and fully
machine-checked: conjugation commutes with taking powers, so `Aᵏ = P · (diagonal d)ᵏ · P⁻¹`,
trace is conjugation-invariant, and `(diagonal d)ᵏ = diagonal (dᵏ)`. The diagonalizable
class already covers the most important cases — Hermitian and (more generally) normal
matrices over `ℂ`, and any matrix with distinct eigenvalues.

All results are fully machine-checked with no `sorry` and no extra axioms.
-/

namespace SpectralTraceDetEigenvaluesOQ01OQ01

open Matrix Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {K : Type*} [Field K]

/-- The eigenvalues of `A`, counted with algebraic multiplicity: the multiset of roots of
the characteristic polynomial. (Same alias as in the parent entry.) -/
noncomputable abbrev eigenvalues (A : Matrix n n K) : Multiset K := A.charpoly.roots

/-- `A` is **diagonalizable**: it is similar to a diagonal matrix, i.e. there is an
invertible `P` and a diagonal `diagonal d` with `A = P · diagonal d · P⁻¹`. The diagonal
entries `d` are exactly the eigenvalues of `A` (with multiplicity); see
`eigenvalues_eq_of_isDiagonalizable`. -/
def IsDiagonalizable (A : Matrix n n K) : Prop :=
  ∃ (P : (Matrix n n K)ˣ) (d : n → K), A = P.val * diagonal d * P⁻¹.val

/-! ### Conjugation commutes with powers -/

/-- Conjugation by a unit commutes with taking powers:
`(P · M · P⁻¹)ᵏ = P · Mᵏ · P⁻¹`. -/
theorem conj_pow (P : (Matrix n n K)ˣ) (M : Matrix n n K) :
    ∀ k : ℕ, (P.val * M * P⁻¹.val) ^ k = P.val * M ^ k * P⁻¹.val
  | 0 => by simp
  | (k + 1) => by
      rw [pow_succ, pow_succ, conj_pow P M k]
      calc P.val * M ^ k * P⁻¹.val * (P.val * M * P⁻¹.val)
          = P.val * M ^ k * (P⁻¹.val * P.val) * M * P⁻¹.val := by
            simp only [Matrix.mul_assoc]
        _ = P.val * M ^ k * 1 * M * P⁻¹.val := by rw [P.inv_mul]
        _ = P.val * (M ^ k * M) * P⁻¹.val := by
            simp only [mul_one, Matrix.mul_assoc]

/-! ### The eigenvalues of a diagonalizable matrix are its diagonal entries -/

/-- The characteristic polynomial of a diagonalizable matrix `A = P · diagonal d · P⁻¹` is
that of `diagonal d`, namely `∏ i, (X - d i)`. -/
theorem charpoly_eq_of_isDiagonalizable {A : Matrix n n K} {P : (Matrix n n K)ˣ}
    {d : n → K} (h : A = P.val * diagonal d * P⁻¹.val) :
    A.charpoly = ∏ i, (X - C (d i)) := by
  rw [h, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]

/-- The eigenvalue multiset of a diagonalizable matrix is the multiset of its diagonal
entries `{d i : i}` (counted with multiplicity). -/
theorem eigenvalues_eq_of_isDiagonalizable {A : Matrix n n K} {P : (Matrix n n K)ˣ}
    {d : n → K} (h : A = P.val * diagonal d * P⁻¹.val) :
    eigenvalues A = Finset.univ.val.map d := by
  have hprod : (∏ i, (X - C (d i)) : K[X])
      = ((Finset.univ.val.map d).map fun a => X - C a).prod := by
    rw [Multiset.map_map]; rfl
  rw [eigenvalues, charpoly_eq_of_isDiagonalizable h, hprod,
    Polynomial.roots_multiset_prod_X_sub_C]

/-! ### The power-sum identity -/

/-- **Power sums for a diagonalizable matrix**, diagonal form. If
`A = P · diagonal d · P⁻¹` then `trace (Aᵏ) = Σ i, (d i)ᵏ`. -/
theorem trace_pow_eq_sum_diagonal {A : Matrix n n K} {P : (Matrix n n K)ˣ} {d : n → K}
    (h : A = P.val * diagonal d * P⁻¹.val) (k : ℕ) :
    (A ^ k).trace = ∑ i, (d i) ^ k := by
  rw [h, conj_pow, Matrix.trace_units_conj, Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp [Pi.pow_apply]

/-- **Power sums of the eigenvalues.** For a diagonalizable matrix `A`, the trace of `Aᵏ`
is the sum of the `k`-th powers of the eigenvalues (counted with multiplicity):
`trace (Aᵏ) = Σ λᵢᵏ`. This is the `k`-th Newton power sum `pₖ` of the spectrum; `k = 1`
recovers the parent's `trace A = (eigenvalues A).sum`. -/
theorem trace_pow_eq_sum_pow_eigenvalues {A : Matrix n n K} (hA : IsDiagonalizable A)
    (k : ℕ) :
    (A ^ k).trace = ((eigenvalues A).map (· ^ k)).sum := by
  obtain ⟨P, d, h⟩ := hA
  rw [trace_pow_eq_sum_diagonal h, eigenvalues_eq_of_isDiagonalizable h,
    Multiset.map_map]
  rfl

/-- Consistency with the parent (`k = 1`): the trace is the first power sum of the
eigenvalues, `trace A = Σ λᵢ`. -/
theorem trace_eq_sum_eigenvalues_of_isDiagonalizable {A : Matrix n n K}
    (hA : IsDiagonalizable A) :
    A.trace = (eigenvalues A).sum := by
  have := trace_pow_eq_sum_pow_eigenvalues hA 1
  simpa using this

/-! ### Diagonal matrices are diagonalizable (the trivial witness) -/

/-- Every diagonal matrix is diagonalizable, with `P = 1`. -/
theorem isDiagonalizable_diagonal (d : n → K) : IsDiagonalizable (diagonal d) :=
  ⟨1, d, by simp⟩

/-- The power-sum identity on a concrete diagonal matrix: for `diagonal d`,
`trace ((diagonal d)ᵏ) = Σ i, (d i)ᵏ`. -/
theorem trace_pow_diagonal (d : n → K) (k : ℕ) :
    ((diagonal d) ^ k).trace = ∑ i, (d i) ^ k := by
  rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp [Pi.pow_apply]

/-! ### A concrete `2 × 2` symmetric example over `ℚ`

The symmetric matrix `A = !![1, 2; 2, 1]` has eigenvalues `3` and `-1` with eigenvectors
`(1, 1)` and `(1, -1)`. With `P = !![1, 1; 1, -1]` (so `det P = -2 ≠ 0`) one has
`A = P · diagonal ![3, -1] · P⁻¹`, hence `trace(Aᵏ) = 3ᵏ + (-1)ᵏ`. For `k = 2` this gives
`9 + 1 = 10`, matching `trace(A²) = trace !![5, 4; 4, 5] = 10`. -/

/-- `diagonal ![3, -1] = !![3, 0; 0, -1]` (an explicit `2 × 2` expansion used below). -/
private theorem diagonal_example :
    diagonal ![(3 : ℚ), -1] = !![3, 0; 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

/-- The witness unit `P = !![1, 1; 1, -1]` with inverse `!![1/2, 1/2; 1/2, -1/2]`. -/
private def Pexample : (Matrix (Fin 2) (Fin 2) ℚ)ˣ where
  val := !![1, 1; 1, -1]
  inv := !![1/2, 1/2; 1/2, -1/2]
  val_inv := by norm_num [Matrix.mul_fin_two, ← Matrix.one_fin_two]
  inv_val := by norm_num [Matrix.mul_fin_two, ← Matrix.one_fin_two]

/-- The explicit similarity `A = P · diagonal ![3, -1] · P⁻¹` for `A = !![1, 2; 2, 1]`. -/
private theorem example_eq :
    (!![(1 : ℚ), 2; 2, 1]) = Pexample.val * diagonal ![3, -1] * Pexample⁻¹.val := by
  show (!![(1 : ℚ), 2; 2, 1]) = !![1, 1; 1, -1] * diagonal ![3, -1] * !![1/2, 1/2; 1/2, -1/2]
  rw [diagonal_example]
  norm_num [Matrix.mul_fin_two]

/-- `A = !![1, 2; 2, 1]` is diagonalizable over `ℚ` (eigenvalues `3` and `-1`). -/
theorem isDiagonalizable_example :
    IsDiagonalizable (!![(1 : ℚ), 2; 2, 1]) :=
  ⟨Pexample, ![3, -1], example_eq⟩

/-- `trace(A²) = 10 = 3² + (-1)²` for the non-diagonal matrix `A = !![1, 2; 2, 1]`,
computed through the power-sum identity. -/
theorem trace_sq_example :
    ((!![(1 : ℚ), 2; 2, 1]) ^ 2).trace = 10 := by
  rw [trace_pow_eq_sum_diagonal example_eq 2]
  norm_num [Fin.sum_univ_two]

end SpectralTraceDetEigenvaluesOQ01OQ01

#print axioms SpectralTraceDetEigenvaluesOQ01OQ01.trace_pow_eq_sum_pow_eigenvalues
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01.eigenvalues_eq_of_isDiagonalizable
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01.conj_pow
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01.trace_sq_example
