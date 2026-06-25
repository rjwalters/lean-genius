import Mathlib
import Proofs.SpectralTraceDetEigenvaluesOQ01

/-
# Spectral trace, OQ-01 → OQ-01 → OQ-02 → OQ-01: Newton's identity `tr(A⁴) = Σ λᵢ⁴` in dimension four

## What this file proves

The parent `spectral-trace-det-eigenvalues-oq-01-oq-01-oq-02`
(`SpectralTraceDetEigenvaluesOQ01OQ01OQ02.lean`) reached the third power-sum identity
`tr(A³) = λ₁³ + λ₂³ + λ₃³` for `3 × 3` matrices, via Newton's identity
`p₃ = e₁³ − 3 e₁ e₂ + 3 e₃`.  Its open question asks to carry the
matrix-side-then-spectral template one dimension further, to the **fourth** power sum:

      tr(A⁴) = e₁⁴ − 4 e₁² e₂ + 2 e₂² + 4 e₁ e₃ − 4 e₄          (Newton's identity `p₄`),

read as the spectral statement `tr(A⁴) = λ₁⁴ + λ₂⁴ + λ₃⁴ + λ₄⁴` for `4 × 4` matrices.  This is
the first power sum that involves **all four** elementary symmetric functions, including the new
top function `e₄ = det` *together with* the genuinely intermediate `e₂` (pairwise-minor sum) and
`e₃` (triple-minor sum), so it is qualitatively richer than the `3 × 3` case (whose `p₃` skips
`e₄` entirely).

## Results

* `det_fin_four` — the explicit Laplace expansion of a `4 × 4` determinant over any commutative
  ring (Mathlib stops at `det_fin_three`).  Built by recursing `det_succ_row_zero` to the
  `1 × 1` base case, exactly as Mathlib derives `det_fin_three`, one level deeper.

* `trace_pow_four` — `tr(A⁴) = Σᵢⱼₖₗ Aᵢⱼ Aⱼₖ Aₖₗ Aₗᵢ`, the quadruple-sum entry form of the
  trace of `A⁴`, over any commutative ring.

* `trace_four_fin_four` — the **matrix-side Newton identity**, over *any* commutative ring:

        tr(A⁴) = (tr A)⁴ − 4 (tr A)² e₂(A) + 2 e₂(A)² + 4 (tr A) e₃(A) − 4 det A,

  where `e₂(A)` is the sum of the six principal `2 × 2` minors and `e₃(A)` the sum of the four
  principal `3 × 3` minors.  A polynomial identity in the sixteen entries, closed by `ring`
  with no field, no algebraic closure, and no eigenvalues.

* `charpoly_fin_four` — the `4 × 4` characteristic polynomial in elementary-symmetric form
  `X⁴ − (tr A) X³ + e₂(A) X² − e₃(A) X + det A`, identifying `e₂(A)` and `e₃(A)` as the
  `X²`- and (negated) `X¹`-coefficients.

* `trace_pow_four_eq_sum_pow_four_eigenvalues` — the **spectral form**, over an algebraically
  closed field: `tr(A⁴) = Σ λᵢ⁴`, the fourth power sum of the eigenvalue multiset.  The proof
  matches the matrix-side identity to the four-variable multiset identity
  `a⁴+b⁴+c⁴+d⁴ = s₁⁴ − 4 s₁² s₂ + 2 s₂² + 4 s₁ s₃ − 4 s₄`, using Vieta
  (`charpoly = ∏ (X − λᵢ)`) to identify the four elementary symmetric functions of the
  eigenvalues with `tr A`, `e₂(A)`, `e₃(A)`, and `det A`.

## Honesty / scope

The matrix-side identity and `det_fin_four` are routine but genuinely new at `k = 4` /
dimension four (Mathlib provides neither `det_fin_four` nor the `p₄` identity).  The spectral
upgrade reuses the parent/grandparent infrastructure (`eigenvalues`,
`charpoly_coeff_eq_esymm_eigenvalues`, `trace_eq_sum_eigenvalues`, `det_eq_prod_eigenvalues`).
No `native_decide`; `#print axioms` confirms only `propext, Classical.choice, Quot.sound`.
-/

namespace SpectralTraceDetEigenvaluesOQ01OQ01OQ02OQ01

open Matrix Finset Polynomial
open SpectralTraceDetEigenvaluesOQ01 (eigenvalues)

/-! ## Part I: the intermediate elementary symmetric functions and the `4 × 4` determinant -/

variable {R : Type*} [CommRing R]

/-- The **second elementary symmetric function** of a `4 × 4` matrix: the sum of its six
principal `2 × 2` minors.  For a matrix with eigenvalues `a, b, c, d` this equals
`ab + ac + ad + bc + bd + cd`. -/
def e2 (A : Matrix (Fin 4) (Fin 4) R) : R :=
  (A 0 0 * A 1 1 - A 0 1 * A 1 0) + (A 0 0 * A 2 2 - A 0 2 * A 2 0)
    + (A 0 0 * A 3 3 - A 0 3 * A 3 0) + (A 1 1 * A 2 2 - A 1 2 * A 2 1)
    + (A 1 1 * A 3 3 - A 1 3 * A 3 1) + (A 2 2 * A 3 3 - A 2 3 * A 3 2)

/-- The **third elementary symmetric function** of a `4 × 4` matrix: the sum of its four
principal `3 × 3` minors (rows/columns `{0,1,2}`, `{0,1,3}`, `{0,2,3}`, `{1,2,3}`).  For a
matrix with eigenvalues `a, b, c, d` this equals `abc + abd + acd + bcd`. -/
def e3 (A : Matrix (Fin 4) (Fin 4) R) : R :=
  (A 0 0 * (A 1 1 * A 2 2 - A 1 2 * A 2 1) - A 0 1 * (A 1 0 * A 2 2 - A 1 2 * A 2 0)
      + A 0 2 * (A 1 0 * A 2 1 - A 1 1 * A 2 0))
  + (A 0 0 * (A 1 1 * A 3 3 - A 1 3 * A 3 1) - A 0 1 * (A 1 0 * A 3 3 - A 1 3 * A 3 0)
      + A 0 3 * (A 1 0 * A 3 1 - A 1 1 * A 3 0))
  + (A 0 0 * (A 2 2 * A 3 3 - A 2 3 * A 3 2) - A 0 2 * (A 2 0 * A 3 3 - A 2 3 * A 3 0)
      + A 0 3 * (A 2 0 * A 3 2 - A 2 2 * A 3 0))
  + (A 1 1 * (A 2 2 * A 3 3 - A 2 3 * A 3 2) - A 1 2 * (A 2 1 * A 3 3 - A 2 3 * A 3 1)
      + A 1 3 * (A 2 1 * A 3 2 - A 2 2 * A 3 1))

set_option maxHeartbeats 2000000 in
/-- **Determinant of a `4 × 4` matrix.**  Mathlib provides `det_fin_three` but stops there; this
extends the Laplace cofactor expansion one dimension further, by recursing `det_succ_row_zero`
down to the `1 × 1` base case (`det_unique`), exactly as Mathlib derives `det_fin_three`. -/
theorem det_fin_four (A : Matrix (Fin 4) (Fin 4) R) :
    A.det =
      A 0 0 * (A 1 1 * (A 2 2 * A 3 3 - A 2 3 * A 3 2) - A 1 2 * (A 2 1 * A 3 3 - A 2 3 * A 3 1)
          + A 1 3 * (A 2 1 * A 3 2 - A 2 2 * A 3 1))
        - A 0 1 * (A 1 0 * (A 2 2 * A 3 3 - A 2 3 * A 3 2) - A 1 2 * (A 2 0 * A 3 3 - A 2 3 * A 3 0)
          + A 1 3 * (A 2 0 * A 3 2 - A 2 2 * A 3 0))
        + A 0 2 * (A 1 0 * (A 2 1 * A 3 3 - A 2 3 * A 3 1) - A 1 1 * (A 2 0 * A 3 3 - A 2 3 * A 3 0)
          + A 1 3 * (A 2 0 * A 3 1 - A 2 1 * A 3 0))
        - A 0 3 * (A 1 0 * (A 2 1 * A 3 2 - A 2 2 * A 3 1) - A 1 1 * (A 2 0 * A 3 2 - A 2 2 * A 3 0)
          + A 1 2 * (A 2 0 * A 3 1 - A 2 1 * A 3 0)) := by
  simp only [det_succ_row_zero, submatrix_apply, Fin.succ_zero_eq_one, submatrix_submatrix,
    det_unique, Fin.default_eq_zero, Function.comp_apply, Fin.succ_one_eq_two, Fin.sum_univ_succ,
    Fin.val_zero, Fin.zero_succAbove, univ_unique, Fin.val_succ, Fin.val_eq_zero,
    Fin.succ_succAbove_zero, sum_singleton, Fin.succ_succAbove_one, Fin.isValue,
    (show ((2 : Fin 3).succ : Fin 4) = 3 from rfl),
    (show Fin.succAbove (1 : Fin 4) 2 = 3 from rfl),
    (show Fin.succAbove (2 : Fin 4) 2 = 3 from rfl),
    (show Fin.succAbove (3 : Fin 4) 2 = 2 from rfl)]
  ring

set_option maxHeartbeats 4000000 in
/-- **Trace of `A⁴` as a quadruple entry sum:** `tr(A⁴) = Σᵢⱼₖₗ Aᵢⱼ Aⱼₖ Aₖₗ Aₗᵢ`. -/
theorem trace_pow_four (A : Matrix (Fin 4) (Fin 4) R) :
    (A ^ 4).trace = ∑ i, ∑ j, ∑ k, ∑ l, A i j * A j k * A k l * A l i := by
  simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1; ext i; congr 1; ext l
  rw [Finset.sum_comm]
  congr 1; ext k; congr 1; ext j
  ring

set_option maxHeartbeats 4000000 in
/-- **The matrix-side Newton identity `p₄ = e₁⁴ − 4 e₁² e₂ + 2 e₂² + 4 e₁ e₃ − 4 e₄` in
dimension four.**  Over any commutative ring, the trace of `A⁴` is determined by the trace, the
two intermediate minor-sums, and the determinant of `A`:

      tr(A⁴) = (tr A)⁴ − 4 (tr A)² e₂(A) + 2 e₂(A)² + 4 (tr A) e₃(A) − 4 det A. -/
theorem trace_four_fin_four (A : Matrix (Fin 4) (Fin 4) R) :
    (A ^ 4).trace =
      A.trace ^ 4 - 4 * A.trace ^ 2 * e2 A + 2 * e2 A ^ 2
        + 4 * A.trace * e3 A - 4 * A.det := by
  rw [trace_pow_four, det_fin_four]
  simp only [Fin.sum_univ_four, Matrix.trace, Matrix.diag, e2, e3]
  ring

/-! ## Part II: the characteristic polynomial in elementary-symmetric form -/

set_option maxHeartbeats 4000000 in
/-- **The `4 × 4` characteristic polynomial in elementary-symmetric form.**
`charpoly A = X⁴ − (tr A) X³ + e₂(A) X² − e₃(A) X + det A`. -/
theorem charpoly_fin_four (A : Matrix (Fin 4) (Fin 4) R) :
    A.charpoly = X ^ 4 - C A.trace * X ^ 3 + C (e2 A) * X ^ 2 - C (e3 A) * X + C A.det := by
  have htr : A.trace = A 0 0 + A 1 1 + A 2 2 + A 3 3 := by
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_four]
  rw [Matrix.charpoly, det_fin_four (Matrix.charmatrix A), det_fin_four A, e2, e3, htr]
  simp only [Matrix.charmatrix_apply_eq, Matrix.charmatrix_apply_ne, Fin.isValue,
    ne_eq, Fin.reduceEq, not_false_eq_true, map_add, map_sub, map_mul]
  ring

/-- `e₂(A)` is the `X²`-coefficient of the characteristic polynomial of a `4 × 4` matrix. -/
theorem charpoly_coeff_two_eq_e2 (A : Matrix (Fin 4) (Fin 4) R) :
    A.charpoly.coeff 2 = e2 A := by
  rw [charpoly_fin_four]
  simp [coeff_X_pow, coeff_C, coeff_C_mul, coeff_sub, coeff_add, coeff_X]

/-- `e₃(A)` is the negated `X¹`-coefficient of the characteristic polynomial of a `4 × 4`
matrix. -/
theorem charpoly_coeff_one_eq_neg_e3 (A : Matrix (Fin 4) (Fin 4) R) :
    A.charpoly.coeff 1 = -e3 A := by
  rw [charpoly_fin_four]
  simp [coeff_X_pow, coeff_C, coeff_C_mul, coeff_sub, coeff_add, coeff_X]

/-! ## Part III: the spectral form `tr(A⁴) = Σ λᵢ⁴` over an algebraically closed field -/

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- A `4 × 4` matrix over an algebraically closed field has exactly four eigenvalues. -/
theorem card_eigenvalues_fin_four (A : Matrix (Fin 4) (Fin 4) K) :
    Multiset.card (eigenvalues A) = 4 := by
  rw [SpectralTraceDetEigenvaluesOQ01.card_eigenvalues_eq_dim]
  simp

/-- The characteristic polynomial factors over the eigenvalues (Vieta). -/
theorem charpoly_eq_prod_eigenvalues (A : Matrix (Fin 4) (Fin 4) K) :
    A.charpoly = ((eigenvalues A).map (fun r => X - C r)).prod :=
  (IsAlgClosed.splits A.charpoly).eq_prod_roots_of_monic A.charpoly_monic

set_option maxHeartbeats 1000000 in
/-- **Newton's fourth power-sum identity, spectral form.**  Over an algebraically closed field,
the trace of `A⁴` is the sum of the fourth powers of the eigenvalues of the `4 × 4` matrix `A`:

      tr(A⁴) = λ₁⁴ + λ₂⁴ + λ₃⁴ + λ₄⁴.

The proof identifies the four elementary symmetric functions of the eigenvalues `a, b, c, d` with
`tr A = a+b+c+d`, `e₂(A) = ab+ac+ad+bc+bd+cd`, `e₃(A) = abc+abd+acd+bcd`, and `det A = abcd`
(the first and last from the grandparent, the middle two from `charpoly_fin_four` + Vieta), then
matches the matrix-side Newton identity `trace_four_fin_four` against the elementary four-variable
multiset identity `a⁴+b⁴+c⁴+d⁴ = s₁⁴ − 4 s₁² s₂ + 2 s₂² + 4 s₁ s₃ − 4 s₄`. -/
theorem trace_pow_four_eq_sum_pow_four_eigenvalues (A : Matrix (Fin 4) (Fin 4) K) :
    (A ^ 4).trace = ((eigenvalues A).map (· ^ 4)).sum := by
  obtain ⟨a, b, c, d, habcd⟩ := Multiset.card_eq_four.mp (card_eigenvalues_fin_four A)
  -- the characteristic polynomial, factored over the eigenvalues, in expanded Vieta form
  have hprod : ((eigenvalues A).map (fun r => X - C r)).prod
      = X ^ 4 - C (a + b + c + d) * X ^ 3
          + C (a * b + a * c + a * d + b * c + b * d + c * d) * X ^ 2
          - C (a * b * c + a * b * d + a * c * d + b * c * d) * X + C (a * b * c * d) := by
    rw [habcd]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton]
    simp only [map_add, map_mul]; ring
  -- the four elementary symmetric functions of the eigenvalues
  have htr : A.trace = a + b + c + d := by
    rw [SpectralTraceDetEigenvaluesOQ01.trace_eq_sum_eigenvalues, habcd]
    simp [add_assoc]
  have hdet : A.det = a * b * c * d := by
    rw [SpectralTraceDetEigenvaluesOQ01.det_eq_prod_eigenvalues, habcd]
    simp [mul_assoc]
  have he2 : e2 A = a * b + a * c + a * d + b * c + b * d + c * d := by
    rw [← charpoly_coeff_two_eq_e2, charpoly_eq_prod_eigenvalues, hprod]
    simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
    norm_num
  have he3 : e3 A = a * b * c + a * b * d + a * c * d + b * c * d := by
    have h1 : A.charpoly.coeff 1 = -(a * b * c + a * b * d + a * c * d + b * c * d) := by
      rw [charpoly_eq_prod_eigenvalues, hprod]
      simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
      norm_num
    rw [charpoly_coeff_one_eq_neg_e3] at h1
    exact neg_inj.mp h1
  rw [trace_four_fin_four, htr, hdet, he2, he3, habcd]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton]
  ring

/-! ## Part IV: a concrete illustration -/

/-- For `A = !![1,2,0,0; 0,3,1,0; 4,0,2,1; 1,0,0,5]` the matrix-side identity gives `tr(A⁴)` from
`tr A`, `e₂(A)`, `e₃(A)`, and `det A` without computing eigenvalues. -/
theorem trace_four_example :
    (!![(1 : ℚ), 2, 0, 0; 0, 3, 1, 0; 4, 0, 2, 1; 1, 0, 0, 5] ^ 4).trace
      = (!![(1 : ℚ), 2, 0, 0; 0, 3, 1, 0; 4, 0, 2, 1; 1, 0, 0, 5]).trace ^ 4
        - 4 * (!![(1 : ℚ), 2, 0, 0; 0, 3, 1, 0; 4, 0, 2, 1; 1, 0, 0, 5]).trace ^ 2
            * e2 (!![(1 : ℚ), 2, 0, 0; 0, 3, 1, 0; 4, 0, 2, 1; 1, 0, 0, 5])
        + 2 * e2 (!![(1 : ℚ), 2, 0, 0; 0, 3, 1, 0; 4, 0, 2, 1; 1, 0, 0, 5]) ^ 2
        + 4 * (!![(1 : ℚ), 2, 0, 0; 0, 3, 1, 0; 4, 0, 2, 1; 1, 0, 0, 5]).trace
            * e3 (!![(1 : ℚ), 2, 0, 0; 0, 3, 1, 0; 4, 0, 2, 1; 1, 0, 0, 5])
        - 4 * (!![(1 : ℚ), 2, 0, 0; 0, 3, 1, 0; 4, 0, 2, 1; 1, 0, 0, 5]).det :=
  trace_four_fin_four _

end SpectralTraceDetEigenvaluesOQ01OQ01OQ02OQ01

-- Axiom audit: only the standard foundational axioms — no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01OQ02OQ01.trace_four_fin_four
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01OQ02OQ01.trace_pow_four_eq_sum_pow_four_eigenvalues
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01OQ02OQ01.charpoly_fin_four
