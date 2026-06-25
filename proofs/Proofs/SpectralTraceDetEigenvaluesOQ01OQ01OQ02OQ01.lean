import Mathlib
import Proofs.SpectralTraceDetEigenvaluesOQ01

/-
# Spectral trace, OQ-01 → OQ-01 → OQ-02 → OQ-01: Newton's identity `tr(A⁴) = Σ λᵢ⁴` in dimension four

## What this file proves

The parent `spectral-trace-det-eigenvalues-oq-01-oq-01-oq-02`
(`SpectralTraceDetEigenvaluesOQ01OQ01OQ02.lean`) reached Newton's **third** power-sum identity
`tr(A³) = e₁³ − 3 e₁ e₂ + 3 e₃` for `3 × 3` matrices — the first power sum whose Newton expansion
involves the *middle* elementary symmetric function `e₂`.  Its open question asks for the next
power sum and the next dimension:

      tr(A⁴) = e₁⁴ − 4 e₁² e₂ + 2 e₂² + 4 e₁ e₃ − 4 e₄          (Newton's identity `p₄`),

read as the genuinely spectral statement `tr(A⁴) = λ₁⁴ + λ₂⁴ + λ₃⁴ + λ₄⁴` for `4 × 4` matrices.

This is the **first power sum whose Newton expansion involves all four elementary symmetric
functions** `e₁, e₂, e₃, e₄` of a `4 × 4` matrix — including the new top function `e₄ = det`,
which appears here for the first time in the power-sum hierarchy (`p₂` reaches `e₂`, `p₃` reaches
`e₃`, and only `p₄` reaches `e₄`).  It also exhibits the first *quadratic* symmetric term `2 e₂²`,
absent from every lower power sum.  Mathlib provides `det_fin_two`/`det_fin_three` and
`trace_fin_two`/`trace_fin_three` but **neither `det_fin_four` nor `trace_fin_four`**, so the
`4 × 4` determinant expansion is built here from the cofactor rule `det_succ_row_zero`.

## Results

* `det_fin_four` — the full `4 × 4` Leibniz expansion (24 signed terms), built from the cofactor
  rule and `det_fin_three`.  Used to unfold `e₄ = det` into matrix entries.

* `trace_fourth_fin_four` — the **matrix-side Newton identity**, over *any* commutative ring:

        tr(A⁴) = (tr A)⁴ − 4 (tr A)² e₂(A) + 2 e₂(A)² + 4 (tr A) e₃(A) − 4 det A,

  where `e₂(A)` is the sum of the six principal `2 × 2` minors and `e₃(A)` the sum of the four
  principal `3 × 3` minors.  No field, no algebraic closure, no eigenvalues — a polynomial
  identity in the sixteen entries, closed by `ring`.

* `charpoly_fin_four` / `charpoly_coeff_two_eq_e2` / `charpoly_coeff_one_eq_neg_e3` — the `4 × 4`
  characteristic polynomial in elementary-symmetric form
  `X⁴ − (tr A) X³ + e₂(A) X² − e₃(A) X + det A`, identifying `e₂(A)` and `e₃(A)` as its `X²`- and
  `X¹`-coefficients.

* `trace_fourth_eq_sum_fourth_eigenvalues` — the **spectral form**, over an algebraically closed
  field: `tr(A⁴) = Σ λᵢ⁴`, the fourth power sum of the eigenvalue multiset.  The proof matches
  the matrix-side identity to the multiset identity, using Vieta (`charpoly = ∏ (X − λᵢ)`) to
  identify the four elementary symmetric functions of the eigenvalues with `tr A`, `e₂(A)`,
  `e₃(A)`, and `det A`.

## Honesty / scope

The matrix-side identity and its `ring` proof are routine in spirit but genuinely new at `k = 4`,
and require building `det_fin_four` (absent from Mathlib).  The spectral upgrade reuses the
parent/grandparent infrastructure (`eigenvalues`, `trace_eq_sum_eigenvalues`,
`det_eq_prod_eigenvalues`).  No `native_decide`; `#print axioms` confirms only
`propext, Classical.choice, Quot.sound`.
-/

namespace SpectralTraceDetEigenvaluesOQ01OQ01OQ02OQ01

open Matrix Polynomial
open SpectralTraceDetEigenvaluesOQ01 (eigenvalues)

/-! ## Part I: the `4 × 4` determinant expansion (built — Mathlib stops at `det_fin_three`) -/

variable {R : Type*} [CommRing R]

/-- **The full `4 × 4` Leibniz expansion** (24 signed terms).  Mathlib provides `det_fin_two` and
`det_fin_three` but not `det_fin_four`; we derive it from the cofactor rule `det_succ_row_zero`
followed by `det_fin_three` on each of the four `3 × 3` minors. -/
theorem det_fin_four (A : Matrix (Fin 4) (Fin 4) R) :
    A.det =
      A 0 0 * (A 1 1 * A 2 2 * A 3 3 - A 1 1 * A 2 3 * A 3 2 - A 1 2 * A 2 1 * A 3 3
        + A 1 2 * A 2 3 * A 3 1 + A 1 3 * A 2 1 * A 3 2 - A 1 3 * A 2 2 * A 3 1)
      - A 0 1 * (A 1 0 * A 2 2 * A 3 3 - A 1 0 * A 2 3 * A 3 2 - A 1 2 * A 2 0 * A 3 3
        + A 1 2 * A 2 3 * A 3 0 + A 1 3 * A 2 0 * A 3 2 - A 1 3 * A 2 2 * A 3 0)
      + A 0 2 * (A 1 0 * A 2 1 * A 3 3 - A 1 0 * A 2 3 * A 3 1 - A 1 1 * A 2 0 * A 3 3
        + A 1 1 * A 2 3 * A 3 0 + A 1 3 * A 2 0 * A 3 1 - A 1 3 * A 2 1 * A 3 0)
      - A 0 3 * (A 1 0 * A 2 1 * A 3 2 - A 1 0 * A 2 2 * A 3 1 - A 1 1 * A 2 0 * A 3 2
        + A 1 1 * A 2 2 * A 3 0 + A 1 2 * A 2 0 * A 3 1 - A 1 2 * A 2 1 * A 3 0) := by
  rw [det_succ_row_zero, Fin.sum_univ_four]
  simp only [det_fin_three, submatrix_apply]
  simp only [Fin.isValue, Fin.succAbove, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.lt_def,
    Fin.succ]
  norm_num
  have h2 : ∀ (h : 2 < 4), (⟨2, h⟩ : Fin 4) = 2 := fun _ => rfl
  have h3 : ∀ (h : 3 < 4), (⟨3, h⟩ : Fin 4) = 3 := fun _ => rfl
  simp only [h2, h3]
  ring

/-! ## Part II: the elementary symmetric functions `e₂`, `e₃` of a `4 × 4` matrix -/

/-- The **second elementary symmetric function** of a `4 × 4` matrix: the sum of its six principal
`2 × 2` minors.  For eigenvalues `a, b, c, d` this is `ab+ac+ad+bc+bd+cd`. -/
def e2 (A : Matrix (Fin 4) (Fin 4) R) : R :=
  (A 0 0 * A 1 1 - A 0 1 * A 1 0)
    + (A 0 0 * A 2 2 - A 0 2 * A 2 0)
    + (A 0 0 * A 3 3 - A 0 3 * A 3 0)
    + (A 1 1 * A 2 2 - A 1 2 * A 2 1)
    + (A 1 1 * A 3 3 - A 1 3 * A 3 1)
    + (A 2 2 * A 3 3 - A 2 3 * A 3 2)

/-- The **third elementary symmetric function** of a `4 × 4` matrix: the sum of its four principal
`3 × 3` minors (rows/cols `{1,2,3}`, `{0,2,3}`, `{0,1,3}`, `{0,1,2}`).  For eigenvalues
`a, b, c, d` this is `abc+abd+acd+bcd`. -/
def e3 (A : Matrix (Fin 4) (Fin 4) R) : R :=
  (A 1 1 * A 2 2 * A 3 3 - A 1 1 * A 2 3 * A 3 2 - A 1 2 * A 2 1 * A 3 3
    + A 1 2 * A 2 3 * A 3 1 + A 1 3 * A 2 1 * A 3 2 - A 1 3 * A 2 2 * A 3 1)
  + (A 0 0 * A 2 2 * A 3 3 - A 0 0 * A 2 3 * A 3 2 - A 0 2 * A 2 0 * A 3 3
    + A 0 2 * A 2 3 * A 3 0 + A 0 3 * A 2 0 * A 3 2 - A 0 3 * A 2 2 * A 3 0)
  + (A 0 0 * A 1 1 * A 3 3 - A 0 0 * A 1 3 * A 3 1 - A 0 1 * A 1 0 * A 3 3
    + A 0 1 * A 1 3 * A 3 0 + A 0 3 * A 1 0 * A 3 1 - A 0 3 * A 1 1 * A 3 0)
  + (A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2
    + A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0)

/-! ## Part III: the matrix-side Newton identity `p₄` -/

/-- **The matrix-side Newton identity `p₄ = e₁⁴ − 4 e₁² e₂ + 2 e₂² + 4 e₁ e₃ − 4 e₄` in
dimension four.**  Over any commutative ring,

      tr(A⁴) = (tr A)⁴ − 4 (tr A)² e₂(A) + 2 e₂(A)² + 4 (tr A) e₃(A) − 4 det A.

This is the first power sum reaching the top function `e₄ = det` (and the first with a `2 e₂²`
term).  A polynomial identity in the sixteen entries, closed by `ring`. -/
theorem trace_fourth_fin_four (A : Matrix (Fin 4) (Fin 4) R) :
    (A ^ 4).trace
      = A.trace ^ 4 - 4 * A.trace ^ 2 * e2 A + 2 * e2 A ^ 2
        + 4 * A.trace * e3 A - 4 * A.det := by
  have hpow : A ^ 4 = A * A * A * A := by
    rw [pow_succ, pow_succ, pow_succ, pow_one]
  rw [hpow, det_fin_four]
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_four, Matrix.mul_apply, e2, e3]
  ring

/-! ## Part IV: the characteristic polynomial in elementary-symmetric form -/

/-- **The `4 × 4` characteristic polynomial in elementary-symmetric form.**
`charpoly A = X⁴ − (tr A) X³ + e₂(A) X² − e₃(A) X + det A`. -/
theorem charpoly_fin_four (A : Matrix (Fin 4) (Fin 4) R) :
    A.charpoly = X ^ 4 - C A.trace * X ^ 3 + C (e2 A) * X ^ 2 - C (e3 A) * X + C A.det := by
  have htr : A.trace = A 0 0 + A 1 1 + A 2 2 + A 3 3 := by
    simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_four]
  rw [show A.charpoly = (Matrix.charmatrix A).det from rfl, det_fin_four, htr, e2, e3,
    det_fin_four]
  simp only [Matrix.charmatrix_apply_eq, Matrix.charmatrix_apply_ne, Fin.isValue,
    ne_eq, Fin.reduceEq, not_false_eq_true, map_add, map_sub, map_mul]
  ring

/-- `e₂(A)` is the `X²`-coefficient of the characteristic polynomial of a `4 × 4` matrix. -/
theorem charpoly_coeff_two_eq_e2 (A : Matrix (Fin 4) (Fin 4) R) :
    A.charpoly.coeff 2 = e2 A := by
  rw [charpoly_fin_four]
  simp [coeff_X_pow, coeff_C, coeff_sub, coeff_add, coeff_mul_X_pow', coeff_mul_X]

/-- `e₃(A)` is *minus* the `X¹`-coefficient of the characteristic polynomial of a `4 × 4`
matrix (the sign alternates with the elementary symmetric functions). -/
theorem charpoly_coeff_one_eq_neg_e3 (A : Matrix (Fin 4) (Fin 4) R) :
    A.charpoly.coeff 1 = -e3 A := by
  rw [charpoly_fin_four]
  simp [coeff_X_pow, coeff_C, coeff_sub, coeff_add, coeff_mul_X_pow', coeff_mul_X]

/-! ## Part V: the spectral form `tr(A⁴) = Σ λᵢ⁴` over an algebraically closed field -/

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

/-- **Newton's fourth power-sum identity, spectral form.**  Over an algebraically closed field,
the trace of `A⁴` is the sum of the fourth powers of the eigenvalues of the `4 × 4` matrix `A`:

      tr(A⁴) = λ₁⁴ + λ₂⁴ + λ₃⁴ + λ₄⁴.

The proof identifies the four elementary symmetric functions of the eigenvalues `a, b, c, d` with
`tr A = a+b+c+d`, `e₂(A) = ab+ac+ad+bc+bd+cd`, `e₃(A) = abc+abd+acd+bcd`, and `det A = abcd`
(the first and last from the grandparent, the middle two from the charpoly coefficients + Vieta),
then matches the matrix-side Newton identity `trace_fourth_fin_four` against the elementary
multiset identity for `a⁴+b⁴+c⁴+d⁴`. -/
theorem trace_fourth_eq_sum_fourth_eigenvalues (A : Matrix (Fin 4) (Fin 4) K) :
    (A ^ 4).trace = ((eigenvalues A).map (· ^ 4)).sum := by
  obtain ⟨a, b, c, d, habcd⟩ := Multiset.card_eq_four.mp (card_eigenvalues_fin_four A)
  -- the four elementary symmetric functions of the eigenvalues, via Vieta
  have hexpand : A.charpoly
      = X ^ 4 - C (a + b + c + d) * X ^ 3
        + C (a*b + a*c + a*d + b*c + b*d + c*d) * X ^ 2
        - C (a*b*c + a*b*d + a*c*d + b*c*d) * X + C (a*b*c*d) := by
    rw [charpoly_eq_prod_eigenvalues, habcd]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton]
    have : (X - C a) * ((X - C b) * ((X - C c) * (X - C d)))
        = X ^ 4 - C (a + b + c + d) * X ^ 3
          + C (a*b + a*c + a*d + b*c + b*d + c*d) * X ^ 2
          - C (a*b*c + a*b*d + a*c*d + b*c*d) * X + C (a*b*c*d) := by
      simp only [map_add, map_mul]; ring
    rw [this]
  have htr : A.trace = a + b + c + d := by
    rw [SpectralTraceDetEigenvaluesOQ01.trace_eq_sum_eigenvalues, habcd]
    simp [add_assoc]
  have hdet : A.det = a * b * c * d := by
    rw [SpectralTraceDetEigenvaluesOQ01.det_eq_prod_eigenvalues, habcd]
    simp [mul_assoc]
  have he2 : e2 A = a*b + a*c + a*d + b*c + b*d + c*d := by
    have h := charpoly_coeff_two_eq_e2 A
    rw [hexpand] at h
    simp [coeff_X_pow, coeff_C, coeff_sub, coeff_add, coeff_mul_X_pow',
      coeff_mul_X] at h
    linear_combination -h
  have he3 : e3 A = a*b*c + a*b*d + a*c*d + b*c*d := by
    have h := charpoly_coeff_one_eq_neg_e3 A
    rw [hexpand] at h
    simp [coeff_X_pow, coeff_C, coeff_sub, coeff_add, coeff_mul_X_pow',
      coeff_mul_X] at h
    linear_combination h
  rw [trace_fourth_fin_four, htr, hdet, he2, he3, habcd]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton]
  ring

/-! ## Part VI: a concrete illustration -/

/-- For `A = !![1,2,0,1; 0,3,1,0; 4,0,2,1; 1,0,0,2]` the matrix-side identity gives `tr(A⁴)`
from `tr A`, `e₂(A)`, `e₃(A)`, and `det A` without computing eigenvalues. -/
theorem trace_fourth_example :
    (!![(1 : ℚ), 2, 0, 1; 0, 3, 1, 0; 4, 0, 2, 1; 1, 0, 0, 2] ^ 4).trace
      = (!![(1 : ℚ), 2, 0, 1; 0, 3, 1, 0; 4, 0, 2, 1; 1, 0, 0, 2]).trace ^ 4
        - 4 * (!![(1 : ℚ), 2, 0, 1; 0, 3, 1, 0; 4, 0, 2, 1; 1, 0, 0, 2]).trace ^ 2
            * e2 (!![(1 : ℚ), 2, 0, 1; 0, 3, 1, 0; 4, 0, 2, 1; 1, 0, 0, 2])
        + 2 * e2 (!![(1 : ℚ), 2, 0, 1; 0, 3, 1, 0; 4, 0, 2, 1; 1, 0, 0, 2]) ^ 2
        + 4 * (!![(1 : ℚ), 2, 0, 1; 0, 3, 1, 0; 4, 0, 2, 1; 1, 0, 0, 2]).trace
            * e3 (!![(1 : ℚ), 2, 0, 1; 0, 3, 1, 0; 4, 0, 2, 1; 1, 0, 0, 2])
        - 4 * (!![(1 : ℚ), 2, 0, 1; 0, 3, 1, 0; 4, 0, 2, 1; 1, 0, 0, 2]).det :=
  trace_fourth_fin_four _

end SpectralTraceDetEigenvaluesOQ01OQ01OQ02OQ01

-- Axiom audit: only the standard foundational axioms — no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01OQ02OQ01.trace_fourth_fin_four
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01OQ02OQ01.trace_fourth_eq_sum_fourth_eigenvalues
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01OQ02OQ01.charpoly_coeff_two_eq_e2
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01OQ02OQ01.det_fin_four
