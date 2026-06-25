import Mathlib
import Proofs.SpectralTraceDetEigenvaluesOQ01

/-
# Spectral trace, OQ-01 → OQ-01 → OQ-02 → OQ-01: Newton's identity `tr(A⁴) = Σ λᵢ⁴` in dimension four

## What this file proves

The parent (`spectral-trace-det-eigenvalues-oq-01-oq-01-oq-02`,
`SpectralTraceDetEigenvaluesOQ01OQ01OQ02.lean`) proved Newton's **third** power sum
`tr(A³) = e₁³ − 3 e₁ e₂ + 3 e₃` and its spectral reading `tr(A³) = λ₁³ + λ₂³ + λ₃³` for `3 × 3`
matrices.  Its open question asks for the next power sum and the next dimension:

      tr(A⁴) = e₁⁴ − 4 e₁² e₂ + 2 e₂² + 4 e₁ e₃ − 4 e₄          (Newton's identity `p₄`),

read spectrally as `tr(A⁴) = λ₁⁴ + λ₂⁴ + λ₃⁴ + λ₄⁴` for `4 × 4` matrices.  This is the first
power sum in which the elementary symmetric function `e₄ = det` finally **emerges** as an
independent term (it is the top symmetric function at dimension four, absent from every
`p_k` with `k < 4`), and the first whose Newton expansion involves *all four* elementary
symmetric functions `e₁, e₂, e₃, e₄` simultaneously — including the genuinely new `e₃`, the sum
of the four principal `3 × 3` minors.  So it is qualitatively harder than the `3 × 3` cube.

## Results

* `trace_quartic_fin_four` — the **matrix-side Newton identity**, over *any* commutative ring:

        tr(A⁴) = (tr A)⁴ − 4 (tr A)² e₂(A) + 2 e₂(A)² + 4 (tr A) e₃(A) − 4 det A,

  where `e₂(A)` is the sum of the six principal `2 × 2` minors and `e₃(A)` the sum of the four
  principal `3 × 3` minors.  This holds with no field, no algebraic closure, and no eigenvalues —
  it is a polynomial identity in the sixteen entries, closed by `ring`.

* `det_fin_four` / `trace_fin_four` — explicit `4 × 4` determinant (cofactor expansion along the
  top row) and trace expansions over any commutative ring, supplying the `Fin 4` analogues of
  Mathlib's `Matrix.det_fin_three` / `Matrix.trace_fin_three`, which stop at dimension three.

* `charpoly_fin_four` / `charpoly_coeff_two_eq_e2` / `charpoly_coeff_one_eq_neg_e3` — the `4 × 4`
  characteristic polynomial in elementary-symmetric form
  `X⁴ − (tr A) X³ + e₂(A) X² − e₃(A) X + det A`, identifying `e₂(A)` as its `X²`-coefficient and
  `e₃(A)` as the negative of its `X¹`-coefficient.

* `trace_quartic_eq_sum_fourth_eigenvalues` — the **spectral form**, over an algebraically closed
  field: `tr(A⁴) = Σ λᵢ⁴`, the fourth power sum of the eigenvalue multiset.  The proof matches the
  matrix-side identity to the multiset identity
  `a⁴+b⁴+c⁴+d⁴ = e₁⁴ − 4e₁²e₂ + 2e₂² + 4e₁e₃ − 4e₄` in the four eigenvalues, using Vieta
  (`charpoly = ∏ (X − λᵢ)`) to identify the four elementary symmetric functions of the eigenvalues
  with `tr A`, `e₂(A)`, `e₃(A)`, and `det A`.

## Honesty / scope

The matrix-side identity, the `4 × 4` determinant/charpoly expansions, and their `ring` proofs are
routine but genuinely new at `k = 4` (Mathlib's `Fin n` matrix expansions stop at `n = 3`); the
spectral upgrade reuses the base infrastructure (`eigenvalues`,
`card_eigenvalues_eq_dim`, `trace_eq_sum_eigenvalues`, `det_eq_prod_eigenvalues`).  No
`native_decide`; `#print axioms` confirms only `propext, Classical.choice, Quot.sound`.
-/

namespace SpectralTraceDetEigenvaluesOQ01OQ01OQ02OQ01

open Matrix Polynomial
open SpectralTraceDetEigenvaluesOQ01 (eigenvalues)

/-! ## Part I: `4 × 4` trace and determinant expansions (the `Fin 4` analogues Mathlib lacks) -/

variable {R : Type*} [CommRing R]

/-- The trace of a `4 × 4` matrix is the sum of its four diagonal entries.  (The `Fin 4` analogue
of `Matrix.trace_fin_three`, which Mathlib does not provide.) -/
theorem trace_fin_four (M : Matrix (Fin 4) (Fin 4) R) :
    M.trace = M 0 0 + M 1 1 + M 2 2 + M 3 3 := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_four]

/-- **Cofactor (Laplace) expansion of the `4 × 4` determinant along the top row.**  The `Fin 4`
analogue of `Matrix.det_fin_three`, which Mathlib does not provide. -/
theorem det_fin_four (A : Matrix (Fin 4) (Fin 4) R) :
    A.det =
      A 0 0 * (A 1 1 * (A 2 2 * A 3 3 - A 2 3 * A 3 2)
                - A 1 2 * (A 2 1 * A 3 3 - A 2 3 * A 3 1)
                + A 1 3 * (A 2 1 * A 3 2 - A 2 2 * A 3 1))
      - A 0 1 * (A 1 0 * (A 2 2 * A 3 3 - A 2 3 * A 3 2)
                - A 1 2 * (A 2 0 * A 3 3 - A 2 3 * A 3 0)
                + A 1 3 * (A 2 0 * A 3 2 - A 2 2 * A 3 0))
      + A 0 2 * (A 1 0 * (A 2 1 * A 3 3 - A 2 3 * A 3 1)
                - A 1 1 * (A 2 0 * A 3 3 - A 2 3 * A 3 0)
                + A 1 3 * (A 2 0 * A 3 1 - A 2 1 * A 3 0))
      - A 0 3 * (A 1 0 * (A 2 1 * A 3 2 - A 2 2 * A 3 1)
                - A 1 1 * (A 2 0 * A 3 2 - A 2 2 * A 3 0)
                + A 1 2 * (A 2 0 * A 3 1 - A 2 1 * A 3 0)) := by
  simp [Matrix.det_succ_row_zero, Matrix.submatrix_apply, Fin.succAbove, Fin.sum_univ_succ]
  ring

/-! ## Part II: the elementary symmetric functions `e₂`, `e₃` and the matrix-side Newton identity -/

/-- The **second elementary symmetric function** of a `4 × 4` matrix: the sum of its six principal
`2 × 2` minors.  For a matrix with eigenvalues `a, b, c, d` this equals
`ab + ac + ad + bc + bd + cd`. -/
def e2 (A : Matrix (Fin 4) (Fin 4) R) : R :=
  (A 0 0 * A 1 1 - A 0 1 * A 1 0)
  + (A 0 0 * A 2 2 - A 0 2 * A 2 0)
  + (A 0 0 * A 3 3 - A 0 3 * A 3 0)
  + (A 1 1 * A 2 2 - A 1 2 * A 2 1)
  + (A 1 1 * A 3 3 - A 1 3 * A 3 1)
  + (A 2 2 * A 3 3 - A 2 3 * A 3 2)

/-- The **third elementary symmetric function** of a `4 × 4` matrix: the sum of its four principal
`3 × 3` minors (on index sets `{0,1,2}`, `{0,1,3}`, `{0,2,3}`, `{1,2,3}`).  For a matrix with
eigenvalues `a, b, c, d` this equals `abc + abd + acd + bcd`. -/
def e3 (A : Matrix (Fin 4) (Fin 4) R) : R :=
  (A 0 0 * (A 1 1 * A 2 2 - A 1 2 * A 2 1)
    - A 0 1 * (A 1 0 * A 2 2 - A 1 2 * A 2 0)
    + A 0 2 * (A 1 0 * A 2 1 - A 1 1 * A 2 0))
  + (A 0 0 * (A 1 1 * A 3 3 - A 1 3 * A 3 1)
    - A 0 1 * (A 1 0 * A 3 3 - A 1 3 * A 3 0)
    + A 0 3 * (A 1 0 * A 3 1 - A 1 1 * A 3 0))
  + (A 0 0 * (A 2 2 * A 3 3 - A 2 3 * A 3 2)
    - A 0 2 * (A 2 0 * A 3 3 - A 2 3 * A 3 0)
    + A 0 3 * (A 2 0 * A 3 2 - A 2 2 * A 3 0))
  + (A 1 1 * (A 2 2 * A 3 3 - A 2 3 * A 3 2)
    - A 1 2 * (A 2 1 * A 3 3 - A 2 3 * A 3 1)
    + A 1 3 * (A 2 1 * A 3 2 - A 2 2 * A 3 1))

/-- **The matrix-side Newton identity `p₄ = e₁⁴ − 4 e₁² e₂ + 2 e₂² + 4 e₁ e₃ − 4 e₄` in dimension
four.**  Over any commutative ring, the trace of `A⁴` is determined by the trace, the second and
third elementary symmetric functions (the principal `2 × 2`- and `3 × 3`-minor sums), and the
determinant of `A`:

      tr(A⁴) = (tr A)⁴ − 4 (tr A)² e₂(A) + 2 e₂(A)² + 4 (tr A) e₃(A) − 4 det A.

A polynomial identity in the sixteen entries, closed by `ring`. -/
theorem trace_quartic_fin_four (A : Matrix (Fin 4) (Fin 4) R) :
    (A ^ 4).trace
      = A.trace ^ 4 - 4 * A.trace ^ 2 * e2 A + 2 * e2 A ^ 2
        + 4 * A.trace * e3 A - 4 * A.det := by
  rw [show A ^ 4 = A * A * A * A by rw [pow_succ, pow_succ, pow_succ, pow_one],
    trace_fin_four (A * A * A * A), trace_fin_four A, det_fin_four, e2, e3]
  simp only [Matrix.mul_apply, Fin.sum_univ_four]
  ring

/-! ## Part III: the characteristic polynomial in elementary-symmetric form -/

/-- **The `4 × 4` characteristic polynomial in elementary-symmetric form.**
`charpoly A = X⁴ − (tr A) X³ + e₂(A) X² − e₃(A) X + det A`. -/
theorem charpoly_fin_four (A : Matrix (Fin 4) (Fin 4) R) :
    A.charpoly = X ^ 4 - C A.trace * X ^ 3 + C (e2 A) * X ^ 2 - C (e3 A) * X + C A.det := by
  rw [show A.charpoly = (Matrix.charmatrix A).det from rfl, det_fin_four (Matrix.charmatrix A),
    trace_fin_four A, e2, e3, det_fin_four A]
  simp only [Matrix.charmatrix_apply_eq, Matrix.charmatrix_apply_ne, Fin.isValue,
    ne_eq, Fin.reduceEq, not_false_eq_true, map_add, map_sub, map_mul]
  ring

/-- `e₂(A)` is the `X²`-coefficient of the characteristic polynomial of a `4 × 4` matrix. -/
theorem charpoly_coeff_two_eq_e2 (A : Matrix (Fin 4) (Fin 4) R) :
    A.charpoly.coeff 2 = e2 A := by
  rw [charpoly_fin_four]
  simp [coeff_X_pow, coeff_C, coeff_sub, coeff_add, coeff_mul_X_pow', coeff_mul_X]

/-- `e₃(A)` is the negative of the `X¹`-coefficient of the characteristic polynomial of a
`4 × 4` matrix. -/
theorem charpoly_coeff_one_eq_neg_e3 (A : Matrix (Fin 4) (Fin 4) R) :
    A.charpoly.coeff 1 = - e3 A := by
  rw [charpoly_fin_four]
  simp [coeff_X_pow, coeff_C, coeff_sub, coeff_add, coeff_mul_X_pow', coeff_mul_X]

/-! ## Part IV: the spectral form `tr(A⁴) = Σ λᵢ⁴` over an algebraically closed field -/

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
`tr A = a+b+c+d`, `e₂(A) = ab+ac+ad+bc+bd+cd`, `e₃(A) = abc+abd+acd+bcd`, and `det A = abcd` (the
first and last from the base parent, the middle two from `charpoly_coeff_two_eq_e2` /
`charpoly_coeff_one_eq_neg_e3` + Vieta), then matches the matrix-side Newton identity
`trace_quartic_fin_four` against the elementary multiset identity
`a⁴+b⁴+c⁴+d⁴ = e₁⁴ − 4e₁²e₂ + 2e₂² + 4e₁e₃ − 4e₄`. -/
theorem trace_quartic_eq_sum_fourth_eigenvalues (A : Matrix (Fin 4) (Fin 4) K) :
    (A ^ 4).trace = ((eigenvalues A).map (· ^ 4)).sum := by
  obtain ⟨a, b, c, d, habcd⟩ := Multiset.card_eq_four.mp (card_eigenvalues_fin_four A)
  -- the four elementary symmetric functions of the eigenvalues
  have htr : A.trace = a + b + c + d := by
    rw [SpectralTraceDetEigenvaluesOQ01.trace_eq_sum_eigenvalues, habcd]
    simp [add_assoc]
  have hdet : A.det = a * b * c * d := by
    rw [SpectralTraceDetEigenvaluesOQ01.det_eq_prod_eigenvalues, habcd]
    simp [mul_assoc]
  have hprodexp : (X - C a) * ((X - C b) * ((X - C c) * (X - C d)))
      = X ^ 4 - C (a + b + c + d) * X ^ 3
        + C (a * b + a * c + a * d + b * c + b * d + c * d) * X ^ 2
        - C (a * b * c + a * b * d + a * c * d + b * c * d) * X + C (a * b * c * d) := by
    simp only [map_add, map_mul]; ring
  have hcp : A.charpoly = (X - C a) * ((X - C b) * ((X - C c) * (X - C d))) := by
    rw [charpoly_eq_prod_eigenvalues, habcd]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton]
  have he2 : e2 A = a * b + a * c + a * d + b * c + b * d + c * d := by
    have hc : A.charpoly.coeff 2 = a * b + a * c + a * d + b * c + b * d + c * d := by
      rw [hcp, hprodexp]
      simp [coeff_X_pow, coeff_C, coeff_sub, coeff_add, coeff_mul_X_pow', coeff_mul_X]
    rw [← charpoly_coeff_two_eq_e2]; exact hc
  have he3 : e3 A = a * b * c + a * b * d + a * c * d + b * c * d := by
    have hc : A.charpoly.coeff 1 = -(a * b * c + a * b * d + a * c * d + b * c * d) := by
      rw [hcp, hprodexp]
      simp [coeff_X_pow, coeff_C, coeff_sub, coeff_add, coeff_mul_X_pow', coeff_mul_X]
    rw [charpoly_coeff_one_eq_neg_e3] at hc
    exact neg_injective hc
  rw [trace_quartic_fin_four, htr, hdet, he2, he3, habcd]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton]
  ring

/-! ## Part V: a concrete illustration -/

/-- For `A = !![1,2,0,1; 0,3,1,0; 4,0,2,1; 1,1,0,2]` the matrix-side identity gives `tr(A⁴)` from
`tr A`, `e₂(A)`, `e₃(A)`, and `det A` without computing eigenvalues. -/
theorem trace_quartic_example :
    (!![(1 : ℚ), 2, 0, 1; 0, 3, 1, 0; 4, 0, 2, 1; 1, 1, 0, 2] ^ 4).trace
      = (!![(1 : ℚ), 2, 0, 1; 0, 3, 1, 0; 4, 0, 2, 1; 1, 1, 0, 2]).trace ^ 4
        - 4 * (!![(1 : ℚ), 2, 0, 1; 0, 3, 1, 0; 4, 0, 2, 1; 1, 1, 0, 2]).trace ^ 2
            * e2 (!![(1 : ℚ), 2, 0, 1; 0, 3, 1, 0; 4, 0, 2, 1; 1, 1, 0, 2])
        + 2 * e2 (!![(1 : ℚ), 2, 0, 1; 0, 3, 1, 0; 4, 0, 2, 1; 1, 1, 0, 2]) ^ 2
        + 4 * (!![(1 : ℚ), 2, 0, 1; 0, 3, 1, 0; 4, 0, 2, 1; 1, 1, 0, 2]).trace
            * e3 (!![(1 : ℚ), 2, 0, 1; 0, 3, 1, 0; 4, 0, 2, 1; 1, 1, 0, 2])
        - 4 * (!![(1 : ℚ), 2, 0, 1; 0, 3, 1, 0; 4, 0, 2, 1; 1, 1, 0, 2]).det :=
  trace_quartic_fin_four _

end SpectralTraceDetEigenvaluesOQ01OQ01OQ02OQ01

-- Axiom audit: only the standard foundational axioms — no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01OQ02OQ01.trace_quartic_fin_four
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01OQ02OQ01.trace_quartic_eq_sum_fourth_eigenvalues
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01OQ02OQ01.charpoly_fin_four
