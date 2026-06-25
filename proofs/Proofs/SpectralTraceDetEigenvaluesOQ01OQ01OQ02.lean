import Mathlib
import Proofs.SpectralTraceDetEigenvaluesOQ01

/-
# Spectral trace, OQ-01 → OQ-01 → OQ-02: Newton's identity `tr(A³) = Σ λᵢ³` in dimension three

## What this file proves

The sibling `spectral-trace-det-eigenvalues-oq-01-oq-01`
(`SpectralTraceDetEigenvaluesOQ01OQ01.lean`) reached the first power-sum identity
`tr(A²) = λ₁² + λ₂²` for `2 × 2` matrices, via **Newton's identity** `p₂ = e₁² − 2 e₂` — there
`e₂` is just the determinant, the *top* elementary symmetric function, so no intermediate
symmetric function appears.  Its open question asks to extend this to the next power sum and the
next dimension:

      tr(A³) = e₁³ − 3 e₁ e₂ + 3 e₃          (Newton's identity `p₃`),

and to read it as the genuinely spectral statement `tr(A³) = λ₁³ + λ₂³ + λ₃³` for `3 × 3`
matrices.  This is the first power sum whose Newton expansion involves the *middle* elementary
symmetric function `e₂` (the sum of the principal `2 × 2` minors, equivalently the `X¹`
coefficient of the characteristic polynomial), so it is qualitatively harder than the `2 × 2`
case.

## Results

* `trace_cube_fin_three` — the **matrix-side Newton identity**, over *any* commutative ring:

        tr(A³) = (tr A)³ − 3 (tr A) e₂(A) + 3 det A,

  where `e₂(A)` is the sum of the principal `2 × 2` minors.  This holds with no field, no
  algebraic closure, and no eigenvalues — it is a polynomial identity in the nine entries,
  closed by `ring`.

* `charpoly_fin_three` / `charpoly_coeff_one_eq_e2` — the `3 × 3` characteristic polynomial in
  elementary-symmetric form `X³ − (tr A) X² + e₂(A) X − det A`, identifying `e₂(A)` as its
  `X¹`-coefficient.

* `trace_cube_eq_sum_cube_eigenvalues` — the **spectral form**, over an algebraically closed
  field: `tr(A³) = Σ λᵢ³`, the third power sum of the eigenvalue multiset.  The proof matches the
  matrix-side identity to the multiset identity `a³+b³+c³ = (a+b+c)³ − 3(a+b+c)(ab+ac+bc)+3abc`,
  using Vieta (`charpoly = ∏ (X − λᵢ)`) to identify the three elementary symmetric functions of
  the eigenvalues with `tr A`, `e₂(A)`, and `det A`.

## Honesty / scope

The matrix-side identity and its `ring` proof are routine but genuinely new at `k = 3`; the
spectral upgrade reuses the sibling/parent infrastructure (`eigenvalues`,
`charpoly_coeff_eq_esymm_eigenvalues`, `trace_eq_sum_eigenvalues`, `det_eq_prod_eigenvalues`).
No `native_decide`; `#print axioms` confirms only `propext, Classical.choice, Quot.sound`.
-/

namespace SpectralTraceDetEigenvaluesOQ01OQ01OQ02

open Matrix Polynomial
open SpectralTraceDetEigenvaluesOQ01 (eigenvalues)

/-! ## Part I: the second elementary symmetric function and the matrix-side Newton identity -/

variable {R : Type*} [CommRing R]

/-- The **second elementary symmetric function** of a `3 × 3` matrix: the sum of its three
principal `2 × 2` minors.  For a matrix with eigenvalues `a, b, c` this equals `ab + ac + bc`. -/
def e2 (A : Matrix (Fin 3) (Fin 3) R) : R :=
  (A 0 0 * A 1 1 - A 0 1 * A 1 0)
    + (A 0 0 * A 2 2 - A 0 2 * A 2 0)
    + (A 1 1 * A 2 2 - A 1 2 * A 2 1)

/-- **The matrix-side Newton identity `p₃ = e₁³ − 3 e₁ e₂ + 3 e₃` in dimension three.**
Over any commutative ring, the trace of `A³` is determined by the trace, the second elementary
symmetric function (minor sum), and the determinant of `A`:

      tr(A³) = (tr A)³ − 3 (tr A) e₂(A) + 3 det A.

A polynomial identity in the nine entries, closed by `ring`. -/
theorem trace_cube_fin_three (A : Matrix (Fin 3) (Fin 3) R) :
    (A ^ 3).trace = A.trace ^ 3 - 3 * A.trace * e2 A + 3 * A.det := by
  simp only [pow_three, Matrix.trace_fin_three, Matrix.det_fin_three, Matrix.mul_apply,
    Fin.sum_univ_three, e2]
  ring

/-! ## Part II: the characteristic polynomial in elementary-symmetric form -/

/-- **The `3 × 3` characteristic polynomial in elementary-symmetric form.**
`charpoly A = X³ − (tr A) X² + e₂(A) X − det A`. -/
theorem charpoly_fin_three (A : Matrix (Fin 3) (Fin 3) R) :
    A.charpoly = X ^ 3 - C A.trace * X ^ 2 + C (e2 A) * X - C A.det := by
  have htr : A.trace = A 0 0 + A 1 1 + A 2 2 := Matrix.trace_fin_three A
  have hdet : A.det = A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1
      - A 0 1 * A 1 0 * A 2 2 + A 0 1 * A 1 2 * A 2 0
      + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0 := Matrix.det_fin_three A
  rw [show A.charpoly = (Matrix.charmatrix A).det from rfl, Matrix.det_fin_three, htr, hdet, e2]
  simp only [Matrix.charmatrix_apply_eq, Matrix.charmatrix_apply_ne, Fin.isValue,
    ne_eq, Fin.reduceEq, not_false_eq_true, map_add, map_sub, map_mul]
  ring

/-- `e₂(A)` is the `X¹`-coefficient of the characteristic polynomial of a `3 × 3` matrix. -/
theorem charpoly_coeff_one_eq_e2 (A : Matrix (Fin 3) (Fin 3) R) :
    A.charpoly.coeff 1 = e2 A := by
  rw [charpoly_fin_three]
  simp [coeff_X_pow, coeff_C, coeff_C_mul, coeff_sub, coeff_add]

/-! ## Part III: the spectral form `tr(A³) = Σ λᵢ³` over an algebraically closed field -/

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- A `3 × 3` matrix over an algebraically closed field has exactly three eigenvalues. -/
theorem card_eigenvalues_fin_three (A : Matrix (Fin 3) (Fin 3) K) :
    Multiset.card (eigenvalues A) = 3 := by
  rw [SpectralTraceDetEigenvaluesOQ01.card_eigenvalues_eq_dim]
  simp

/-- The characteristic polynomial factors over the eigenvalues (Vieta). -/
theorem charpoly_eq_prod_eigenvalues (A : Matrix (Fin 3) (Fin 3) K) :
    A.charpoly = ((eigenvalues A).map (fun r => X - C r)).prod :=
  (IsAlgClosed.splits A.charpoly).eq_prod_roots_of_monic A.charpoly_monic

/-- **Newton's third power-sum identity, spectral form.**  Over an algebraically closed field,
the trace of `A³` is the sum of the cubes of the eigenvalues of the `3 × 3` matrix `A`:

      tr(A³) = λ₁³ + λ₂³ + λ₃³.

The proof identifies the three elementary symmetric functions of the eigenvalues `a, b, c` with
`tr A = a+b+c`, `e₂(A) = ab+ac+bc`, and `det A = abc` (the first and last from the parent, the
middle one from `charpoly_coeff_one_eq_e2` + Vieta), then matches the matrix-side Newton identity
`trace_cube_fin_three` against the elementary multiset identity
`a³+b³+c³ = (a+b+c)³ − 3(a+b+c)(ab+ac+bc) + 3abc`. -/
theorem trace_cube_eq_sum_cube_eigenvalues (A : Matrix (Fin 3) (Fin 3) K) :
    (A ^ 3).trace = ((eigenvalues A).map (· ^ 3)).sum := by
  obtain ⟨a, b, c, habc⟩ := Multiset.card_eq_three.mp (card_eigenvalues_fin_three A)
  -- the three elementary symmetric functions of the eigenvalues
  have htr : A.trace = a + b + c := by
    rw [SpectralTraceDetEigenvaluesOQ01.trace_eq_sum_eigenvalues, habc]
    simp [add_assoc]
  have hdet : A.det = a * b * c := by
    rw [SpectralTraceDetEigenvaluesOQ01.det_eq_prod_eigenvalues, habc]
    simp [mul_assoc]
  have he2 : e2 A = a * b + a * c + b * c := by
    have hcoeff : A.charpoly.coeff 1 = a * b + a * c + b * c := by
      rw [charpoly_eq_prod_eigenvalues, habc]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
        Multiset.prod_cons, Multiset.prod_singleton]
      have : (X - C a) * ((X - C b) * (X - C c))
          = X ^ 3 - C (a + b + c) * X ^ 2 + C (a * b + a * c + b * c) * X - C (a * b * c) := by
        simp only [map_add, map_mul]; ring
      rw [this]
      simp [coeff_X_pow, coeff_C, coeff_sub, coeff_add, coeff_mul_X_pow', coeff_mul_X]
    rw [← charpoly_coeff_one_eq_e2]; exact hcoeff
  rw [trace_cube_fin_three, htr, hdet, he2, habc]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton]
  ring

/-! ## Part IV: a concrete illustration -/

/-- For `A = !![1,2,0; 0,3,1; 4,0,2]` the matrix-side identity gives `tr(A³)` from
`tr A = 6`, `e₂(A)`, and `det A` without computing eigenvalues. -/
theorem trace_cube_example :
    (!![(1 : ℚ), 2, 0; 0, 3, 1; 4, 0, 2] ^ 3).trace
      = (!![(1 : ℚ), 2, 0; 0, 3, 1; 4, 0, 2]).trace ^ 3
        - 3 * (!![(1 : ℚ), 2, 0; 0, 3, 1; 4, 0, 2]).trace
            * e2 (!![(1 : ℚ), 2, 0; 0, 3, 1; 4, 0, 2])
        + 3 * (!![(1 : ℚ), 2, 0; 0, 3, 1; 4, 0, 2]).det :=
  trace_cube_fin_three _

end SpectralTraceDetEigenvaluesOQ01OQ01OQ02

-- Axiom audit: only the standard foundational axioms — no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01OQ02.trace_cube_fin_three
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01OQ02.trace_cube_eq_sum_cube_eigenvalues
#print axioms SpectralTraceDetEigenvaluesOQ01OQ01OQ02.charpoly_coeff_one_eq_e2
