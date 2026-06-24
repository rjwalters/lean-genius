/-
  Addition formulas for Chebyshev polynomials of the first and second kind.

  The parent file (`Proofs.ChebyshevPolynomialsOQ01`) records the *composition*
  law `T_{m·n} = T_m ∘ T_n` and the commuting-family structure it generates.
  Mathlib supplements this with the *product-to-sum* identity
  `T_mul_T : 2·T_m·T_k = T_{m+k} + T_{m−k}`.  What Mathlib does **not** record is
  the genuine **angle-addition formula** — the polynomial shadow of
  `cos(α+β) = cos α cos β − sin α sin β`:

      **T_{m+n} = T_m · T_n − (1 − X²) · U_{m−1} · U_{n−1}.**

  Here `U` is the Chebyshev polynomial of the second kind, and the factor
  `(1 − X²)` plays the role of `sin²`, since `Uₖ(cos θ)·sin θ = sin((k+1)θ)`.
  This file proves that identity (`T_add`), together with:

  * `T_sub`           — the matching subtraction formula
                        `T_{m−n} = T_m·T_n + (1−X²)·U_{m−1}·U_{n−1}`
                        (the `cos(α−β)` analog);
  * `T_sq_add`        — the Pell / Pythagorean identity obtained at `m = n`,
                        `Tₙ² + (1−X²)·U_{n−1}² = 1`
                        (the polynomial `cos² + sin² = 1`);
  * `U_add`           — the second-kind addition formula
                        `U_{m+n} = U_m·T_n + T_{m+1}·U_{n−1}`
                        (the polynomial `sin(α+β) = sin α cos β + cos α sin β`),
                        which Mathlib likewise omits.

  All identities hold over an arbitrary commutative ring `R` and for all integer
  indices `m, n : ℤ`, with the usual conventions `U_{-1} = 0`, `T_0 = 1`.

  The proofs use Mathlib's two-step integer induction principle
  `Polynomial.Chebyshev.induct`, exactly as `T_mul_T` does: the second-order
  recurrences `T_add_two`/`U_add_two` (and their downward `_sub_two` forms)
  collapse each inductive step, discharged by `linear_combination`.  The `n = 1`
  base cases are precisely Mathlib's mixed recurrences
  `T_eq_X_mul_T_sub_pol_U` and `U_eq_X_mul_U_add_T`.

  Verified: 0 sorries, 0 axioms.
-/
import Mathlib

open Polynomial

namespace ChebyshevPolynomialsOQ01OQ01

open Polynomial.Chebyshev

variable (R : Type*) [CommRing R]

/-- **Addition formula** for Chebyshev polynomials of the first kind:
`T_{m+n} = T_m · T_n − (1 − X²) · U_{m−1} · U_{n−1}`.

This is the polynomial form of `cos(α+β) = cos α cos β − sin α sin β`: writing
`x = cos θ`, the factor `1 − x²` is `sin² θ` and `U_{k−1}(x)·sin θ = sin(k θ)`.
Mathlib records only the product-to-sum identity `T_mul_T`, not this. -/
theorem T_add (m n : ℤ) :
    T R (m + n) = T R m * T R n - (1 - X ^ 2) * U R (m - 1) * U R (n - 1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp [T_zero, U_neg_one]
  | one =>
      have h := T_eq_X_mul_T_sub_pol_U R (m - 1)
      rw [show m - 1 + 2 = m + 1 from by ring, show m - 1 + 1 = m from by ring] at h
      simp only [T_one, sub_self, U_zero, mul_one]
      linear_combination h
  | add_two k ih1 ih2 =>
      have h₁ := T_add_two R (m + k)
      have hT := T_add_two R k
      have hU := U_add_two R (k - 1)
      linear_combination (norm := ring_nf)
        h₁ + 2 * (X : R[X]) * ih1 - ih2 - T R m * hT
          + (1 - (X : R[X]) ^ 2) * U R (m - 1) * hU
  | neg_add_one k ih1 ih2 =>
      have h₁ := T_sub_two R (m + (-(k : ℤ) + 1))
      have hT := T_sub_two R (-(k : ℤ) + 1)
      have hU := U_sub_two R (-(k : ℤ))
      linear_combination (norm := ring_nf)
        h₁ + 2 * (X : R[X]) * ih1 - ih2 - T R m * hT
          + (1 - (X : R[X]) ^ 2) * U R (m - 1) * hU

/-- **Subtraction formula** for the first kind:
`T_{m−n} = T_m · T_n + (1 − X²) · U_{m−1} · U_{n−1}` — the `cos(α−β)` analog.
Obtained from `T_add` at `−n` using `T_{-n} = Tₙ` and `U_{-n-1} = −U_{n-1}`. -/
theorem T_sub (m n : ℤ) :
    T R (m - n) = T R m * T R n + (1 - X ^ 2) * U R (m - 1) * U R (n - 1) := by
  have h := T_add R m (-n)
  rw [T_neg R n, U_neg_sub_one R n] at h
  linear_combination (norm := ring_nf) h

/-- **Pell / Pythagorean identity**: `Tₙ² + (1 − X²)·U_{n−1}² = 1`.
This is the polynomial `cos²(nθ) + sin²(nθ) = 1`, and exhibits `(Tₙ, U_{n−1})`
as a solution of the Pell equation `T² − (X² − 1)·U² = 1`.  It is the diagonal
`m = n` of the subtraction formula, since `T_0 = 1`. -/
theorem T_sq_add (n : ℤ) :
    T R n ^ 2 + (1 - X ^ 2) * U R (n - 1) ^ 2 = 1 := by
  have h := T_sub R n n
  rw [sub_self, T_zero] at h
  linear_combination (norm := ring_nf) -h

/-- **Addition formula** for Chebyshev polynomials of the second kind:
`U_{m+n} = U_m · T_n + T_{m+1} · U_{n−1}` — the polynomial form of
`sin(α+β) = sin α cos β + cos α sin β`.  Mathlib does not record this. -/
theorem U_add (m n : ℤ) :
    U R (m + n) = U R m * T R n + T R (m + 1) * U R (n - 1) := by
  induction n using Polynomial.Chebyshev.induct with
  | zero => simp [T_zero, U_neg_one]
  | one =>
      have h := U_eq_X_mul_U_add_T R m
      simp only [T_one, sub_self, U_zero, mul_one]
      linear_combination h
  | add_two k ih1 ih2 =>
      have h₁ := U_add_two R (m + k)
      have hT := T_add_two R k
      have hU := U_add_two R (k - 1)
      linear_combination (norm := ring_nf)
        h₁ + 2 * (X : R[X]) * ih1 - ih2 - U R m * hT - T R (m + 1) * hU
  | neg_add_one k ih1 ih2 =>
      have h₁ := U_sub_two R (m + (-(k : ℤ) + 1))
      have hT := T_sub_two R (-(k : ℤ) + 1)
      have hU := U_sub_two R (-(k : ℤ))
      linear_combination (norm := ring_nf)
        h₁ + 2 * (X : R[X]) * ih1 - ih2 - U R m * hT - T R (m + 1) * hU

/-! ### Concrete instances -/

/-- `T_{2+3} = T₂·T₃ − (1 − X²)·U_{2−1}·U_{3−1}` over `ℤ`: the addition formula
at `m = 2, n = 3`, stated with the indices exactly as the theorem produces them. -/
example : T ℤ (2 + 3) = T ℤ 2 * T ℤ 3 - (1 - X ^ 2) * U ℤ (2 - 1) * U ℤ (3 - 1) :=
  T_add ℤ 2 3

/-- `U_{2+2} = U₂·T₂ + T_{2+1}·U_{2−1}` over `ℤ`: the second-kind addition formula
at `m = n = 2`. -/
example : U ℤ (2 + 2) = U ℤ 2 * T ℤ 2 + T ℤ (2 + 1) * U ℤ (2 - 1) :=
  U_add ℤ 2 2

end ChebyshevPolynomialsOQ01OQ01
