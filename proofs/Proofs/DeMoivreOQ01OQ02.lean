import Mathlib

/-
# De Moivre OQ-01-OQ-02: Complex and Hyperbolic Multiple-Angle Formulas via Chebyshev

## Open Question (parent: de-moivre-oq-01)

> Can the Chebyshev connection be extended to complex (or p-adic) settings?
> Specifically: do `T_n` and `U_n` evaluated at `cos z` reproduce `cos (n z)` and the
> sine ratio for *complex* `z`?

## Mathematical Content

Over `ℝ`, the parent file `DeMoivreOQ01.lean` establishes the Chebyshev–De Moivre
dictionary `cos (n θ) = T_n(cos θ)` and `sin ((n+1) θ) = U_n(cos θ) · sin θ`, and
derives explicit multiple-angle formulas up to degree 5.

This file lifts the dictionary to `ℂ` (Mathlib already provides the analytic core via
`T_complex_cos` / `U_complex_cos`) and then exploits a feature with **no real-analytic
analogue**: the *same* Chebyshev polynomial `T_n` simultaneously governs the circular
multiple-angle map (evaluated at `cos z`) **and** the hyperbolic one (evaluated at
`cosh z`), because `cos (i w) = cosh w`. Concretely, one polynomial computation
`T_4 = 8X⁴ - 8X² + 1` yields *both*
  `cos (4 z) = 8 cos⁴ z - 8 cos² z + 1`   and   `cosh (4 z) = 8 cosh⁴ z - 8 cosh² z + 1`.

Mathlib carries the degree ≤ 3 circular/hyperbolic multiple-angle formulas
(`Complex.cos_two_mul`, `Complex.cos_three_mul`, `Complex.cosh_three_mul`, …) but **not**
the degree-4 and degree-5 forms, and not the unifying Chebyshev presentation. Those are
the new content here. The complex De Moivre composition law
`cos (m n · z) = T_m(T_n(cos z))` is also recorded, coming from `Chebyshev.T_mul`.

All results are 0-axiom, no `sorry`, no `native_decide`; the explicit formulas are pure
ring rewrites of the Mathlib evaluation lemmas.

Parent: `DeMoivreOQ01.lean` (real Chebyshev–De Moivre dictionary, 0 axioms).
-/

open Polynomial Polynomial.Chebyshev Complex

namespace DeMoivreOQ01OQ02

-- ============================================================
-- PART 1: Complex Chebyshev–De Moivre dictionary (wrappers)
-- ============================================================

/-- **Complex extraction (cos)**: `cos (n z) = T_n(cos z)` for complex `z`. -/
theorem cos_intMul_eq_eval_T (z : ℂ) (n : ℤ) :
    Complex.cos ((n : ℂ) * z) = (T ℂ n).eval (Complex.cos z) :=
  (T_complex_cos z n).symm

/-- **Complex extraction (sin)**: `sin ((n+1) z) = U_n(cos z) · sin z` for complex `z`. -/
theorem sin_succMul_eq_eval_U (z : ℂ) (n : ℤ) :
    Complex.sin (((n : ℂ) + 1) * z) = (U ℂ n).eval (Complex.cos z) * Complex.sin z :=
  (U_complex_cos z n).symm

/-- **Hyperbolic extraction (cosh)**: `cosh (n z) = T_n(cosh z)`. The *same* `T_n` as the
circular case — this is the unification specific to the complex setting. -/
theorem cosh_intMul_eq_eval_T (z : ℂ) (n : ℤ) :
    Complex.cosh ((n : ℂ) * z) = (T ℂ n).eval (Complex.cosh z) :=
  (T_complex_cosh z n).symm

/-- **Hyperbolic extraction (sinh)**: `sinh ((n+1) z) = U_n(cosh z) · sinh z`. -/
theorem sinh_succMul_eq_eval_U (z : ℂ) (n : ℤ) :
    Complex.sinh (((n : ℂ) + 1) * z) = (U ℂ n).eval (Complex.cosh z) * Complex.sinh z :=
  (U_complex_cosh z n).symm

-- ============================================================
-- PART 2: Existence — `cos (n z)` / `cosh (n z)` are polynomial
-- ============================================================

/-- For every `n`, `cos (n z)` is a (fixed) polynomial in `cos z`, over `ℂ`. -/
theorem cos_intMul_isPolyInCos (n : ℤ) :
    ∃ P : ℂ[X], ∀ z : ℂ, P.eval (Complex.cos z) = Complex.cos ((n : ℂ) * z) :=
  ⟨T ℂ n, fun z => T_complex_cos z n⟩

/-- For every `n`, `cosh (n z)` is a (fixed) polynomial in `cosh z` — the *same* polynomial
that expresses `cos (n z)` in `cos z`. -/
theorem cosh_intMul_isPolyInCosh (n : ℤ) :
    ∃ P : ℂ[X], ∀ z : ℂ, P.eval (Complex.cosh z) = Complex.cosh ((n : ℂ) * z) :=
  ⟨T ℂ n, fun z => T_complex_cosh z n⟩

-- ============================================================
-- PART 3: Explicit Chebyshev polynomials (over ℂ)
-- ============================================================

/-- `T₃ = 4X³ - 3X`. -/
theorem T_three : T ℂ 3 = 4 * X ^ 3 - 3 * X := by
  have h : T ℂ (1 + 2 : ℤ) = 2 * X * T ℂ (1 + 1 : ℤ) - T ℂ 1 := T_add_two (R := ℂ) 1
  simp only [show (1 + 2 : ℤ) = 3 from by decide, show (1 + 1 : ℤ) = 2 from by decide] at h
  rw [h, T_two, T_one]; ring

/-- `T₄ = 8X⁴ - 8X² + 1`. -/
theorem T_four : T ℂ 4 = 8 * X ^ 4 - 8 * X ^ 2 + 1 := by
  have h : T ℂ (2 + 2 : ℤ) = 2 * X * T ℂ (2 + 1 : ℤ) - T ℂ 2 := T_add_two (R := ℂ) 2
  simp only [show (2 + 2 : ℤ) = 4 from by decide, show (2 + 1 : ℤ) = 3 from by decide] at h
  rw [h, T_three, T_two]; ring

/-- `T₅ = 16X⁵ - 20X³ + 5X`. -/
theorem T_five : T ℂ 5 = 16 * X ^ 5 - 20 * X ^ 3 + 5 * X := by
  have h : T ℂ (3 + 2 : ℤ) = 2 * X * T ℂ (3 + 1 : ℤ) - T ℂ 3 := T_add_two (R := ℂ) 3
  simp only [show (3 + 2 : ℤ) = 5 from by decide, show (3 + 1 : ℤ) = 4 from by decide] at h
  rw [h, T_four, T_three]; ring

/-- `U₃ = 8X³ - 4X`. -/
theorem U_three : U ℂ 3 = 8 * X ^ 3 - 4 * X := by
  have h : U ℂ (1 + 2 : ℤ) = 2 * X * U ℂ (1 + 1 : ℤ) - U ℂ 1 := U_add_two (R := ℂ) 1
  simp only [show (1 + 2 : ℤ) = 3 from by decide, show (1 + 1 : ℤ) = 2 from by decide] at h
  rw [h, U_two, U_one]; ring

/-- `U₄ = 16X⁴ - 12X² + 1`. -/
theorem U_four : U ℂ 4 = 16 * X ^ 4 - 12 * X ^ 2 + 1 := by
  have h : U ℂ (2 + 2 : ℤ) = 2 * X * U ℂ (2 + 1 : ℤ) - U ℂ 2 := U_add_two (R := ℂ) 2
  simp only [show (2 + 2 : ℤ) = 4 from by decide, show (2 + 1 : ℤ) = 3 from by decide] at h
  rw [h, U_three, U_two]; ring

-- ============================================================
-- PART 4: Explicit complex multiple-angle formulas (degree 4, 5)
-- (degree ≤ 3 are already in Mathlib)
-- ============================================================

/-- **cos(4z)** over `ℂ`: `cos (4 z) = 8 cos⁴ z - 8 cos² z + 1`. -/
theorem cos_four_mul (z : ℂ) :
    Complex.cos (4 * z) = 8 * Complex.cos z ^ 4 - 8 * Complex.cos z ^ 2 + 1 := by
  have h := T_complex_cos z 4
  rw [T_four] at h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat, eval_one] at h
  rw [show ((4 : ℤ) : ℂ) = (4 : ℂ) from by norm_num] at h
  linear_combination -h

/-- **cos(5z)** over `ℂ`: `cos (5 z) = 16 cos⁵ z - 20 cos³ z + 5 cos z`. -/
theorem cos_five_mul (z : ℂ) :
    Complex.cos (5 * z) = 16 * Complex.cos z ^ 5 - 20 * Complex.cos z ^ 3 + 5 * Complex.cos z := by
  have h := T_complex_cos z 5
  rw [T_five] at h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat] at h
  rw [show ((5 : ℤ) : ℂ) = (5 : ℂ) from by norm_num] at h
  linear_combination -h

/-- **sin(4z)** over `ℂ`: `sin (4 z) = (8 cos³ z - 4 cos z) · sin z`. -/
theorem sin_four_mul (z : ℂ) :
    Complex.sin (4 * z) = (8 * Complex.cos z ^ 3 - 4 * Complex.cos z) * Complex.sin z := by
  have h := U_complex_cos z 3
  rw [U_three] at h
  simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat] at h
  rw [show ((3 : ℤ) : ℂ) + 1 = (4 : ℂ) from by norm_num] at h
  linear_combination -h

/-- **sin(5z)** over `ℂ`: `sin (5 z) = (16 cos⁴ z - 12 cos² z + 1) · sin z`. -/
theorem sin_five_mul (z : ℂ) :
    Complex.sin (5 * z) = (16 * Complex.cos z ^ 4 - 12 * Complex.cos z ^ 2 + 1) * Complex.sin z := by
  have h := U_complex_cos z 4
  rw [U_four] at h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat, eval_one] at h
  rw [show ((4 : ℤ) : ℂ) + 1 = (5 : ℂ) from by norm_num] at h
  linear_combination -h

-- ============================================================
-- PART 5: Explicit hyperbolic multiple-angle formulas (degree 4, 5)
-- Derived from the SAME Chebyshev polynomials as the circular forms.
-- ============================================================

/-- **cosh(4z)**: `cosh (4 z) = 8 cosh⁴ z - 8 cosh² z + 1`. Same `T₄` as `cos_four_mul`. -/
theorem cosh_four_mul (z : ℂ) :
    Complex.cosh (4 * z) = 8 * Complex.cosh z ^ 4 - 8 * Complex.cosh z ^ 2 + 1 := by
  have h := T_complex_cosh z 4
  rw [T_four] at h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat, eval_one] at h
  rw [show ((4 : ℤ) : ℂ) = (4 : ℂ) from by norm_num] at h
  linear_combination -h

/-- **cosh(5z)**: `cosh (5 z) = 16 cosh⁵ z - 20 cosh³ z + 5 cosh z`. Same `T₅` as `cos_five_mul`. -/
theorem cosh_five_mul (z : ℂ) :
    Complex.cosh (5 * z)
      = 16 * Complex.cosh z ^ 5 - 20 * Complex.cosh z ^ 3 + 5 * Complex.cosh z := by
  have h := T_complex_cosh z 5
  rw [T_five] at h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat] at h
  rw [show ((5 : ℤ) : ℂ) = (5 : ℂ) from by norm_num] at h
  linear_combination -h

/-- **sinh(4z)**: `sinh (4 z) = (8 cosh³ z - 4 cosh z) · sinh z`. Same `U₃` as `sin_four_mul`. -/
theorem sinh_four_mul (z : ℂ) :
    Complex.sinh (4 * z) = (8 * Complex.cosh z ^ 3 - 4 * Complex.cosh z) * Complex.sinh z := by
  have h := U_complex_cosh z 3
  rw [U_three] at h
  simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat] at h
  rw [show ((3 : ℤ) : ℂ) + 1 = (4 : ℂ) from by norm_num] at h
  linear_combination -h

/-- **sinh(5z)**: `sinh (5 z) = (16 cosh⁴ z - 12 cosh² z + 1) · sinh z`. Same `U₄` as `sin_five_mul`. -/
theorem sinh_five_mul (z : ℂ) :
    Complex.sinh (5 * z)
      = (16 * Complex.cosh z ^ 4 - 12 * Complex.cosh z ^ 2 + 1) * Complex.sinh z := by
  have h := U_complex_cosh z 4
  rw [U_four] at h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_ofNat, eval_one] at h
  rw [show ((4 : ℤ) : ℂ) + 1 = (5 : ℂ) from by norm_num] at h
  linear_combination -h

-- ============================================================
-- PART 6: Unification and the De Moivre composition law
-- ============================================================

/-- **One polynomial, two trigonometries**: the same `T_n` realizes both the circular and
the hyperbolic `n`-fold angle maps. This is the structural content of moving to `ℂ`. -/
theorem T_eval_cos_and_cosh (z : ℂ) (n : ℤ) :
    (T ℂ n).eval (Complex.cos z) = Complex.cos ((n : ℂ) * z) ∧
    (T ℂ n).eval (Complex.cosh z) = Complex.cosh ((n : ℂ) * z) :=
  ⟨T_complex_cos z n, T_complex_cosh z n⟩

/-- **De Moivre composition law (cos)**: `cos (m n · z) = T_m(T_n(cos z))`, the analytic
shadow of `T_{mn} = T_m ∘ T_n`. -/
theorem cos_mul_eq_T_comp (z : ℂ) (m n : ℤ) :
    Complex.cos (((m * n : ℤ) : ℂ) * z) = (T ℂ m).eval ((T ℂ n).eval (Complex.cos z)) := by
  rw [← eval_comp, ← T_mul, T_complex_cos]

/-- **De Moivre composition law (cosh)**: `cosh (m n · z) = T_m(T_n(cosh z))`. -/
theorem cosh_mul_eq_T_comp (z : ℂ) (m n : ℤ) :
    Complex.cosh (((m * n : ℤ) : ℂ) * z) = (T ℂ m).eval ((T ℂ n).eval (Complex.cosh z)) := by
  rw [← eval_comp, ← T_mul, T_complex_cosh]

end DeMoivreOQ01OQ02
