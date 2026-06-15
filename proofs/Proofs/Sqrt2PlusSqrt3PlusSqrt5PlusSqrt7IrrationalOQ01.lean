/-
# Irrationality of √2 + √3 + √5 + √7 (OQ-01 of `sqrt2-plus-sqrt3-plus-sqrt5-irrational`)

## Strategy D — algebraic integer + bounded interval

Let α := √2 + √3 + √5 + √7. We avoid the entire degree-16 minimal-polynomial /
iterated-squaring machinery (Strategy A) and argue purely from integral-closure:

1. **α is an algebraic integer.** Each √k is a root of the monic integer polynomial
   `X² − C k`, hence `IsIntegral ℤ (√k)`. Algebraic integers are closed under addition
   (`IsIntegral.add`), so `IsIntegral ℤ α`.

2. **A rational that is an algebraic integer is an integer.** Assume `α = (q : ℝ)` for some
   `q : ℚ`. Integrality descends along the injective ring map `algebraMap ℚ ℝ`
   (`isIntegral_algebraMap_iff`), giving `IsIntegral ℤ q`. Since `ℤ` is integrally closed in
   its fraction field `ℚ` (`IsIntegrallyClosed.isIntegral_iff`), there is `n : ℤ` with
   `(n : ℚ) = q`, i.e. `α = (n : ℝ)`.

3. **But `8 < α < 9`.** Rational bounds on each radical (`1.41 < √2 < 1.42`, etc.) give
   `8.01 ≤ α` and `α ≤ 8.05`, so `8 < α < 9`. No integer lies strictly between `8` and `9`,
   contradicting `α = (n : ℝ)`. Hence α is irrational. ∎

This is far shorter than the elementary 3-squaring chain (Strategy A) and introduces no new
Mathlib theory — only the standard integral-closure API.
-/

import Mathlib

open Real

namespace Sqrt2PlusSqrt3PlusSqrt5PlusSqrt7IrrationalOQ01

/-- A real number `c` whose square is an integer `m` is an algebraic integer:
`c` is a root of the monic integer polynomial `X² − C m`. -/
theorem isIntegral_of_sq (c : ℝ) (m : ℤ) (hc : c ^ 2 = (m : ℝ)) : IsIntegral ℤ c := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C m, Polynomial.monic_X_pow_sub_C m (by norm_num), ?_⟩
  have : (Polynomial.aeval c) (Polynomial.X ^ 2 - Polynomial.C m) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hc]
    simp
  simpa [Polynomial.aeval_def] using this

/-- Each summand is an algebraic integer over `ℤ`. -/
theorem isIntegral_sqrt_two : IsIntegral ℤ (sqrt 2) :=
  isIntegral_of_sq _ 2 (by rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num)

theorem isIntegral_sqrt_three : IsIntegral ℤ (sqrt 3) :=
  isIntegral_of_sq _ 3 (by rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num)

theorem isIntegral_sqrt_five : IsIntegral ℤ (sqrt 5) :=
  isIntegral_of_sq _ 5 (by rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]; norm_num)

theorem isIntegral_sqrt_seven : IsIntegral ℤ (sqrt 7) :=
  isIntegral_of_sq _ 7 (by rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 7)]; norm_num)

/-- `α = √2 + √3 + √5 + √7` is an algebraic integer (closed under `+`). -/
theorem isIntegral_alpha : IsIntegral ℤ (sqrt 2 + sqrt 3 + sqrt 5 + sqrt 7) :=
  ((isIntegral_sqrt_two.add isIntegral_sqrt_three).add isIntegral_sqrt_five).add
    isIntegral_sqrt_seven

/-- Lower bound: `8 < √2 + √3 + √5 + √7` (via `1.41 + 1.73 + 2.23 + 2.64 = 8.01`). -/
theorem alpha_lower : (8 : ℝ) < sqrt 2 + sqrt 3 + sqrt 5 + sqrt 7 := by
  have b2 : (1.41 : ℝ) < sqrt 2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have b3 : (1.73 : ℝ) < sqrt 3 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have b5 : (2.23 : ℝ) < sqrt 5 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have b7 : (2.64 : ℝ) < sqrt 7 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  linarith

/-- Upper bound: `√2 + √3 + √5 + √7 < 9` (via `1.42 + 1.74 + 2.24 + 2.65 = 8.05`). -/
theorem alpha_upper : sqrt 2 + sqrt 3 + sqrt 5 + sqrt 7 < (9 : ℝ) := by
  have b2 : sqrt 2 < (1.42 : ℝ) := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have b3 : sqrt 3 < (1.74 : ℝ) := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have b5 : sqrt 5 < (2.24 : ℝ) := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have b7 : sqrt 7 < (2.65 : ℝ) := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

/-- **Main theorem**: `√2 + √3 + √5 + √7` is irrational.

Proved via Strategy D: α is an algebraic integer trapped strictly between `8` and `9`, so it
cannot equal any integer; a rational algebraic integer must be an integer, contradiction. -/
theorem irrational_sqrt2_add_sqrt3_add_sqrt5_add_sqrt7 :
    Irrational (sqrt 2 + sqrt 3 + sqrt 5 + sqrt 7) := by
  rintro ⟨q, hq⟩
  -- hq : (q : ℝ) = √2 + √3 + √5 + √7
  -- Step 1: α is integral over ℤ, hence so is (q : ℝ) = algebraMap ℚ ℝ q.
  have hqℝ : IsIntegral ℤ (algebraMap ℚ ℝ q) := by
    rw [eq_ratCast (algebraMap ℚ ℝ) q, hq]; exact isIntegral_alpha
  -- Step 2: descend integrality along the injective ℚ ↪ ℝ, then use ℤ integrally closed.
  have hqℤ : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff (algebraMap ℚ ℝ).injective).mp hqℝ
  obtain ⟨n, hn⟩ := (IsIntegrallyClosed.isIntegral_iff).mp hqℤ
  rw [show algebraMap ℤ ℚ n = (n : ℚ) by simp] at hn
  -- hn : (n : ℚ) = q  ⇒  α = (n : ℝ)
  have hαn : sqrt 2 + sqrt 3 + sqrt 5 + sqrt 7 = (n : ℝ) := by
    rw [← hq, ← hn]; push_cast; ring
  -- Step 3: 8 < α < 9 forces an integer strictly between 8 and 9 — impossible.
  have hlo := alpha_lower
  have hhi := alpha_upper
  rw [hαn] at hlo hhi
  have h8 : (8 : ℤ) < n := by exact_mod_cast hlo
  have h9 : n < (9 : ℤ) := by exact_mod_cast hhi
  omega

end Sqrt2PlusSqrt3PlusSqrt5PlusSqrt7IrrationalOQ01
