/-
  The Rational Root Theorem and integrality of roots of monic polynomials.

  **Rational Root Theorem.**  Let `p ∈ ℤ[X]` and let `r = a/b ∈ ℚ` (in lowest
  terms) be a root of `p`.  Then

      a ∣ p.coeff 0      (the numerator divides the constant term),
      b ∣ p.leadingCoeff (the denominator divides the leading coefficient).

  In particular, if `p` is **monic** (leading coefficient `1`) then `b ∣ 1`, so
  every rational root is in fact an INTEGER — the rational roots of a monic
  integer polynomial are integers.

  This is the engine behind the classic irrationality proofs: `√2` is irrational
  because it is a root of the monic `X² − 2`, which has no integer root (no
  integer squares to `2`).

  Mathlib provides the general statements over an integrally closed domain `A`
  with fraction field `K` (`num_dvd_of_is_root`, `den_dvd_of_is_root`,
  `isInteger_of_is_root_of_monic`); here we specialize to `ℤ ⊂ ℚ`, package the
  monic-roots-are-integers corollary, and derive the irrationality of `√2`.
  Fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/
import Mathlib

open Polynomial IsFractionRing

namespace IntegralRootTheoremOQ01

/-! ### The Rational Root Theorem over ℤ ⊂ ℚ -/

/-- **Numerator divides the constant term.** If `r ∈ ℚ` is a root of `p ∈ ℤ[X]`,
its numerator divides `p.coeff 0`. -/
theorem num_dvd_of_root {p : ℤ[X]} {r : ℚ} (hr : aeval r p = 0) :
    num ℤ r ∣ p.coeff 0 :=
  num_dvd_of_is_root hr

/-- **Denominator divides the leading coefficient.** If `r ∈ ℚ` is a root of
`p ∈ ℤ[X]`, its denominator divides `p.leadingCoeff`. -/
theorem den_dvd_of_root {p : ℤ[X]} {r : ℚ} (hr : aeval r p = 0) :
    (den ℤ r : ℤ) ∣ p.leadingCoeff :=
  den_dvd_of_is_root hr

/-- **Roots of a monic integer polynomial are integral.** -/
theorem isInteger_of_monic_root {p : ℤ[X]} (hp : p.Monic) {r : ℚ} (hr : aeval r p = 0) :
    IsLocalization.IsInteger ℤ r :=
  isInteger_of_is_root_of_monic hp hr

/-- **Rational roots of a monic integer polynomial are integers**: if `p` is
monic and `r ∈ ℚ` is a root, then `r = z` for some integer `z`. -/
theorem monic_root_isInteger {p : ℤ[X]} (hp : p.Monic) {r : ℚ} (hr : aeval r p = 0) :
    ∃ z : ℤ, (z : ℚ) = r := by
  obtain ⟨z, hz⟩ := isInteger_of_monic_root hp hr
  exact ⟨z, by rw [← hz]; simp⟩

/-! ### Application: irrationality of √2 -/

/-- No integer squares to `2`. -/
theorem no_int_sq_eq_two : ∀ z : ℤ, z ^ 2 ≠ 2 := by
  intro z hz
  have hb1 : z < 2 := by nlinarith [sq_nonneg (z - 2)]
  have hb2 : -2 < z := by nlinarith [sq_nonneg (z + 2)]
  interval_cases z <;> simp_all

/-- **`√2` is irrational**: no rational number squares to `2`. The map `X² − 2`
is monic with a root `r` would be an integer `z` with `z² = 2`, impossible. -/
theorem no_rat_sq_eq_two : ∀ r : ℚ, r ^ 2 ≠ 2 := by
  intro r hr
  have hroot : aeval r (X ^ 2 - C 2 : ℤ[X]) = 0 := by
    simp only [map_sub, map_pow, aeval_X, map_ofNat]
    rw [hr]; ring
  have hmonic : (X ^ 2 - C 2 : ℤ[X]).Monic := by
    apply monic_X_pow_sub_C; norm_num
  obtain ⟨z, hz⟩ := monic_root_isInteger hmonic hroot
  have hz2 : (z : ℚ) ^ 2 = 2 := by rw [hz]; exact hr
  have : (z ^ 2 : ℤ) = 2 := by exact_mod_cast hz2
  exact no_int_sq_eq_two z this

end IntegralRootTheoremOQ01
