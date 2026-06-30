import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Niven
import Mathlib.Tactic

/-
# Niven's Theorem for Sine

## What This Proves
If `θ` is a rational multiple of `π` (i.e. `θ = (m/n)·π`) and `sin θ` is rational,
then `sin θ ∈ {0, ±1/2, ±1}`.

This is the sine companion to Niven's theorem. The gallery entry
`niven-theorem-oq-01` (`Proofs/NivenTheorem.lean`) proves the *cosine* statement
only: the rational values of `cos` at rational multiples of `π` are `0, ±1/2, ±1`.

## Approach
The sine result is a clean corollary of the cosine result via the co-function
identity `cos (π/2 - θ) = sin θ` (`Real.cos_pi_div_two_sub`).

If `θ = (m/n)·π`, set `φ := π/2 - θ`. Then
`φ = (1/2 - m/n)·π = ((n - 2m)/(2n))·π`,
so `φ` is again a rational multiple of `π` (numerator `n - 2m`, denominator `2n`).
Moreover `cos φ = sin θ`, so if `sin θ` is rational then `cos φ` is rational.
Cosine Niven applied to `φ` gives `cos φ ∈ {0, ±1/2, ±1}`, i.e.
`sin θ ∈ {0, ±1/2, ±1}`.

## Status
- [x] Cosine core restated (delegates the deep algebraic-integer step to Mathlib's
      `Real.isIntegral_two_mul_cos_rat_mul_pi`, exactly as `niven-theorem-oq-01`)
- [x] Sine corollary derived via `Real.cos_pi_div_two_sub`

## Mathlib Dependencies
- `Real.isIntegral_two_mul_cos_rat_mul_pi` — `2 cos(q π)` is integral over `ℤ`
- `IsIntegral.exists_int_iff_exists_rat` — a rational algebraic integer is an integer
- `Real.cos_le_one`, `Real.neg_one_le_cos` — cosine bounds (enumeration tail)
- `Real.cos_pi_div_two_sub` — co-function identity `cos (π/2 - x) = sin x`
-/

namespace NivenTheoremOQ02

open Real

/-- **Cosine Niven (helper).** Restated from `niven-theorem-oq-01` so the sine
corollary is self-contained: if `θ` is a rational multiple of `π` and `cos θ` is
rational, then `cos θ ∈ {0, ±1/2, ±1}`. The deep step (`2 cos θ` is an algebraic
integer) is delegated to Mathlib. -/
theorem cos_niven (θ : ℝ) (m n : ℤ) (hn : n ≠ 0) (hθ : θ = (m / n : ℝ) * π)
    (hcos : ∃ r : ℚ, Real.cos θ = r) :
    Real.cos θ = 0 ∨ Real.cos θ = 1 / 2 ∨ Real.cos θ = -1 / 2 ∨
      Real.cos θ = 1 ∨ Real.cos θ = -1 := by
  obtain ⟨r, hr⟩ := hcos
  have hq : θ = ((m / n : ℚ) : ℝ) * π := by rw [hθ]; push_cast; ring
  have hint : IsIntegral ℤ (2 * Real.cos θ) := by
    rw [hq]; exact Real.isIntegral_two_mul_cos_rat_mul_pi (m / n)
  obtain ⟨k, hk⟩ :=
    hint.exists_int_iff_exists_rat.mp ⟨2 * r, by rw [hr]; push_cast; ring⟩
  have hub : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hlb : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  have hkl : -2 ≤ k := by
    have : (-2 : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast this
  have hku : k ≤ 2 := by
    have : (k : ℝ) ≤ 2 := by linarith
    exact_mod_cast this
  interval_cases k <;> push_cast at hk
  · right; right; right; right; linarith
  · right; right; left; linarith
  · left; linarith
  · right; left; linarith
  · right; right; right; left; linarith

/-- **Niven's Theorem for sine.** If `θ` is a rational multiple of `π` and
`sin θ` is rational, then `sin θ ∈ {0, ±1/2, ±1}`. -/
theorem sin_niven (θ : ℝ) (m n : ℤ) (hn : n ≠ 0) (hθ : θ = (m / n : ℝ) * π)
    (hsin : ∃ r : ℚ, Real.sin θ = r) :
    Real.sin θ = 0 ∨ Real.sin θ = 1 / 2 ∨ Real.sin θ = -1 / 2 ∨
      Real.sin θ = 1 ∨ Real.sin θ = -1 := by
  -- The complementary angle `φ = π/2 - θ` is again a rational multiple of `π`,
  -- and `cos φ = sin θ`.
  set φ := π / 2 - θ with hφ
  have hsc : Real.cos φ = Real.sin θ := by rw [hφ, Real.cos_pi_div_two_sub]
  have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hφeq : φ = ((↑(n - 2 * m) : ℝ) / (↑(2 * n) : ℝ)) * π := by
    rw [hφ, hθ]
    push_cast
    field_simp
  have h2n : (2 * n : ℤ) ≠ 0 := mul_ne_zero (by norm_num) hn
  have hcosrat : ∃ r : ℚ, Real.cos φ = r := by
    obtain ⟨r, hr⟩ := hsin
    exact ⟨r, by rw [hsc, hr]⟩
  have hcn := cos_niven φ (n - 2 * m) (2 * n) h2n hφeq hcosrat
  rwa [hsc] at hcn

end NivenTheoremOQ02
