import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Niven
import Mathlib.Tactic

/-
# Niven's Theorem

## What This Proves
If `θ` is a rational multiple of `π` (i.e. `θ = (m/n)·π`) and `cos θ` is rational,
then `cos θ ∈ {0, ±1/2, ±1}`.

This is Niven's theorem (Ivan Niven, 1956): the only rational values of the cosine
function at rational multiples of `π` are `0, ±1/2, ±1`. Equivalently, the only
"nice" angles whose cosine is rational are multiples of `90°` and `60°`.

## Approach
The proof has two parts:

1. **Algebraic-integer core** (`two_cos_int_of_rational`):
   If `θ = (m/n)·π` then `n·θ = m·π`, so `cos(n θ) = ±1 ∈ ℤ`.
   The normalized Chebyshev recurrence gives a *monic* integer polynomial `Cₙ`
   with `Cₙ(2 cos θ) = 2 cos(n θ) ∈ ℤ`, so `2 cos θ` is a root of a monic integer
   polynomial — an algebraic integer. A rational algebraic integer is a rational
   integer because `ℤ` is integrally closed in `ℚ`. Hence `2 cos θ ∈ ℤ`.

2. **Enumeration tail** (`niven`):
   Since `|cos θ| ≤ 1` we have `2 cos θ ∈ [-2, 2] ∩ ℤ = {-2,-1,0,1,2}`,
   giving `cos θ ∈ {-1, -1/2, 0, 1/2, 1}`.

## Status
- [x] Enumeration tail proved from Mathlib trig bounds
- [x] Algebraic-integer core discharged via Mathlib's `Real.isIntegral_two_mul_cos_rat_mul_pi`

## Note on Mathlib coverage
Mathlib (as of v4.26.0) already contains a complete Niven's theorem in
`Mathlib/NumberTheory/Niven.lean` (Alex Meiburg, Snir Broshi, 2025), including the
algebraic-integer core `Real.isIntegral_two_mul_cos_rat_mul_pi` and a top-level
`niven : cos θ ∈ {-1, -1/2, 0, 1/2, 1}`. This gallery entry is therefore a
*presentation*, not original formalization: it keeps the explicit enumeration
argument (`interval_cases` over `2 cos θ ∈ {-2,…,2}`) for pedagogy and discharges
the deep algebraic-integer step by citing Mathlib.

## Mathlib Dependencies
- `Real.cos_le_one`, `Real.neg_one_le_cos` — cosine bounds (enumeration tail)
- `Real.isIntegral_two_mul_cos_rat_mul_pi` — `2 cos(q π)` is integral over `ℤ`
- `IsIntegral.exists_int_iff_exists_rat` — a rational algebraic integer is an integer
-/

namespace NivenTheorem

open Real

/-- **Core lemma (Niven's key step).**
If `θ` is a rational multiple of `π` and `cos θ` is rational, then `2·cos θ` is an integer.

`θ = (m/n)·π = q·π` with `q := m/n : ℚ`, so by Mathlib's
`Real.isIntegral_two_mul_cos_rat_mul_pi` the number `2 cos θ` is an algebraic integer
over `ℤ`. Being also rational, it is a rational integer
(`IsIntegral.exists_int_iff_exists_rat`, i.e. `ℤ` is integrally closed in `ℚ`),
so `2 cos θ ∈ ℤ`.

The classical from-scratch argument (2 cos θ is a root of the monic integer
Vieta–Lucas/Chebyshev polynomial `Cₙ(X) - 2cos(nθ)`) is equivalent; we delegate to
Mathlib's roots-of-unity proof of the same fact. -/
theorem two_cos_int_of_rational
    (θ : ℝ) (m n : ℤ) (hn : n ≠ 0) (hθ : θ = (m / n : ℝ) * π)
    (hcos : ∃ r : ℚ, Real.cos θ = r) :
    ∃ k : ℤ, 2 * Real.cos θ = k := by
  obtain ⟨r, hr⟩ := hcos
  have hq : θ = ((m / n : ℚ) : ℝ) * π := by rw [hθ]; push_cast; ring
  have hint : IsIntegral ℤ (2 * Real.cos θ) := by
    rw [hq]; exact Real.isIntegral_two_mul_cos_rat_mul_pi (m / n)
  exact hint.exists_int_iff_exists_rat.mp ⟨2 * r, by rw [hr]; push_cast; ring⟩

/-- **Niven's Theorem.**
If `θ` is a rational multiple of `π` and `cos θ` is rational, then
`cos θ ∈ {0, ±1/2, ±1}`. -/
theorem niven (θ : ℝ) (m n : ℤ) (hn : n ≠ 0) (hθ : θ = (m / n : ℝ) * π)
    (hcos : ∃ r : ℚ, Real.cos θ = r) :
    Real.cos θ = 0 ∨ Real.cos θ = 1 / 2 ∨ Real.cos θ = -1 / 2 ∨
      Real.cos θ = 1 ∨ Real.cos θ = -1 := by
  obtain ⟨k, hk⟩ := two_cos_int_of_rational θ m n hn hθ hcos
  have hub : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hlb : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
  have hkl : -2 ≤ k := by
    have : (-2 : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast this
  have hku : k ≤ 2 := by
    have : (k : ℝ) ≤ 2 := by linarith
    exact_mod_cast this
  interval_cases k <;> push_cast at hk
  · -- k = -2 : 2 cos θ = -2 ⇒ cos θ = -1
    right; right; right; right; linarith
  · -- k = -1 : cos θ = -1/2
    right; right; left; linarith
  · -- k = 0 : cos θ = 0
    left; linarith
  · -- k = 1 : cos θ = 1/2
    right; left; linarith
  · -- k = 2 : cos θ = 1
    right; right; right; left; linarith

end NivenTheorem
