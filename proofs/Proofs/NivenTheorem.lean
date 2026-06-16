import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.RootsOfUnity.Basic
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
- [ ] Algebraic-integer core (Chebyshev / integrally-closed) — Aristotle target

## Mathlib Dependencies
- `Real.cos_le_one`, `Real.neg_one_le_cos` — cosine bounds
- `Polynomial.Chebyshev.T` — Chebyshev polynomials (for the core)
- `IsIntegrallyClosed` — `ℤ` integrally closed in `ℚ` (for the core)
-/

namespace NivenTheorem

open Real

/-- **Core lemma (Niven's key step).**
If `θ` is a rational multiple of `π` and `cos θ` is rational, then `2·cos θ` is an integer.

Reasoning: writing `θ = (m/n)·π` with `n ≠ 0`, we have `n·θ = m·π`, so
`cos(n θ) = (-1)^m ∈ ℤ`. By the monic integer Chebyshev recurrence
`2 cos(n θ) = Cₙ(2 cos θ)` (where `Cₙ` is monic over `ℤ`), the number `2 cos θ`
is a root of the monic integer polynomial `Cₙ(X) - 2 cos(n θ)`, hence an algebraic
integer. A rational algebraic integer is a rational integer (`ℤ` is integrally
closed in `ℚ`), so `2 cos θ ∈ ℤ`. -/
theorem two_cos_int_of_rational
    (θ : ℝ) (m n : ℤ) (hn : n ≠ 0) (hθ : θ = (m / n : ℝ) * π)
    (hcos : ∃ r : ℚ, Real.cos θ = r) :
    ∃ k : ℤ, 2 * Real.cos θ = k := by
  sorry

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
