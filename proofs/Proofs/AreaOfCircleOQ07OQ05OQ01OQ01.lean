import Proofs.AreaOfCircleOQ07OQ05OQ01
import Mathlib.Tactic

/-
# Vanishing of the Odd Gaussian Moments  (area-of-circle-oq-07-oq-05-oq-01-oq-01)

## Open Question (area-of-circle-oq-07-oq-05-oq-01-oq-01)
"Add the vanishing odd moments `∫_ℝ x^{2n+1} e^{-x²} dx = 0` to give the full
moment sequence."

## Answer

For every `n : ℕ`,

  `∫_{-∞}^{∞} x^{2n+1} e^{-x²} dx = 0`.

The parent entry `area-of-circle-oq-07-oq-05-oq-01` evaluated the *even* moments
`∫ x^{2n} e^{-x²} = (2n-1)‼ √π / 2^n` by an integration-by-parts recursion.  The
moment sequence of the standard Gaussian is completed by the **odd** moments,
which all vanish.

The vanishing is a pure symmetry statement, not an artefact of non-integrability:
the integrand `x^{2n+1} e^{-x²}` is genuinely Lebesgue integrable (parent's
`integrable_pow_mul_gaussian`), yet its integral is zero because the integrand is
an **odd** function and Lebesgue measure on `ℝ` is invariant under `x ↦ -x`.
Concretely, writing `f x = x^{2n+1} e^{-x²}`,

  `∫ f = ∫ x, f(-x)`   (`integral_neg_eq_self`, negation-invariance of volume)
       `= ∫ x, -f(x)`   (`f` is odd: `(-x)^{2n+1} = -x^{2n+1}`, `(-x)² = x²`)
       `= -∫ f`,

so `∫ f = -∫ f`, forcing `∫ f = 0` (`gaussian_odd_moment`).

Folding the new odd-moment vanishing together with the parent's even-moment
closed form gives the **full moment sequence** indexed by a single natural number
`m` (`gaussian_moment`):

  `∫_ℝ x^m e^{-x²} dx = if Even m then (m-1)‼ √π / 2^{m/2} else 0`.

No new axioms: the odd-moment vanishing is `integral_neg_eq_self` together with
oddness of the integrand; the full sequence merely case-splits on the parity of
`m` and reuses the parent's even-moment evaluation.
-/

open Real MeasureTheory
open scoped Nat

namespace AreaOfCircleOQ07OQ05OQ01OQ01

/-- **The odd moments of the standard Gaussian vanish.**
`∫_{-∞}^{∞} x^{2n+1} e^{-x²} dx = 0`.

The integrand is odd and Lebesgue measure on `ℝ` is negation-invariant, so the
integral equals its own negation and must be zero. -/
theorem gaussian_odd_moment (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n + 1) * Real.exp (-x ^ 2) = 0 := by
  set f : ℝ → ℝ := fun x => x ^ (2 * n + 1) * Real.exp (-x ^ 2) with hf
  -- `f` is odd: `(-x)^{2n+1} = -(x^{2n+1})` and `(-x)² = x²`.
  have hodd : ∀ x : ℝ, f (-x) = -f x := by
    intro x
    simp only [hf]
    rw [Odd.neg_pow ⟨n, rfl⟩, neg_sq]
    ring
  -- Negation-invariance of volume: `∫ f(-x) = ∫ f`.
  have h1 : ∫ x : ℝ, f (-x) = ∫ x : ℝ, f x := integral_neg_eq_self f volume
  -- Oddness rewrites the same integral as `∫ -f = -∫ f`.
  have h2 : ∫ x : ℝ, f (-x) = -∫ x : ℝ, f x := by
    rw [show (fun x : ℝ => f (-x)) = (fun x : ℝ => -f x) from funext hodd, integral_neg]
  -- Hence `∫ f = -∫ f`, so `∫ f = 0`.
  have : ∫ x : ℝ, f x = -∫ x : ℝ, f x := h1 ▸ h2
  linarith [this]

/-- Sanity check: the first odd moment `∫ x e^{-x²} = 0` (the `n = 0` case). -/
theorem gaussian_first_odd_moment :
    ∫ x : ℝ, x * Real.exp (-x ^ 2) = 0 := by
  have h := gaussian_odd_moment 0
  simpa using h

/-- **The full moment sequence of the standard Gaussian.**
`∫_{-∞}^{∞} x^m e^{-x²} dx = (m-1)‼ √π / 2^{m/2}` when `m` is even, and `0` when
`m` is odd.  This unifies the parent's even-moment evaluation
(`AreaOfCircleOQ07OQ05OQ01.gaussian_even_moment`) with the odd-moment vanishing
above into one statement indexed by a single natural number. -/
theorem gaussian_moment (m : ℕ) :
    ∫ x : ℝ, x ^ m * Real.exp (-x ^ 2)
      = if Even m then ((m - 1)‼ : ℝ) * Real.sqrt Real.pi / 2 ^ (m / 2) else 0 := by
  rcases Nat.even_or_odd m with h | h
  · -- `m = k + k` even.
    obtain ⟨k, rfl⟩ := h
    have hdiv : (k + k) / 2 = k := by omega
    have hpow : k + k = 2 * k := by ring
    rw [if_pos ⟨k, rfl⟩, hdiv, hpow,
      AreaOfCircleOQ07OQ05OQ01.gaussian_even_moment k]
  · -- `m = 2k + 1` odd.
    obtain ⟨k, rfl⟩ := h
    rw [if_neg (Nat.not_even_iff_odd.mpr ⟨k, rfl⟩), gaussian_odd_moment k]

end AreaOfCircleOQ07OQ05OQ01OQ01
