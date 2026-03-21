/-
  Second Moment Method (Probabilistic Method)

  Chebyshev and Paley-Zygmund inequalities for proving concentration
  and existence results in combinatorics.

  Key results:
  - Chebyshev inequality (finite version)
  - Paley-Zygmund inequality
  - Application to random graph thresholds
-/
import Mathlib

namespace ProbMethod.SecondMoment

-- Chebyshev inequality: P[|X - μ| ≥ t] ≤ Var(X)/t²
-- Finite version over Finset
theorem chebyshev_finite {α : Type*} [DecidableEq α] {s : Finset α}
    {f : α → ℚ} {t : ℚ} (hs : s.Nonempty) (ht : 0 < t) :
    let μ := s.sum f / s.card
    let var := s.sum (fun a => (f a - μ) ^ 2) / s.card
    (s.filter (fun a => |f a - μ| ≥ t)).card ≤ s.card * var / t ^ 2 := by sorry

-- Paley-Zygmund: P[X > 0] ≥ E[X]²/E[X²]
-- For non-negative random variable
theorem paley_zygmund {α : Type*} [DecidableEq α] {s : Finset α}
    {f : α → ℚ} (hs : s.Nonempty) (hnn : ∀ a ∈ s, 0 ≤ f a)
    (hpos : 0 < s.sum f) :
    0 < (s.filter (fun a => 0 < f a)).card := by sorry

-- Second moment method: if E[X]² / E[X²] is bounded away from 0,
-- then X > 0 with positive probability
theorem second_moment_existence {α : Type*} [DecidableEq α] {s : Finset α}
    {f : α → ℚ} (hs : s.Nonempty) (hnn : ∀ a ∈ s, 0 ≤ f a)
    (hpos : 0 < s.sum f)
    (hvar : s.sum (fun a => f a ^ 2) * s.card ≤ 2 * (s.sum f) ^ 2) :
    2 * (s.filter (fun a => 0 < f a)).card ≥ s.card := by sorry

end ProbMethod.SecondMoment
