/-!
# Erdős Problem #466 — Points in a Circle with Fractional Distance Separation

Let N(X, δ) denote the maximum number of points P₁, …, Pₙ in a disk of
radius X such that ‖|Pᵢ − Pⱼ|‖ ≥ δ for all i ≠ j, where ‖x‖ denotes the
distance from x to the nearest integer.

**Question:** Is there some δ > 0 such that N(X, δ) → ∞ as X → ∞?

## Status: PROVED

- **Graham**: Showed N(X, 1/10) ≥ (log X) / 10, answering the question
  affirmatively.
- **Sárközy (1976)**: For all sufficiently small δ > 0,
  N(X, δ) > X^{1/2 − δ^{1/7}}, a substantially stronger bound.

## Context

The problem asks whether large disks can accommodate arbitrarily many
points whose pairwise distances all stay bounded away from integers.
This connects to Diophantine approximation and the distribution of
distances in Euclidean point sets.

Related: Problem #465 (upper bounds), Problem #953 (similar).

*Reference:* [erdosproblems.com/466](https://www.erdosproblems.com/466)
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Set Real

/-! ## Core Definitions -/

/-- Distance from a real number to the nearest integer. -/
noncomputable def fracDist (x : ℝ) : ℝ :=
  |x - round x|

/-- A configuration of n points in a disk of radius X in ℝ²,
with all pairwise fractional-distance separations ≥ δ. -/
structure SeparatedConfig (X δ : ℝ) where
  n : ℕ
  points : Fin n → (Fin 2 → ℝ)
  inDisk : ∀ i, ‖points i‖ ≤ X
  separated : ∀ i j, i ≠ j →
    fracDist (dist (points i) (points j)) ≥ δ

/-- N(X, δ) = maximum number of points in a disk of radius X with
pairwise fractional-distance separation ≥ δ. -/
noncomputable def maxSeparatedPoints (X δ : ℝ) : ℕ :=
  sSup { c.n | c : SeparatedConfig X δ }

/-! ## Main Result (Proved) -/

/-- **Erdős Problem #466 (Proved).**
There exists δ > 0 such that N(X, δ) → ∞ as X → ∞. -/
axiom erdos_466 :
  ∃ δ : ℝ, 0 < δ ∧ Filter.Tendsto (fun X => maxSeparatedPoints X δ) Filter.atTop Filter.atTop

/-! ## Graham's Bound -/

/-- **Graham.** N(X, 1/10) ≥ (log X)/10 for sufficiently large X.
This answers Erdős's question in the affirmative. -/
axiom graham_logarithmic_bound :
  ∀ᶠ (X : ℝ) in Filter.atTop,
    (maxSeparatedPoints X (1/10) : ℝ) ≥ Real.log X / 10

/-! ## Sárközy's Improvement -/

/-- **Sárközy (1976).** For all sufficiently small δ > 0,
N(X, δ) > X^{1/2 − δ^{1/7}} for all large X.
This is a polynomial (almost √X) lower bound, far stronger than
Graham's logarithmic bound. -/
axiom sarkozy_polynomial_bound :
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ᶠ (X : ℝ) in Filter.atTop,
      (maxSeparatedPoints X δ : ℝ) > X ^ (1/2 - δ ^ (1/7 : ℝ))

/-! ## Structural Observations -/

/-- For any δ > 1/2, we have N(X, δ) = 0 for all X, since the
fractional distance is always at most 1/2. -/
axiom fracDist_bound : ∀ x : ℝ, fracDist x ≤ 1/2

/-- N(X, δ) is monotone non-decreasing in X: a larger disk can
accommodate at least as many separated points. -/
axiom maxSeparatedPoints_mono (δ : ℝ) (X₁ X₂ : ℝ) (h : X₁ ≤ X₂) :
  maxSeparatedPoints X₁ δ ≤ maxSeparatedPoints X₂ δ

/-- N(X, δ) is monotone non-increasing in δ: a stricter separation
requirement can only reduce the maximum count. -/
axiom maxSeparatedPoints_anti (X : ℝ) (δ₁ δ₂ : ℝ) (h : δ₁ ≤ δ₂) :
  maxSeparatedPoints X δ₂ ≤ maxSeparatedPoints X δ₁
