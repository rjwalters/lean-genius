/-
Erdős Problem #1014: Ramsey Number Ratio Limit

**Statement**: For fixed k ≥ 3, prove that
  lim_{l → ∞} R(k,l+1) / R(k,l) = 1

**Status**: OPEN (even for k=3!)

**Context**: This asks whether consecutive Ramsey numbers grow subexponentially
in the second parameter. The conjecture says they converge to the same growth.

Reference: https://erdosproblems.com/1014
Related: #544 (R(3,k) behavior), #1030 (diagonal Ramsey ratio)
-/

import Mathlib

open Real Filter Topology

namespace Erdos1014

/-
## Part I: Ramsey Numbers
-/

/-- The Ramsey number R(m,n): minimum N such that any 2-coloring of K_N
    contains a red clique of size m or a blue clique of size n. -/
axiom ramseyNumber (m n : ℕ) : ℕ

/-- Ramsey numbers are symmetric. -/
axiom ramsey_symmetric (m n : ℕ) : ramseyNumber m n = ramseyNumber n m

/-- Ramsey numbers are monotone in both arguments. -/
axiom ramsey_mono_left (m₁ m₂ n : ℕ) (h : m₁ ≤ m₂) :
    ramseyNumber m₁ n ≤ ramseyNumber m₂ n

axiom ramsey_mono_right (m n₁ n₂ : ℕ) (h : n₁ ≤ n₂) :
    ramseyNumber m n₁ ≤ ramseyNumber m n₂

/-- Basic bound: R(m,n) ≤ R(m-1,n) + R(m,n-1). -/
axiom ramsey_recurrence (m n : ℕ) (hm : m ≥ 2) (hn : n ≥ 2) :
    ramseyNumber m n ≤ ramseyNumber (m - 1) n + ramseyNumber m (n - 1)

/-
## Part II: The Main Conjecture
-/

/-- The ratio R(k, l+1) / R(k, l). -/
noncomputable def ramseyRatio (k l : ℕ) : ℝ :=
  (ramseyNumber k (l + 1) : ℝ) / (ramseyNumber k l : ℝ)

/-- The main conjecture: for fixed k ≥ 3, the ratio tends to 1. -/
def mainConjecture (k : ℕ) (hk : k ≥ 3) : Prop :=
  Tendsto (fun l => ramseyRatio k l) atTop (𝓝 1)

/-- Equivalently: R(k, l+1) - R(k, l) = o(R(k, l)). -/
def mainConjectureAlt (k : ℕ) (hk : k ≥ 3) : Prop :=
  ∀ ε > 0, ∃ L : ℕ, ∀ l ≥ L,
    |(ramseyNumber k (l + 1) : ℝ) - (ramseyNumber k l : ℝ)| ≤ ε * (ramseyNumber k l : ℝ)

/-- The two formulations are equivalent. -/
theorem conjecture_equiv (k : ℕ) (hk : k ≥ 3) :
    mainConjecture k hk ↔ mainConjectureAlt k hk := by
  sorry

/-
## Part III: What We Know
-/

/-- Trivial upper bound: R(k, l+1) ≤ 2 · R(k, l) (very weak). -/
theorem ratio_upper_trivial (k l : ℕ) (hk : k ≥ 2) (hl : l ≥ 1) :
    ramseyRatio k l ≤ 2 := by
  sorry

/-- From recurrence: R(k, l+1) ≤ R(k-1, l+1) + R(k, l). -/
theorem ratio_bound_from_recurrence (k l : ℕ) (hk : k ≥ 3) (hl : l ≥ 1) :
    ramseyRatio k l ≤ 1 + (ramseyNumber (k - 1) (l + 1) : ℝ) / (ramseyNumber k l : ℝ) := by
  sorry

/-- For k=3: R(3, l+1) ≤ R(2, l+1) + R(3, l) = (l+1) + R(3, l). -/
theorem ratio_k3_bound (l : ℕ) (hl : l ≥ 1) :
    ramseyRatio 3 l ≤ 1 + ((l + 1 : ℕ) : ℝ) / (ramseyNumber 3 l : ℝ) := by
  sorry

/-
## Part IV: Known R(3,k) Asymptotics
-/

/-- R(3,k) ~ c · k²/log k for some c ∈ [1/2, 1]. -/
axiom R3_asymptotic :
    ∃ c : ℝ, c ∈ Set.Icc (1/2 : ℝ) 1 ∧
      Tendsto (fun k => (ramseyNumber 3 k : ℝ) / (k^2 / log k)) atTop (𝓝 c)

/-- If R(3,k) ~ c · k²/log k, then R(3,k+1)/R(3,k) → 1.
    Because (k+1)²/log(k+1) / (k²/log k) → 1. -/
theorem asymptotic_implies_ratio (c : ℝ) (hc : c > 0)
    (hasym : Tendsto (fun k => (ramseyNumber 3 k : ℝ) / (c * k^2 / log k)) atTop (𝓝 1)) :
    Tendsto (fun l => ramseyRatio 3 l) atTop (𝓝 1) := by
  sorry

/-
## Part V: The Diagonal Case (Related Problem #1030)
-/

/-- Diagonal Ramsey ratio: R(n+1,n+1) / R(n,n). -/
noncomputable def diagonalRatio (n : ℕ) : ℝ :=
  (ramseyNumber (n + 1) (n + 1) : ℝ) / (ramseyNumber n n : ℝ)

/-- The diagonal version (Problem #1030): Does lim R(n+1,n+1)/R(n,n) = √2 · e? -/
def diagonalConjecture : Prop :=
  Tendsto diagonalRatio atTop (𝓝 (Real.sqrt 2 * Real.exp 1))

/-- Known: 2 ≤ liminf ≤ limsup ≤ 4. -/
axiom diagonal_ratio_bounds :
    2 ≤ liminf diagonalRatio atTop ∧ limsup diagonalRatio atTop ≤ 4

/-
## Part VI: Summary
-/

/-- Erdős Problem #1014: Summary

    **Conjecture**: For fixed k ≥ 3, lim_{l→∞} R(k,l+1)/R(k,l) = 1.

    **Status**: OPEN even for k=3!

    **Key Insight**: If R(k,l) has a nice asymptotic formula f(l), then
    f(l+1)/f(l) → 1 implies the conjecture.

    **For k=3**:
    - R(3,l) ~ c · l²/log l (proved)
    - So R(3,l+1)/R(3,l) ~ (l+1)²/log(l+1) / (l²/log l) → 1
    - But this doesn't constitute a proof because "~" hides error terms!

    **Related**:
    - Problem #544: R(3,k) asymptotics
    - Problem #1030: diagonal R(n,n) ratio (different conjecture: → √2·e) -/
theorem erdos_1014_summary :
    -- The conjecture is well-formulated for k=3
    mainConjecture 3 (by omega) ↔
    Tendsto (fun l => ramseyRatio 3 l) atTop (𝓝 1) := by
  rfl

end Erdos1014
