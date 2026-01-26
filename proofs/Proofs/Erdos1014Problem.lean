/-!
# Erdős Problem #1014: Ramsey Number Ratio Convergence

For fixed k ≥ 3, prove that R(k, l+1) / R(k, l) → 1 as l → ∞,
where R(k, l) is the Ramsey number.

## Key Results

- Open even for k = 3
- Best known bounds for R(3, l): between c₁ l² / log l and c₂ l² / log l
  (Bohman–Keevash, Shearer, Mattheus–Verstraëte)
- The conjecture would follow from precise enough asymptotics for R(k, l)

## References

- Erdős [Er71], p. 99
- Related: Problem 544 (R(3,k) behavior), Problem 1030 (diagonal)
- <https://erdosproblems.com/1014>
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- The Ramsey number R(k, l): minimum n such that every 2-coloring of
    edges of K_n contains a red K_k or a blue K_l. -/
axiom ramseyNumber (k l : ℕ) : ℕ

/-- Basic property: R(k, l) ≥ 1 for all k, l ≥ 1. -/
axiom ramsey_pos (k l : ℕ) (hk : k ≥ 1) (hl : l ≥ 1) :
  ramseyNumber k l ≥ 1

/-- Symmetry: R(k, l) = R(l, k). -/
axiom ramsey_symm (k l : ℕ) : ramseyNumber k l = ramseyNumber l k

/-! ## Classical Bounds -/

/-- Erdős–Szekeres upper bound: R(k, l) ≤ C(k+l-2, k-1). -/
axiom ramsey_upper_erdos_szekeres (k l : ℕ) (hk : k ≥ 2) (hl : l ≥ 2) :
  (ramseyNumber k l : ℝ) ≤ (Nat.choose (k + l - 2) (k - 1) : ℝ)

/-- Monotonicity: R(k, l) ≤ R(k, l+1). -/
axiom ramsey_monotone_right (k l : ℕ) :
  ramseyNumber k l ≤ ramseyNumber k (l + 1)

/-- R(k, l+1) ≤ R(k, l) + R(k-1, l+1) (recurrence). -/
axiom ramsey_recurrence (k l : ℕ) (hk : k ≥ 2) (hl : l ≥ 1) :
  ramseyNumber k (l + 1) ≤ ramseyNumber k l + ramseyNumber (k - 1) (l + 1)

/-! ## R(3, l) Bounds -/

/-- Shearer (1983) / Kim (1995): R(3, l) ≥ c · l² / log l. -/
axiom R3_lower (c : ℝ) (hc : c > 0) :
  ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
    (ramseyNumber 3 l : ℝ) ≥ c * (l : ℝ) ^ 2 / Real.log l

/-- Ajtai–Komlós–Szemerédi (1980): R(3, l) ≤ C · l² / log l. -/
axiom R3_upper :
  ∃ C : ℝ, C > 0 ∧ ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
    (ramseyNumber 3 l : ℝ) ≤ C * (l : ℝ) ^ 2 / Real.log l

/-! ## Main Conjecture -/

/-- **Erdős Problem #1014** (OPEN): For fixed k ≥ 3,
    R(k, l+1) / R(k, l) → 1 as l → ∞. -/
axiom erdos_1014_conjecture (k : ℕ) (hk : k ≥ 3) :
  ∀ ε : ℝ, ε > 0 → ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
    |(ramseyNumber k (l + 1) : ℝ) / (ramseyNumber k l : ℝ) - 1| < ε

/-! ## Consequences and Implications -/

/-- If R(k, l) ~ c_k · l^(k-1) / (log l)^(k-2) (conjectured asymptotics),
    then R(k, l+1)/R(k, l) = ((l+1)/l)^(k-1) · (log l / log(l+1))^(k-2) → 1. -/
axiom ratio_from_asymptotics (k : ℕ) (hk : k ≥ 3) :
  (∀ ε : ℝ, ε > 0 → ∃ c : ℝ, c > 0 ∧ ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
    |(ramseyNumber k l : ℝ) / (c * (l : ℝ) ^ (k - 1) / (Real.log l) ^ (k - 2)) - 1| < ε) →
  ∀ ε : ℝ, ε > 0 → ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
    |(ramseyNumber k (l + 1) : ℝ) / (ramseyNumber k l : ℝ) - 1| < ε

/-- The conjecture is equivalent to: R(k, l+1) - R(k, l) = o(R(k, l)). -/
axiom ratio_equiv_difference (k : ℕ) (hk : k ≥ 3) :
  (∀ ε : ℝ, ε > 0 → ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
    |(ramseyNumber k (l + 1) : ℝ) / (ramseyNumber k l : ℝ) - 1| < ε) ↔
  (∀ ε : ℝ, ε > 0 → ∃ L₀ : ℕ, ∀ l : ℕ, l > L₀ →
    ((ramseyNumber k (l + 1) : ℝ) - (ramseyNumber k l : ℝ)) /
    (ramseyNumber k l : ℝ) < ε)

/-! ## Special Cases -/

/-- For k = 2: R(2, l) = l, so R(2, l+1)/R(2, l) = (l+1)/l → 1.
    This is trivial (k = 2 case). -/
axiom ramsey_k2 (l : ℕ) (hl : l ≥ 1) : ramseyNumber 2 l = l

/-- Known small values: R(3,3) = 6, R(3,4) = 9, R(3,5) = 14. -/
axiom R33 : ramseyNumber 3 3 = 6
axiom R34 : ramseyNumber 3 4 = 9
axiom R35 : ramseyNumber 3 5 = 14

/-- For the diagonal case k = l, see Erdős Problem #1030. -/
axiom diagonal_ramsey_related :
  True  -- R(k,k) asymptotics is a separate major open problem
