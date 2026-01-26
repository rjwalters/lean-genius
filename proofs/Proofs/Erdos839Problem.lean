/-!
# Erdős Problem #839: Sequences Avoiding Consecutive-Term Sums

Erdős Problem #839 considers sequences 1 ≤ a₁ < a₂ < ⋯ where no term
equals a sum of consecutive earlier terms (i.e., aₘ ≠ aᵢ + aᵢ₊₁ + ⋯ + aⱼ
for any i ≤ j < m). Two questions are posed:

1. Is lim sup(aₙ/n) = ∞?
2. Does (1/log x)·Σ_{aₙ<x} 1/aₙ → 0?

Known:
- lim inf(aₙ/n) < ∞ is achievable
- Σ 1/aₙ ≥ c·log log x is possible
- Upper density can reach 19/36 (Freud), disproving Erdős's conjecture of 1/2

Reference: https://erdosproblems.com/839
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic

/-! ## Definitions -/

/-- A strictly increasing sequence of positive integers. -/
def StrictIncSeq := { a : ℕ → ℕ // ∀ i j, i < j → a i < a j }

/-- The sum of consecutive terms a_i + a_{i+1} + ... + a_j. -/
def consecutiveSum (a : ℕ → ℕ) (i j : ℕ) : ℕ :=
  ∑ k in Finset.Icc i j, a k

/-- No term of the sequence equals a sum of consecutive earlier terms. -/
def AvoidConsecutiveSums (a : ℕ → ℕ) : Prop :=
  ∀ m : ℕ, ∀ i j : ℕ, i ≤ j → j < m →
    a m ≠ consecutiveSum a i j

/-- The set of all valid sequences (avoiding consecutive-term sums). -/
def ValidSeq := { a : ℕ → ℕ //
  (∀ i j, i < j → a i < a j) ∧ AvoidConsecutiveSums a }

/-! ## Growth Rate Questions -/

/-- Question 1: Is lim sup(aₙ/n) = ∞ for every valid sequence? -/
def Question1 : Prop :=
  ∀ a : ValidSeq, ∀ C : ℝ, ∃ n : ℕ, C < (a.val n : ℝ) / (n + 1 : ℝ)

/-- Question 2: Does the logarithmic density vanish?
    (1/log x)·Σ_{aₙ < x} 1/aₙ → 0 as x → ∞. -/
def Question2 : Prop :=
  ∀ a : ValidSeq, ∀ ε : ℝ, 0 < ε →
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑ n in (Finset.range X).filter (fun n => a.val n < X),
        (1 : ℝ) / (a.val n : ℝ)) ≤ ε * Real.log X

/-! ## Known Results -/

/-- lim inf(aₙ/n) can be finite: there exist valid sequences where
    aₙ/n stays bounded infinitely often. -/
axiom liminf_finite :
  ∃ a : ValidSeq, ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ (a.val n : ℝ) / (n + 1 : ℝ) ≤ C

/-- The reciprocal sum can grow at least as fast as c·log log x. -/
axiom reciprocal_sum_lower :
  ∃ a : ValidSeq, ∃ c : ℝ, 0 < c ∧
    ∀ X : ℕ, 3 ≤ X →
      c * Real.log (Real.log X) ≤
        ∑ n in (Finset.range X).filter (fun n => a.val n < X),
          (1 : ℝ) / (a.val n : ℝ)

/-! ## Upper Density -/

/-- The upper density of a valid sequence. -/
noncomputable def upperDensity (a : ValidSeq) : ℝ :=
  Filter.limsup (fun N : ℕ =>
    ((Finset.range N).filter (fun n => a.val n ≤ N)).card / (N : ℝ))
    Filter.atTop

/-- Erdős conjectured the upper density is at most 1/2, but
    Freud disproved this by constructing a sequence with density 19/36. -/
axiom freud_counterexample :
  ∃ a : ValidSeq, (1 : ℝ) / 2 < upperDensity a

/-- The Freud construction achieves upper density 19/36. -/
axiom freud_density :
  ∃ a : ValidSeq, upperDensity a = 19 / 36

/-! ## Main Open Questions -/

/-- Erdős Problem #839, Question 1: Is lim sup(aₙ/n) = ∞? -/
axiom erdos_839_question1 : Question1

/-- Erdős Problem #839, Question 2: Does the logarithmic density vanish? -/
axiom erdos_839_question2 : Question2
