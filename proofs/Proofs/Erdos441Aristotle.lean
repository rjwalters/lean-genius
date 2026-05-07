/-
  Aristotle targets for Erdős Problem #441: LCM-Bounded Subsets
  Routine supporting lemmas for automated proof search.
  See Erdos441Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main deep results (Chen 1998, Chen-Dai 2006/2007)
  - erdos_question_answer: follows directly from erdos_question_disproved + chen_dai_2006
  - Membership and interval lemmas for ErdosFirstPart and ErdosSecondPart
  - LCM bound supporting lemmas using Nat.lcm API
  - No axioms, no definition sorries, no open conjectures
  - Use only block comments, not module docstrings

  Excluded (too deep for Aristotle):
  - construction_gives_lower_bound: requires LCM bound proof for full construction
  - Chen-Dai upper bound: deep analytic number theory
  - Asymptotic formula: requires advanced analysis
-/
import Mathlib
import Proofs.Erdos441Problem

open Finset Nat Real

namespace Erdos441Aristotle

open Erdos441

/-
## Section 1: Direct proof of erdos_question_answer

The theorem follows immediately from erdos_question_disproved and chen_dai_2006.
-/

/-- The answer to Erdős' original question is NO.
    Strategy: apply erdos_question_disproved to chen_dai_2006. -/
theorem erdos_question_answer_proof : ¬ErdosQuestion := by
  exact erdos_question_disproved chen_dai_2006

/-
## Section 2: Membership lemmas for ErdosFirstPart
-/

/-- Membership in ErdosFirstPart: x ∈ ErdosFirstPart N iff 1 ≤ x and x ≤ sqrt(N/2). -/
theorem mem_erdosFirstPart_iff (N x : ℕ) :
    x ∈ ErdosFirstPart N ↔ 1 ≤ x ∧ x ≤ Nat.sqrt (N / 2) := by
  simp [ErdosFirstPart, Finset.mem_filter, Finset.mem_range]
  omega

/-- Elements of ErdosFirstPart are at least 1. -/
theorem erdosFirstPart_ge_one (N x : ℕ) (hx : x ∈ ErdosFirstPart N) : 1 ≤ x := by
  rw [mem_erdosFirstPart_iff] at hx
  exact hx.1

/-- Elements of ErdosFirstPart are bounded by sqrt(N/2). -/
theorem erdosFirstPart_le_sqrt (N x : ℕ) (hx : x ∈ ErdosFirstPart N) :
    x ≤ Nat.sqrt (N / 2) := by
  rw [mem_erdosFirstPart_iff] at hx
  exact hx.2

/-
## Section 3: Membership lemmas for ErdosSecondPart
-/

/-- Membership in ErdosSecondPart: x ∈ ErdosSecondPart N iff
    sqrt(N/2) ≤ x, x ≤ sqrt(2N), and x is even. -/
theorem mem_erdosSecondPart_iff (N x : ℕ) :
    x ∈ ErdosSecondPart N ↔
      Nat.sqrt (N / 2) ≤ x ∧ x ≤ Nat.sqrt (2 * N) ∧ x % 2 = 0 := by
  simp [ErdosSecondPart, Finset.mem_filter, Finset.mem_range]
  omega

/-- Elements of ErdosSecondPart are even. -/
theorem erdosSecondPart_even (N x : ℕ) (hx : x ∈ ErdosSecondPart N) : x % 2 = 0 := by
  rw [mem_erdosSecondPart_iff] at hx
  exact hx.2.2

/-- Elements of ErdosSecondPart are bounded by sqrt(2N). -/
theorem erdosSecondPart_le_sqrt2N (N x : ℕ) (hx : x ∈ ErdosSecondPart N) :
    x ≤ Nat.sqrt (2 * N) := by
  rw [mem_erdosSecondPart_iff] at hx
  exact hx.2.1

/-
## Section 4: Bounds on sqrt for the construction
-/

/-- sqrt(N/2) ≤ sqrt(N) for any N. -/
theorem sqrt_half_le_sqrt (N : ℕ) : Nat.sqrt (N / 2) ≤ Nat.sqrt N := by
  apply Nat.sqrt_le_sqrt
  omega

/-- sqrt(2N) ≤ 2 * sqrt(N) + 1 (crude bound). -/
theorem sqrt_2N_bound (N : ℕ) : Nat.sqrt (2 * N) ≤ 2 * Nat.sqrt N + 1 := by
  sorry

/-
## Section 5: LCM basic lemmas
-/

/-- lcm(a, a) = a. -/
theorem lcm_self_eq (a : ℕ) : Nat.lcm a a = a := by
  simp [Nat.lcm]

/-- lcm(a, b) ≤ a * b for positive a, b. -/
theorem lcm_le_mul (a b : ℕ) : Nat.lcm a b ≤ a * b := by
  sorry

/-- For a, b ≤ k, lcm(a, b) ≤ k^2. -/
theorem lcm_le_sq (a b k : ℕ) (ha : a ≤ k) (hb : b ≤ k) : Nat.lcm a b ≤ k ^ 2 := by
  sorry

/-
## Section 6: ErdosFirstPart LCM bound
-/

/-- Any element in ErdosFirstPart is ≤ N (when N ≥ 1).
    Follows because sqrt(N/2) ≤ N for N ≥ 1. -/
theorem erdosFirstPart_le_N (N x : ℕ) (hN : N ≥ 1) (hx : x ∈ ErdosFirstPart N) : x ≤ N := by
  have h1 := erdosFirstPart_le_sqrt N x hx
  have h2 : Nat.sqrt (N / 2) ≤ N := by
    apply Nat.sqrt_le_self
  omega

/-- LCM of two elements in ErdosFirstPart is at most N.
    Strategy: a, b ≤ sqrt(N/2), so lcm(a,b) ≤ a*b ≤ (N/2) ≤ N. -/
theorem erdosFirstPart_lcm_bound (N a b : ℕ) (hN : N ≥ 1)
    (ha : a ∈ ErdosFirstPart N) (hb : b ∈ ErdosFirstPart N) :
    Nat.lcm a b ≤ N := by
  sorry

end Erdos441Aristotle
