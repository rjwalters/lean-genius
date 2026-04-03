/-
  Aristotle targets for Erdos Problem #263
  Routine supporting lemmas for automated proof search.
  See Stubs/Erdos263Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the open questions (irrationality conjectures)
  - Concrete growth rate computations for doubleExp and factorial sequences
  - No definition sorries
  - No axioms

  Included sorries (5 targets):
  - doubleExp_folklore_const: (2^{2^n})^{1/2^n} = 2 for all n (computation)
  - doubleExp_not_folklore_growth: doubleExp does not satisfy folklore condition
  - two_pow_div_n_tendsto_top: 2^n / n diverges (standard analysis)
  - doubleExp_superexponential: doubleExp has superexponential growth
  - factorial_no_folklore_growth: factorial does not satisfy folklore condition

  Excluded (OPEN or deep results):
  - folklore_irrationality: the folklore sufficient condition (deep number theory)
  - kovac_tao_not_irrationality: 2024 negative result (deep construction)
  - positive_condition_irrationality: sufficient condition (deep)
  - truncation_insufficient: requires construction of specific sequences (deep)
  - ErdosQuestion1, ErdosQuestion2: the actual open problems
-/
import Mathlib

namespace Erdos263Aristotle

open Filter Topology Real

/-- A sequence of positive integers. -/
def PosIntSeq := ℕ → ℕ+

/-- The double exponential sequence: a_n = 2^{2^n}. -/
def doubleExp : PosIntSeq := fun n => ⟨2 ^ (2 ^ n), Nat.pos_pow_of_pos _ (by norm_num)⟩

/-- The factorial sequence: a_n = (n+1)!. -/
def factorial_seq : PosIntSeq := fun n => ⟨Nat.factorial (n + 1), Nat.factorial_pos _⟩

/-- Folklore growth: a_n^{1/2^n} → ∞. -/
def HasFolkloreGrowth (a : PosIntSeq) : Prop :=
  Tendsto (fun n => ((a n : ℕ) : ℝ) ^ (1 / (2 ^ n : ℝ))) atTop atTop

/-- Superexponential growth: a_n^{1/n} → ∞. -/
def HasSuperexponentialGrowth (a : PosIntSeq) : Prop :=
  Tendsto (fun n => ((a n : ℕ) : ℝ) ^ (1 / (n : ℝ))) atTop atTop

-- Routine: For doubleExp, the folklore exponent sequence is constantly 2.
-- (2^{2^n})^{1/2^n} = 2^(2^n / 2^n) = 2^1 = 2 for all n >= 1.
theorem doubleExp_folklore_const (n : ℕ) :
    ((doubleExp n : ℕ) : ℝ) ^ (1 / (2 ^ n : ℝ)) = 2 := by
  sorry

-- Routine: Double exponential does NOT have folklore growth.
-- The sequence (2^{2^n})^{1/2^n} = 2 is constant, not tending to infinity.
theorem doubleExp_not_folklore_growth : ¬HasFolkloreGrowth doubleExp := by
  sorry

-- Routine: 2^n / n tends to infinity as n tends to infinity.
-- Standard analysis result: exponential growth dominates linear.
theorem two_pow_div_n_tendsto_top :
    Tendsto (fun n : ℕ => (2 : ℝ) ^ n / n) atTop atTop := by
  sorry

-- Routine: Double exponential has superexponential growth.
-- (2^{2^n})^{1/n} = 2^{2^n/n} tends to infinity since 2^n/n tends to infinity.
theorem doubleExp_superexponential : HasSuperexponentialGrowth doubleExp := by
  sorry

-- Routine: Factorial does NOT have folklore growth.
-- ((n+1)!)^{1/2^n} tends to 1 (not to infinity) since factorial grows
-- much slower than doubly exponential; by Stirling, (n!)^{1/n} ~ n/e.
theorem factorial_no_folklore_growth : ¬HasFolkloreGrowth factorial_seq := by
  sorry

end Erdos263Aristotle
