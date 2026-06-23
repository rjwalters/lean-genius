/-
  Aristotle targets for Erdős Problem #859: Density of Divisor Sum Representations
  Routine supporting lemmas for automated proof search.
  See Erdos859Problem.lean for the main formalization.

  These lemmas expose the concrete IsPractical examples for Aristotle.

  IsPractical n = ∀ k ≤ sigma n, n ∈ DivisorSumSet k
  DivisorSumSet t = {n | ∃ s ⊆ Nat.divisors n, t = ∑ i in s, i}

  All definitions come from Erdos859Problem.lean; no sorries in definitions.
-/

import Mathlib
import Proofs.Erdos859Problem

namespace Erdos859Aristotle

open Erdos859 Nat Finset

/-
  ## Section 1: Concrete sigma values
-/

/-- sigma 1 = 1 (only divisor of 1 is 1). -/
lemma sigma_one : sigma 1 = 1 := by native_decide

/-- sigma 2 = 3 (divisors of 2: {1, 2}, sum = 3). -/
lemma sigma_two : sigma 2 = 3 := by native_decide

/-- sigma 6 = 12 (divisors of 6: {1, 2, 3, 6}, sum = 12). -/
lemma sigma_six : sigma 6 = 12 := by native_decide

/-- sigma 12 = 28 (divisors of 12: {1, 2, 3, 4, 6, 12}, sum = 28). -/
lemma sigma_twelve : sigma 12 = 28 := by native_decide

/-
  ## Section 2: Basic DivisorSumSet membership facts
-/

/-- 0 is always representable using the empty sum. -/
lemma mem_divisorSumSet_zero (n : ℕ) : n ∈ DivisorSumSet 0 :=
  ⟨∅, empty_subset _, by simp⟩

/-- Every positive divisor d of n witnesses n ∈ DivisorSumSet d. -/
lemma mem_divisorSumSet_of_dvd (n d : ℕ) (hd : d ∈ Nat.divisors n) :
    n ∈ DivisorSumSet d :=
  ⟨{d}, singleton_subset_iff.mpr hd, by simp⟩

/-
  ## Section 3: IsPractical concrete examples
  Each is a finite check: for k = 0, 1, ..., sigma n, show n ∈ DivisorSumSet k.
-/

/-- 1 is practical: sigma 1 = 1, need ∀ k ≤ 1, 1 ∈ DivisorSumSet k. -/
theorem isPractical_one : IsPractical 1 := by
  sorry

/-- 2 is practical: sigma 2 = 3, need ∀ k ≤ 3, 2 ∈ DivisorSumSet k. -/
theorem isPractical_two : IsPractical 2 := by
  sorry

/-- 6 is practical: sigma 6 = 12, need ∀ k ≤ 12, 6 ∈ DivisorSumSet k. -/
theorem isPractical_six : IsPractical 6 := by
  sorry

/-- 12 is practical: sigma 12 = 28, need ∀ k ≤ 28, 12 ∈ DivisorSumSet k. -/
theorem isPractical_twelve : IsPractical 12 := by
  sorry

/-- All four concrete examples are practical. -/
theorem practical_examples : IsPractical 1 ∧ IsPractical 2 ∧ IsPractical 6 ∧ IsPractical 12 :=
  ⟨isPractical_one, isPractical_two, isPractical_six, isPractical_twelve⟩

end Erdos859Aristotle
