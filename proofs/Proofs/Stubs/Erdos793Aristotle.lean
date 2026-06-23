/-
  Aristotle targets for Erdős Problem #793: Primitive Sets Avoiding Product Divisibility
  Routine supporting lemmas for automated proof search.
  See Stubs/Erdos793Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the open problem (exact asymptotics of F(n))
  - NOT theorems depending on axiomatized bounds (F_lower_bound, F_upper_bound)
  - Routine properties of satisfiesCondition and basic divisibility
  - No definition sorries
  - No axioms

  Included targets (5):
  - satisfiesCondition_empty: empty set satisfies the condition (vacuous)
  - satisfiesCondition_singleton: singleton set satisfies the condition (vacuous)
  - satisfiesCondition_antitone: subset of satisfying set also satisfies
  - noDividesProduct_empty: empty set satisfies noDividesProduct (vacuous)
  - Icc_nat_card: (Finset.Icc 1 n).card = n
-/
import Mathlib

open Finset Nat

namespace Erdos793Aristotle

def satisfiesCondition (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
    a ≠ b → a ≠ c → ¬(a ∣ b * c)

def noDividesProduct (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
    a ≠ b → a ≠ c → b ≠ c → ¬(a ∣ b * c)

-- Routine: empty set satisfies the condition.
-- Vacuously true since ∅ has no elements.
theorem satisfiesCondition_empty : satisfiesCondition ∅ := by
  sorry

-- Routine: singleton set satisfies the condition.
-- For {a}: any b, c ∈ {a} must equal a, contradicting a ≠ b or a ≠ c.
theorem satisfiesCondition_singleton (a : ℕ) : satisfiesCondition {a} := by
  sorry

-- Routine: sub-family of a satisfying set also satisfies.
-- If A satisfies the condition and B ⊆ A, then B satisfies it too.
theorem satisfiesCondition_antitone (A B : Finset ℕ) (hBA : B ⊆ A)
    (hA : satisfiesCondition A) : satisfiesCondition B := by
  sorry

-- Routine: empty set satisfies noDividesProduct.
-- Vacuously true since ∅ has no elements.
theorem noDividesProduct_empty : noDividesProduct ∅ := by
  sorry

-- Routine: Finset.Icc 1 n has exactly n elements.
-- This is a basic Finset.card fact.
theorem Icc_nat_card (n : ℕ) : (Finset.Icc 1 n).card = n := by
  sorry

end Erdos793Aristotle
