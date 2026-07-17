-- Test API for Erdős 241
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Tactic

-- IsB3 definition from the problem file.
-- A set A is B₃ (a Sidon set of order 3) if every sorted triple of elements
-- has a distinct sum: equal 3-element sums force equal (sorted) triples.
def IsB3 (A : Finset ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ b₁ ∈ A, ∀ c₁ ∈ A,
  ∀ a₂ ∈ A, ∀ b₂ ∈ A, ∀ c₂ ∈ A,
    a₁ ≤ b₁ → b₁ ≤ c₁ → a₂ ≤ b₂ → b₂ ≤ c₂ →
    a₁ + b₁ + c₁ = a₂ + b₂ + c₂ →
    a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂

-- `{1, 2, 4, 8}` is NOT B₃ (e.g. 1+1+4 = 6 = 2+2+2, distinct sorted triples,
-- same sum), so the correct positive witness uses powers of a base > 3.
-- Powers of 4 are B₃: a 3-element multiset sum is a base-4 numeral with all
-- digits ≤ 3, hence uniquely determined by its value.
theorem test_b3 : IsB3 {1, 4, 16, 64} := by unfold IsB3; decide
