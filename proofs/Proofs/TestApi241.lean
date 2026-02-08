-- Test API for Erdős 241
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Tactic

-- IsB3 definition from the problem file
def IsB3 (A : Finset ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ b₁ ∈ A, ∀ c₁ ∈ A,
  ∀ a₂ ∈ A, ∀ b₂ ∈ A, ∀ c₂ ∈ A,
    a₁ ≤ b₁ → b₁ ≤ c₁ → a₂ ≤ b₂ → b₂ ≤ c₂ →
    a₁ + b₁ + c₁ = a₂ + b₂ + c₂ →
    a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂

-- Test with native_decide
theorem test_b3 : IsB3 {1, 2, 4, 8} := by native_decide

