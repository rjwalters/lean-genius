/-
# Erdős Problem #241: Maximum Size of B₃ Sets

Let f(N) be the maximum size of A ⊆ {1,...,N} such that all
three-element sums a + b + c (a ≤ b ≤ c, a,b,c ∈ A) are distinct.
Is f(N) ~ N^{1/3}?

## Status: OPEN ($100 prize)

## References
- Bose–Chowla, "Theorems in the additive theory of numbers" (1962)
- Green, "The number of squares and B_h[g] sets" (2001)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-
## Section I: B₃ Sets
-/

/-- The multiset of ordered three-element sums from A. -/
def threeSums (A : Finset ℕ) : Finset ℕ :=
  ((A ×ˢ A ×ˢ A).filter (fun t => t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2)).image
    (fun t => t.1 + t.2.1 + t.2.2)

/-- A set A is B₃ if all ordered triples (a,b,c) with a ≤ b ≤ c from A
give distinct sums a + b + c. Equivalently, a₁+b₁+c₁ = a₂+b₂+c₂ implies
{a₁,b₁,c₁} = {a₂,b₂,c₂} as multisets. -/
def IsB3 (A : Finset ℕ) : Prop :=
  ∀ a₁ ∈ A, ∀ b₁ ∈ A, ∀ c₁ ∈ A,
  ∀ a₂ ∈ A, ∀ b₂ ∈ A, ∀ c₂ ∈ A,
    a₁ ≤ b₁ → b₁ ≤ c₁ → a₂ ≤ b₂ → b₂ ≤ c₂ →
    a₁ + b₁ + c₁ = a₂ + b₂ + c₂ →
    a₁ = a₂ ∧ b₁ = b₂ ∧ c₁ = c₂

noncomputable instance : DecidablePred (fun S : Finset ℕ => IsB3 S) :=
  fun _ => Classical.dec _

/-
## Section II: Maximum B₃ Subset Size
-/

/-- f(N): the maximum size of a B₃ subset of {1,...,N}. -/
noncomputable def maxB3Size (N : ℕ) : ℕ :=
  ((Finset.range N).powerset.filter (fun S => IsB3 S)).sup Finset.card

/-
## Section III: The Conjecture
-/

/-- **Erdős Problem #241**: Is f(N) ~ N^{1/3}?

More precisely: is it true that f(N) / N^{1/3} → 1 as N → ∞?
This would mean the Bose–Chowla construction is asymptotically optimal. -/
def ErdosProblem241 : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (1 - ε) * (N : ℝ) ^ (1/3 : ℝ) ≤ (maxB3Size N : ℝ) ∧
      (maxB3Size N : ℝ) ≤ (1 + ε) * (N : ℝ) ^ (1/3 : ℝ)

/-
## Section IV: The Bose–Chowla Lower Bound
-/

/-- Bose and Chowla (1962) proved that f(N) ≥ (1+o(1)) · N^{1/3}.
They constructed explicit B₃ sets of this size using finite fields. -/

/-
## Section V: Green's Upper Bound
-/

/-- Green (2001) proved f(N) ≤ ((7/2)^{1/3} + o(1)) · N^{1/3},
where (7/2)^{1/3} ≈ 1.519. This is the best known upper bound. -/

/-
## Section VI: Generalized Bₕ Sets
-/

/-- A set A is Bₕ if all h-element sums with a₁ ≤ ... ≤ aₕ are distinct.
B₂ sets are Sidon sets (Problem #30). B₃ sets are the subject of this problem. -/
def IsBh (h : ℕ) (A : Finset ℕ) : Prop :=
  h ≥ 2 ∧
  ∀ (S₁ S₂ : Finset ℕ),
    S₁ ⊆ A → S₂ ⊆ A → S₁.card = h → S₂.card = h →
    S₁.sum id = S₂.sum id → S₁ = S₂

noncomputable instance (h : ℕ) : DecidablePred (fun S : Finset ℕ => IsBh h S) :=
  fun _ => Classical.dec _

/-- Maximum size of a Bₕ subset of {1,...,N}. -/
noncomputable def maxBhSize (h N : ℕ) : ℕ :=
  ((Finset.range N).powerset.filter (fun S => IsBh h S)).sup Finset.card

/-- Bose–Chowla conjecture (general): for all h ≥ 2,
the maximum Bₕ set in {1,...,N} has size ~ N^{1/h}. -/
def BoseChowlaConjecture (h : ℕ) : Prop :=
  h ≥ 2 →
  ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
      (1 - ε) * (N : ℝ) ^ (1 / (h : ℝ)) ≤ (maxBhSize h N : ℝ) ∧
      (maxBhSize h N : ℝ) ≤ (1 + ε) * (N : ℝ) ^ (1 / (h : ℝ))

/-- The case h = 2 (Sidon sets) is resolved: Problem #30. -/

/-- Bose–Chowla lower bound holds for all h ≥ 2. -/

/-
## Section VII: Known Small B₃ Sets
-/

/-- Example: {1, 5, 14, 30} is a B₃ set.
All 20 ordered triple sums (a ≤ b ≤ c) are distinct:
3, 7, 11, 15, 16, 20, 24, 29, 32, 33, 36, 40, 42, 45, 49, 58, 61, 65, 74, 90.

Note: The previously claimed {1,2,4,8} is NOT B₃ since 1+1+4 = 2+2+2 = 6. -/

/-- The trivial upper bound: a B₃ set in {1,...,N} has at most
O(N^{1/3}) elements since distinct sums lie in {3,...,3N}. -/
