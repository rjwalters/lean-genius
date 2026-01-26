/-!
# Erdős Problem #43: Sidon Sets with Disjoint Difference Sets

If A, B ⊆ {1,...,N} are Sidon sets with (A-A) ∩ (B-B) = {0},
must C(|A|,2) + C(|B|,2) ≤ C(f(N),2) + O(1), where f(N) is
the maximum Sidon set size in {1,...,N}?

## Status: OPEN ($100 bounty)

## References
- Erdős
- Tao (partial progress)
- Barreto (negative answer to equal-size variant)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
## Section I: Sidon Sets
-/

/-- A Sidon set (B₂ set): all pairwise sums a + b (a ≤ b, a,b ∈ A) are distinct,
equivalently all nonzero pairwise differences are distinct. -/
def IsSidonSet (A : Finset ℤ) : Prop :=
  ∀ a₁ b₁ a₂ b₂ : ℤ, a₁ ∈ A → b₁ ∈ A → a₂ ∈ A → b₂ ∈ A →
    a₁ + b₁ = a₂ + b₂ → ({a₁, b₁} : Finset ℤ) = {a₂, b₂}

/-- The difference set A - A = { a - b | a, b ∈ A }. -/
def diffSet (A : Finset ℤ) : Finset ℤ :=
  (A ×ˢ A).image (fun p => p.1 - p.2)

/-!
## Section II: Disjoint Differences
-/

/-- Two sets have disjoint nonzero differences: (A-A) ∩ (B-B) = {0}. -/
def DisjointDifferences (A B : Finset ℤ) : Prop :=
  ∀ d : ℤ, d ∈ diffSet A → d ∈ diffSet B → d = 0

/-!
## Section III: Maximum Sidon Set Size
-/

/-- f(N): the maximum cardinality of a Sidon set in {1,...,N}. -/
axiom maxSidonSize : ℕ → ℕ

/-- f(N) ~ √N: the maximum Sidon set size is asymptotically √N. -/
axiom sidon_size_asymptotic :
  ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    |(maxSidonSize N : ℝ) - Real.sqrt N| ≤ ε * Real.sqrt N

/-!
## Section IV: The Conjecture
-/

/-- **Erdős Problem #43**: If A, B are Sidon sets in {1,...,N} with
disjoint nonzero differences, then C(|A|,2) + C(|B|,2) ≤ C(f(N),2) + O(1). -/
def ErdosProblem43 : Prop :=
  ∃ C : ℕ, ∀ N : ℕ, ∀ A B : Finset ℤ,
    IsSidonSet A → IsSidonSet B →
    (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) → (∀ b ∈ B, 1 ≤ b ∧ b ≤ N) →
    DisjointDifferences A B →
    A.card.choose 2 + B.card.choose 2 ≤ (maxSidonSize N).choose 2 + C

/-!
## Section V: Equal Size Variant
-/

/-- The equal-size strengthening: when |A| = |B|, can we get
C(|A|,2) + C(|B|,2) ≤ (1 - c)·C(f(N),2) for some c > 0?
Barreto showed this is FALSE for infinitely many N. -/
def EqualSizeVariant : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, ∀ A B : Finset ℤ,
    IsSidonSet A → IsSidonSet B →
    (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) → (∀ b ∈ B, 1 ≤ b ∧ b ≤ N) →
    DisjointDifferences A B → A.card = B.card →
    (A.card.choose 2 + B.card.choose 2 : ℝ) ≤ (1 - c) * (maxSidonSize N).choose 2

/-- Barreto's result: the equal-size variant is false. -/
axiom barreto_counterexample : ¬EqualSizeVariant

/-!
## Section VI: Structural Bounds
-/

/-- A single Sidon set A in {1,...,N} has C(|A|,2) ≤ N. -/
axiom sidon_pair_bound (A : Finset ℤ) (N : ℕ)
    (hS : IsSidonSet A) (hR : ∀ a ∈ A, 1 ≤ a ∧ a ≤ N) :
  A.card.choose 2 ≤ N

/-- Disjoint differences force A ∪ B to have distinct nonzero
differences, bounding the combined size. -/
axiom disjoint_diff_combined_bound (A B : Finset ℤ) (N : ℕ)
    (hA : IsSidonSet A) (hB : IsSidonSet B)
    (hRA : ∀ a ∈ A, 1 ≤ a ∧ a ≤ N) (hRB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ N)
    (hD : DisjointDifferences A B) :
  A.card.choose 2 + B.card.choose 2 ≤ N
