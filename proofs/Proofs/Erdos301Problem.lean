/-!
# Erdős Problem 301: Egyptian Fraction Avoidance Sets

Let `f(N)` be the maximum size of `A ⊆ {1, ..., N}` with no solution to
`1/a = 1/b₁ + ⋯ + 1/bₖ` where `a, b₁, ..., bₖ ∈ A` are distinct.

Does `f(N) = (1/2 + o(1)) * N`?

Lower bound: `A = (N/2, N] ∩ ℕ` gives `f(N) ≥ N/2`.
Upper bound: Van Doorn showed `f(N) ≤ (25/28 + o(1)) * N`.

*Reference:* [erdosproblems.com/301](https://www.erdosproblems.com/301)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Finset

/-! ## Egyptian fraction decomposition avoidance -/

/-- `HasEgyptianDecomp A a` means there exist distinct `b₁, ..., bₖ ∈ A` with
`1/a = 1/b₁ + ⋯ + 1/bₖ`, where all elements are distinct from `a`. -/
def HasEgyptianDecomp (A : Finset ℕ) (a : ℕ) : Prop :=
    ∃ B : Finset ℕ, B ⊆ A ∧ a ∉ B ∧ B.Nonempty ∧
      (B.sum (fun b => (1 : ℚ) / b)) = (1 : ℚ) / a

/-- `EgyptFractionFree A` means no element of `A` has an Egyptian fraction
decomposition using other elements of `A`. -/
def EgyptFractionFree (A : Finset ℕ) : Prop :=
    ∀ a ∈ A, ¬HasEgyptianDecomp A a

/-- `f(N)` is the maximum cardinality of an EgyptFractionFree subset of `{1,...,N}`. -/
noncomputable def maxEgyptFree (N : ℕ) : ℕ :=
    ((Finset.Icc 1 N).powerset.filter EgyptFractionFree).sup Finset.card

/-! ## Main conjecture -/

/-- Erdős Problem 301: `f(N) = (1/2 + o(1)) * N`. -/
def ErdosProblem301 : Prop :=
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (1 / 2 - ε) * N ≤ (maxEgyptFree N : ℝ) ∧
      (maxEgyptFree N : ℝ) ≤ (1 / 2 + ε) * N

/-! ## Lower bound -/

/-- The interval `(N/2, N]` is EgyptFractionFree, giving `f(N) ≥ N/2`. -/
axiom halfInterval_egyptFree (N : ℕ) :
    EgyptFractionFree ((Finset.Icc 1 N).filter (fun n => N / 2 < n))

/-- Lower bound: `f(N) ≥ N/2`. -/
axiom maxEgyptFree_lower (N : ℕ) (hN : 0 < N) :
    N / 2 ≤ maxEgyptFree N

/-! ## Upper bound (van Doorn) -/

/-- Van Doorn's upper bound: `f(N) ≤ (25/28 + o(1)) * N`. -/
axiom vanDoorn_upper (N : ℕ) (hN : 0 < N) :
    (maxEgyptFree N : ℝ) ≤ (25 / 28 + 1) * N

/-! ## Basic properties -/

/-- The empty set is EgyptFractionFree. -/
theorem egyptFractionFree_empty : EgyptFractionFree ∅ := by
  intro a ha; exact absurd ha (Finset.not_mem_empty a)

/-- A singleton is EgyptFractionFree (no other elements to decompose into). -/
axiom egyptFractionFree_singleton (n : ℕ) : EgyptFractionFree {n}

/-- Subsets of EgyptFractionFree sets are EgyptFractionFree. -/
theorem egyptFractionFree_subset {A B : Finset ℕ} (h : B ⊆ A) (hA : EgyptFractionFree A) :
    EgyptFractionFree B := by
  intro a ha ⟨C, hC, haC, hne, hsum⟩
  exact hA a (h ha) ⟨C, hC.trans h, haC, hne, hsum⟩
