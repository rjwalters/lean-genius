/-!
# Erdős Problem 1103: Squarefree Sumsets

Let `A` be an infinite sequence of positive integers such that every element of
`A + A = {a + b : a, b ∈ A}` is squarefree. How fast must `A` grow?

Erdős expected that no such sequence of polynomial growth exists — exponential
growth may be necessary.

## Known results

- An exponential-growth sequence satisfying the conditions exists.
- van Doorn–Tao (2025) proved an exponential upper bound: `a_j < exp(5j / log j)`
  for large `j`.
- van Doorn–Tao proved a polynomial lower bound: `a_j > 0.24 · j^{4/3}` for all `j`.
- Konyagin: `a_j ≫ j^{15/11 - o(1)}` (finite case).

*Reference:* [erdosproblems.com/1103](https://www.erdosproblems.com/1103)
-/

import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Finset Filter

/-! ## Definitions -/

/-- `SquarefreeSumset A` holds when every element of `A + A` is squarefree,
i.e., for all `a, b ∈ A`, `a + b` is squarefree. -/
def SquarefreeSumset (A : Set ℕ) : Prop :=
    ∀ a ∈ A, ∀ b ∈ A, Squarefree (a + b)

/-- An increasing enumeration of a set: `enumSet A j` is the `j`-th smallest element.
We axiomatize this as a strictly monotone bijection onto `A`. -/
axiom enumSet : Set ℕ → ℕ → ℕ

/-- The enumeration is strictly monotone and surjects onto `A`. -/
axiom enumSet_spec (A : Set ℕ) (hA : A.Infinite) :
    StrictMono (enumSet A) ∧ Set.range (enumSet A) = A

/-! ## Main conjecture -/

/-- Erdős Problem 1103: Does every infinite `A ⊆ ℕ` with `SquarefreeSumset A`
grow at least exponentially? That is, does there exist `C > 1` such that
`a_j ≥ C^j` for all large `j`? -/
def ErdosProblem1103 : Prop :=
    ∀ A : Set ℕ, A.Infinite → SquarefreeSumset A →
      ∃ (C : ℝ), 1 < C ∧ ∀ᶠ j in atTop,
        C ^ (j : ℝ) ≤ (enumSet A j : ℝ)

/-! ## Known bounds -/

/-- van Doorn–Tao upper bound: there exists an infinite squarefree-sumset
sequence with `a_j < exp(5j / log j)` for large `j`. -/
axiom vanDoorn_tao_upper :
    ∃ A : Set ℕ, A.Infinite ∧ SquarefreeSumset A ∧
      ∀ᶠ j in atTop,
        (enumSet A j : ℝ) < Real.exp (5 * (j : ℝ) / Real.log j)

/-- van Doorn–Tao lower bound: `a_j > 0.24 · j^{4/3}` for any infinite
squarefree-sumset sequence. -/
axiom vanDoorn_tao_lower (A : Set ℕ) (hA : A.Infinite) (hS : SquarefreeSumset A) :
    ∀ j : ℕ, (0.24 : ℝ) * (j : ℝ) ^ (4/3 : ℝ) < (enumSet A j : ℝ)

/-- Konyagin's bound for finite sets: for `A ⊆ {1,...,N}` with squarefree sumset,
`|A| ≪ N^{11/15 + o(1)}`. -/
axiom konyagin_finite_bound :
    ∃ (C : ℝ), 0 < C ∧ ∀ N : ℕ, ∀ A : Finset ℕ,
      (∀ a ∈ A, a ≤ N) →
      (∀ a ∈ A, ∀ b ∈ A, Squarefree (a + b)) →
        (A.card : ℝ) ≤ C * (N : ℝ) ^ (11/15 : ℝ)

/-! ## Basic properties -/

/-- Every singleton set has a squarefree sumset iff `2a` is squarefree. -/
axiom squarefreeSumset_singleton (a : ℕ) :
    SquarefreeSumset {a} ↔ Squarefree (a + a)

/-- The empty set trivially has a squarefree sumset. -/
theorem squarefreeSumset_empty : SquarefreeSumset ∅ := by
  intro a ha; exact absurd ha (Set.not_mem_empty a)

/-- If `SquarefreeSumset A` and `B ⊆ A`, then `SquarefreeSumset B`. -/
theorem squarefreeSumset_subset {A B : Set ℕ} (h : B ⊆ A) (hA : SquarefreeSumset A) :
    SquarefreeSumset B :=
  fun a ha b hb => hA a (h ha) b (h hb)

/-- `1` is squarefree (basic fact used in constructions). -/
theorem one_squarefree : Squarefree 1 := squarefree_one
