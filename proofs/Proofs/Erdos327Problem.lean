/-!
# Erdős Problem 327: Sum-Divides-Product Avoidance

Let `A ⊆ {1, ..., N}` have the property that for all distinct `a, b ∈ A`,
`a + b ∤ a * b`. Note that `a + b ∣ a * b` iff `1/a + 1/b` is a unit fraction.

Can `A` be substantially larger than the set of odd numbers in `{1, ..., N}`?

Van Doorn showed: if `|A| ≥ (25/28 + o(1)) * N`, then `A` must contain
`a ≠ b` with `a + b ∣ a * b`.

A variant asks: if `a + b ∤ 2 * a * b` for all distinct `a, b ∈ A`, must `|A| = o(N)`?

*Reference:* [erdosproblems.com/327](https://www.erdosproblems.com/327)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Finset

/-! ## Sum-divides-product property -/

/-- `SumNotDvdProd A` means for all distinct `a, b ∈ A`, `a + b ∤ a * b`. -/
def SumNotDvdProd (A : Finset ℕ) : Prop :=
    ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬(a + b ∣ a * b)

/-- `SumNotDvdTwoProd A` means for all distinct `a, b ∈ A`, `a + b ∤ 2 * a * b`. -/
def SumNotDvdTwoProd (A : Finset ℕ) : Prop :=
    ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬(a + b ∣ 2 * a * b)

/-- The maximum size of a subset of `{1, ..., N}` with `SumNotDvdProd`. -/
noncomputable def maxAvoidSize (N : ℕ) : ℕ :=
    ((Finset.Icc 1 N).powerset.filter SumNotDvdProd).sup Finset.card

/-! ## Main conjecture -/

/-- Erdős Problem 327: The maximum size of a SumNotDvdProd subset of `{1,...,N}`
is asymptotically at most `N/2 + o(N)` (no larger than the odd numbers). -/
def ErdosProblem327 : Prop :=
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (maxAvoidSize N : ℝ) ≤ (1 / 2 + ε) * N

/-! ## Van Doorn's bound -/

/-- Van Doorn's result: if `|A| ≥ (25/28) * N`, then `A` contains `a ≠ b`
with `a + b ∣ a * b`. -/
axiom vanDoorn_bound (N : ℕ) (A : Finset ℕ) :
    A ⊆ Finset.Icc 1 N → (25 * N ≤ 28 * A.card) →
      ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ a + b ∣ a * b

/-! ## Variant: factor-of-2 condition -/

/-- Variant conjecture: if `a + b ∤ 2ab` for distinct `a, b ∈ A ⊆ {1,...,N}`,
then `|A| = o(N)`. -/
def ErdosProblem327_variant : Prop :=
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N → SumNotDvdTwoProd A →
        (A.card : ℝ) ≤ ε * N

/-! ## Unit fraction equivalence -/

/-- `a + b ∣ a * b` iff `1/a + 1/b` is a unit fraction (i.e., `1/c` for some `c`). -/
axiom sumDvdProd_iff_unitFraction (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    a + b ∣ a * b ↔ ∃ c : ℕ, 0 < c ∧ (1 : ℚ) / a + (1 : ℚ) / b = (1 : ℚ) / c

/-! ## Basic properties -/

/-- The empty set trivially satisfies SumNotDvdProd. -/
theorem sumNotDvdProd_empty : SumNotDvdProd ∅ := by
  intro a ha; exact absurd ha (Finset.not_mem_empty a)

/-- A singleton trivially satisfies SumNotDvdProd. -/
theorem sumNotDvdProd_singleton (n : ℕ) : SumNotDvdProd {n} := by
  intro a ha b hb hab
  rw [Finset.mem_singleton] at ha hb
  exact absurd (ha.trans hb.symm) hab

/-- If `B ⊆ A` and `A` has SumNotDvdProd, then so does `B`. -/
theorem sumNotDvdProd_subset {A B : Finset ℕ} (h : B ⊆ A) (hA : SumNotDvdProd A) :
    SumNotDvdProd B := fun a ha b hb => hA a (h ha) b (h hb)

/-- The odd numbers in `{1,...,N}` satisfy SumNotDvdProd (since `a+b` is even
but `a*b` is odd for odd `a, b`). -/
axiom oddNumbers_sumNotDvdProd (N : ℕ) :
    SumNotDvdProd ((Finset.Icc 1 N).filter (fun n => n % 2 = 1))
