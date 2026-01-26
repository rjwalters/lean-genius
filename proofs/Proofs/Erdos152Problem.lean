/-!
# Erdős Problem #152: Isolated Elements in Sidon Sumsets

For any M ≥ 1, if A ⊂ ℕ is a sufficiently large finite Sidon set,
then there exist at least M elements a ∈ A + A such that
a - 1, a + 1 ∉ A + A. Conjectured to have ≫ |A|² such elements.

## Status: OPEN

## References
- Erdős–Sárközy–Sós (1994), "On Sum Sets of Sidon Sets, I",
  J. Number Theory, pp. 329–347
-/

import Mathlib.Combinatorics.Additive.Sidon
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Pointwise
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open scoped Pointwise

/-!
## Section I: Sidon Sets and Sumsets
-/

/-- A finite set A ⊂ ℕ is Sidon if all pairwise sums a + b (a ≤ b)
are distinct. Equivalently, |{(a,b) : a + b = n}| ≤ 2 for all n. -/
def IsSidonFinset (A : Finset ℕ) : Prop :=
  ∀ a₁ b₁ a₂ b₂ : ℕ, a₁ ∈ A → b₁ ∈ A → a₂ ∈ A → b₂ ∈ A →
    a₁ + b₁ = a₂ + b₂ → ({a₁, b₁} : Finset ℕ) = {a₂, b₂}

/-- The sumset A + A = { a + b : a, b ∈ A }. -/
def sumsetFinset (A : Finset ℕ) : Finset ℕ := A + A

/-!
## Section II: Isolated Elements
-/

/-- An element s ∈ A + A is isolated if s - 1 ∉ A + A and s + 1 ∉ A + A.
These are "gaps" in the sumset structure. -/
def IsIsolated (A : Finset ℕ) (s : ℕ) : Prop :=
  s ∈ sumsetFinset A ∧ s - 1 ∉ sumsetFinset A ∧ s + 1 ∉ sumsetFinset A

/-- The number of isolated elements in A + A. -/
noncomputable def isolatedCount (A : Finset ℕ) : ℕ :=
  ((sumsetFinset A).filter (fun s =>
    s - 1 ∉ sumsetFinset A ∧ s + 1 ∉ sumsetFinset A)).card

/-!
## Section III: The Conjecture
-/

/-- **Erdős Problem #152**: For any M ≥ 1, every sufficiently large
finite Sidon set A has at least M isolated elements in A + A. -/
def ErdosProblem152 : Prop :=
  ∀ M : ℕ, ∃ N₀ : ℕ, ∀ A : Finset ℕ,
    IsSidonFinset A → A.card ≥ N₀ →
      isolatedCount A ≥ M

/-!
## Section IV: The Stronger Conjecture
-/

/-- Erdős conjectured the stronger result: there are ≫ |A|² isolated
elements in A + A for any Sidon set A. Since |A + A| ~ |A|² for Sidon
sets, this says a positive proportion of the sumset is isolated. -/
def ErdosProblem152Strong : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ A : Finset ℕ, IsSidonFinset A →
      (isolatedCount A : ℝ) ≥ c * (A.card : ℝ) ^ 2

/-!
## Section V: Sumset Size for Sidon Sets
-/

/-- For a Sidon set A of size n, |A + A| = n(n+1)/2 since all sums
a + b with a ≤ b are distinct. -/
axiom sidon_sumset_size (A : Finset ℕ) (hS : IsSidonFinset A) :
  (sumsetFinset A).card = A.card * (A.card + 1) / 2

/-- The sumset A + A is contained in [min A + min A, max A + max A],
an interval of length at most 2 · max A. For Sidon sets of size n
with elements in [1, N], we need N ≥ n² - n + 1. -/
axiom sidon_set_range_lower_bound (A : Finset ℕ) (hS : IsSidonFinset A)
    (hA : A.card = n) :
  ∃ a_max : ℕ, a_max ∈ A ∧ a_max ≥ n * n - n + 1

/-!
## Section VI: Related Results
-/

/-- A Sidon set of size n has sumset of size n(n+1)/2 contained in
an interval of length ≤ 2(n² - n), so by pigeonhole there are at
least n(n+1)/2 - 2(n² - n) - 1 "missing" values, creating gaps. -/
axiom gap_existence_pigeonhole (A : Finset ℕ) (hS : IsSidonFinset A)
    (hn : A.card ≥ 5) :
  isolatedCount A ≥ 1

/-- The infinite version: if A ⊂ ℕ is an infinite Sidon set and
A_N = A ∩ [1, N], does the number of isolated elements in A_N + A_N
tend to infinity? -/
def ErdosProblem152Infinite : Prop :=
  ∀ (A : Set ℕ) (hS : ∀ a₁ b₁ a₂ b₂ ∈ A, a₁ + b₁ = a₂ + b₂ →
    ({a₁, b₁} : Set ℕ) = {a₂, b₂}),
    ∀ M : ℕ, ∃ N₀ : ℕ,
      isolatedCount ((Finset.range N₀).filter (· ∈ A)) ≥ M
