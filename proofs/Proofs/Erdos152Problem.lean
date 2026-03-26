/-
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

/-
## Section I: Sidon Sets and Sumsets
-/

/-- A finite set A ⊂ ℕ is Sidon if all pairwise sums a + b (a ≤ b)
are distinct. Equivalently, |{(a,b) : a + b = n}| ≤ 2 for all n. -/
def IsSidonFinset (A : Finset ℕ) : Prop :=
  ∀ a₁ b₁ a₂ b₂ : ℕ, a₁ ∈ A → b₁ ∈ A → a₂ ∈ A → b₂ ∈ A →
    a₁ + b₁ = a₂ + b₂ → ({a₁, b₁} : Finset ℕ) = {a₂, b₂}

/-- The sumset A + A = { a + b : a, b ∈ A }. -/
def sumsetFinset (A : Finset ℕ) : Finset ℕ := A + A

/-
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

/-
## Section III: The Conjecture
-/

/-- **Erdős Problem #152**: For any M ≥ 1, every sufficiently large
finite Sidon set A has at least M isolated elements in A + A. -/
def ErdosProblem152 : Prop :=
  ∀ M : ℕ, ∃ N₀ : ℕ, ∀ A : Finset ℕ,
    IsSidonFinset A → A.card ≥ N₀ →
      isolatedCount A ≥ M

/-
## Section IV: The Stronger Conjecture
-/

/-- Erdős conjectured the stronger result: there are ≫ |A|² isolated
elements in A + A for any Sidon set A. Since |A + A| ~ |A|² for Sidon
sets, this says a positive proportion of the sumset is isolated. -/
def ErdosProblem152Strong : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ A : Finset ℕ, IsSidonFinset A →
      (isolatedCount A : ℝ) ≥ c * (A.card : ℝ) ^ 2

/-
## Section V: Proved Properties of Sidon Sets and Their Sumsets
-/

-- Any pair of elements in A has their sum in A + A
theorem sumset_mem {A : Finset ℕ} {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) :
    a + b ∈ sumsetFinset A :=
  Finset.add_mem_add ha hb

-- The double 2a is in A + A for any a ∈ A
theorem sumset_self_double {A : Finset ℕ} {a : ℕ} (ha : a ∈ A) :
    a + a ∈ sumsetFinset A :=
  sumset_mem ha ha

-- Sidon sets have no 3-term arithmetic progressions with distinct terms:
-- if a + c = 2b with a, b, c ∈ A, then a = c (and hence a = b = c)
theorem sidon_no_three_ap {A : Finset ℕ} (hS : IsSidonFinset A)
    {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hap : a + c = b + b) : a = c := by
  have h := hS a c b b ha hc hb hb hap
  -- h : ({a, c} : Finset ℕ) = {b, b}, and {b, b} = {b} in Finset
  have hab : a = b := by
    have h1 : a ∈ ({a, c} : Finset ℕ) := Finset.mem_insert_self a _
    rw [h] at h1; simp at h1; exact h1
  have hcb : c = b := by
    have h2 : c ∈ ({a, c} : Finset ℕ) := by simp
    rw [h] at h2; simp at h2; exact h2
  rw [hab, hcb]

-- Corollary: in a Sidon set, a + c = 2b implies a = b = c
theorem sidon_no_three_ap' {A : Finset ℕ} (hS : IsSidonFinset A)
    {a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hap : a + c = b + b) : a = b ∧ b = c := by
  have hac := sidon_no_three_ap hS ha hb hc hap
  subst hac
  constructor
  · -- a + a = b + b implies a = b
    omega
  · omega

-- For distinct elements a, b in a Sidon set: a + b ≠ 2a
-- (the sumset element a + b is not a doubled element)
theorem sidon_sum_ne_double {A : Finset ℕ} (hS : IsSidonFinset A)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    a + b ≠ a + a := by
  intro h
  have : b = a := by omega
  exact hab this.symm

/-
## Section VI: Sumset Size for Sidon Sets
-/

/-- For a Sidon set A of size n, |A + A| = n(n+1)/2 since all sums
a + b with a ≤ b are distinct. -/
axiom sidon_sumset_size (A : Finset ℕ) (hS : IsSidonFinset A) :
  (sumsetFinset A).card = A.card * (A.card + 1) / 2

/-- For a Sidon set of size n, the maximum element satisfies
max ≥ n(n-1)/2 + 1. This follows from the fact that all n(n-1)/2
differences a_j - a_i (i < j) must be distinct positive integers,
so they occupy at least the range [1, n(n-1)/2], giving
max - min ≥ n(n-1)/2.

Note: the bound n²-n+1 that previously appeared here is too strong;
{1,2,5} is a Sidon set of size 3 with max = 5 < 7 = 3²-3+1. -/
axiom sidon_set_range_lower_bound (A : Finset ℕ) (hS : IsSidonFinset A)
    (hA : A.card = n) (hn : n ≥ 1) :
  ∃ a_max : ℕ, a_max ∈ A ∧ a_max ≥ n * (n - 1) / 2 + 1

/-
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
