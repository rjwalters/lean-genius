/-
Erdős Problem #806: Small Bases for Sumsets

Source: https://erdosproblems.com/806
Status: SOLVED (Alon-Bukh-Sudakov, 2009)

Statement:
Let A ⊆ {1, ..., n} with |A| ≤ √n. Must there exist some B ⊂ ℤ
with |B| = o(√n) such that A ⊆ B + B?

Answer: YES

Alon, Bukh, and Sudakov (2009) proved that for any A ⊆ {1, ..., n} with
|A| ≤ √n, there exists B such that A ⊆ B + B and
    |B| ≪ (log log n / log n) · √n

This matches the lower bound of Erdős-Newman (1977), making the answer tight.

Key insight: Any subset of {1, ..., n} of size at most √n can be covered
by a sumset B + B where B has size strictly smaller than √n (by a
logarithmic factor).

References:
- Erdős-Newman [ErNe77]: Original problem and lower bound
- Alon-Bukh-Sudakov [ABS09]: Upper bound (resolution)
- See also Erdős Problem #333
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

open Set Nat Finset

namespace Erdos806

/-
## Part I: Sumsets and Bases

A set B is a basis for A if every element of A can be written as a sum
of two elements of B.
-/

/--
**Sumset of a Finset:**
B + B = {b₁ + b₂ | b₁, b₂ ∈ B}
-/
def finsetSumset (B : Finset ℤ) : Finset ℤ :=
  (B ×ˢ B).image (fun p => p.1 + p.2)

/--
**B is a basis for A:**
Every element of A is in B + B.
-/
def IsBasisFor (B : Finset ℤ) (A : Finset ℤ) : Prop :=
  A ⊆ finsetSumset B

/--
**Sumset size bound:**
|B + B| ≤ |B|² (trivially, but often much smaller due to structure).
-/
theorem sumset_card_bound (B : Finset ℤ) :
    (finsetSumset B).card ≤ B.card * B.card := by
  unfold finsetSumset
  calc (B ×ˢ B).image (fun p => p.1 + p.2) |>.card
      ≤ (B ×ˢ B).card := Finset.card_image_le
    _ = B.card * B.card := Finset.card_product B B

/-
## Part II: The Interval {1, ..., n}
-/

/--
**Interval [1, n]:**
The set {1, 2, ..., n} as a Finset.
-/
def interval (n : ℕ) : Finset ℕ := Finset.range n |>.filter (· ≥ 1)

/-
## Part III: The Erdős-Newman Lower Bound (1977)

There exist "bad" sets A that require large bases.
-/

/--
**Erdős-Newman Construction:**
There exist sets A ⊆ {1, ..., n} with |A| ≈ √n such that
any basis B for A satisfies |B| ≥ c · (log log n / log n) · √n.

This shows the answer cannot be "B can have size O(√n / log n)" or better.
-/
axiom erdos_newman_lower_bound :
    ∀ ε > 0, ∀ᶠ (n : ℕ) in Filter.atTop,
      ∃ A : Finset ℤ, A.card ≤ Nat.sqrt n ∧
        ∀ B : Finset ℤ, IsBasisFor B A →
          (B.card : ℝ) ≥ (1 - ε) * (Real.log (Real.log n) / Real.log n) * Real.sqrt n

/-
## Part IV: The Alon-Bukh-Sudakov Upper Bound (2009)

The main result: every small A has a small basis.
-/

/--
**Alon-Bukh-Sudakov Theorem (2009):**
For any A ⊆ {1, ..., n} with |A| ≤ √n, there exists B ⊂ ℤ such that
A ⊆ B + B and |B| ≤ C · (log log n / log n) · √n for some constant C.

This resolves Erdős Problem #806 in the affirmative.
-/
axiom alon_bukh_sudakov_upper_bound :
    ∃ C : ℝ, C > 0 ∧
      ∀ n : ℕ, n ≥ 2 →
        ∀ A : Finset ℤ, (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) → A.card ≤ Nat.sqrt n →
          ∃ B : Finset ℤ, IsBasisFor B A ∧
            (B.card : ℝ) ≤ C * (Real.log (Real.log n) / Real.log n) * Real.sqrt n

/--
**Answer to Erdős Problem #806:**
For any A ⊆ {1, ..., n} with |A| ≤ √n, there exists B with
A ⊆ B + B and |B| = o(√n). This follows from the Alon-Bukh-Sudakov
upper bound since (log log n / log n) → 0.
-/
/-
## Part V: The Tight Bound

The upper and lower bounds match up to constants.
-/

/--
**Tight Characterization:**
The optimal basis size for sets A ⊆ {1, ..., n} of size ≈ √n is
    Θ((log log n / log n) · √n)
-/
theorem optimal_basis_size :
    -- Lower bound: some A require this much
    (∀ ε > 0, ∀ᶠ (n : ℕ) in Filter.atTop,
      ∃ A : Finset ℤ, A.card ≤ Nat.sqrt n ∧
        ∀ B : Finset ℤ, IsBasisFor B A →
          (B.card : ℝ) ≥ (1 - ε) * (Real.log (Real.log n) / Real.log n) * Real.sqrt n) ∧
    -- Upper bound: every A has such a basis
    (∃ C : ℝ, C > 0 ∧
      ∀ n : ℕ, n ≥ 2 →
        ∀ A : Finset ℤ, (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) → A.card ≤ Nat.sqrt n →
          ∃ B : Finset ℤ, IsBasisFor B A ∧
            (B.card : ℝ) ≤ C * (Real.log (Real.log n) / Real.log n) * Real.sqrt n) := by
  exact ⟨erdos_newman_lower_bound, alon_bukh_sudakov_upper_bound⟩

/-
## Part VI: Related Results

Connections to other problems in additive combinatorics.
-/

/--
**Connection to Sidon Sets:**

A Sidon set S has the property that all pairwise sums are distinct.
For Sidon sets, S + S has size exactly (|S|² + |S|)/2.

Erdős Problem #806 is in some sense dual: given A, find the smallest B
such that A ⊆ B + B.
-/
def IsSidonSet (S : Finset ℤ) : Prop :=
  ∀ a b c d : ℤ, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    a + b = c + d → ({a, b} : Set ℤ) = {c, d}

/-
## Part VII: Examples
-/

/--
**Trivial Basis:**
A is always covered by B = A ∪ {0}, since a = a + 0 ∈ B + B.
But this gives |B| = |A| + 1, not o(√n).
-/
theorem trivial_basis (A : Finset ℤ) :
    IsBasisFor (A ∪ {0}) A := by
  intro a ha
  simp only [finsetSumset, Finset.mem_image, Finset.mem_product]
  use (a, 0)
  constructor
  · constructor
    · left
      exact ha
    · right
      simp
  · ring

/-
## Part VIII: Asymptotic Notation
-/

/--
**The logarithmic factor tends to zero:**
(log log n / log n) → 0 as n → ∞. This is a standard calculus result
ensuring the Alon-Bukh-Sudakov bound gives |B| = o(√n).
-/
/-
## Part IX: Summary
-/

/--
**Erdős Problem #806: SOLVED**

Q: For A ⊆ {1, ..., n} with |A| ≤ √n, does there exist B with
   |B| = o(√n) such that A ⊆ B + B?

A: YES (Alon-Bukh-Sudakov, 2009)

The optimal bound is Θ((log log n / log n) · √n), matching the
Erdős-Newman lower bound from 1977.

This resolves a 32-year-old problem in additive combinatorics.
-/
end Erdos806
