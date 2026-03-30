/-
Erdős Problem #843: Are the Squares Ramsey 2-Complete?

Source: https://erdosproblems.com/843
Status: SOLVED (Answer: YES, by Burr unpublished; Conlon-Fox-Pham 2021)
Prize: Part of combined $350 for Ramsey completeness problems

Statement:
Are the squares Ramsey 2-complete? That is, is it true that, in any 2-colouring
of the square numbers, every sufficiently large n ∈ ℕ can be written as a
monochromatic sum of distinct squares?

Definition:
A set A ⊆ ℕ is **Ramsey r-complete** if, for every r-coloring of A, all
sufficiently large integers can be written as a monochromatic sum of distinct
elements from A.

Background:
- Burr and Erdős proposed this problem
- Similar question for k-th powers (k ≥ 3) is also interesting
- Erdős (1995) reported Burr proved k-th powers are Ramsey r-complete for all r,k ≥ 2
  but this was never published

Resolution:
- Conlon-Fox-Pham (2021): Proved the stronger result that k-th powers contain
  a SPARSE Ramsey r-complete subsequence for all r,k ≥ 2
- This implies squares are Ramsey 2-complete (and much more)

Reference:
- Conlon, Fox, Pham: "Subset sums, completeness and colorings" arXiv:2104.14766 (2021)
- Erdős: "Some of my favourite problems..." Resenhas (1995)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.NumberTheory.SumFourSquares

open Nat Finset

namespace Erdos843

/-
## Part I: Basic Definitions
-/

/--
**Coloring:**
An r-coloring of a set A assigns each element a color from {0, 1, ..., r-1}.
-/
def Coloring (A : Set ℕ) (r : ℕ) := { a : ℕ // a ∈ A } → Fin r

/--
**Monochromatic subset:**
A subset S ⊆ A is monochromatic under coloring c if all elements have the same color.
-/
def IsMonochromatic {A : Set ℕ} (c : Coloring A r) (S : Finset { a : ℕ // a ∈ A }) : Prop :=
  ∃ color : Fin r, ∀ x ∈ S, c x = color

/--
**Sum of a finset:**
The sum of elements in a finset of naturals.
-/
def finsetSum (S : Finset ℕ) : ℕ := S.sum id

/--
**Distinct sum representation:**
n can be written as a sum of distinct elements from a finset.
-/
def HasDistinctSumRep (n : ℕ) (available : Set ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ available) ∧ S.sum id = n

/-
## Part II: Ramsey r-Completeness
-/

/--
**Ramsey r-complete:**
A set A is Ramsey r-complete if for every r-coloring of A, there exists N such that
every n ≥ N can be written as a monochromatic sum of distinct elements from A.
-/
def IsRamseyComplete (A : Set ℕ) (r : ℕ) : Prop :=
  ∀ c : Coloring A r, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    ∃ color : Fin r, HasDistinctSumRep n { a | a ∈ A ∧ ∃ h : a ∈ A, c ⟨a, h⟩ = color }

/--
**The set of perfect squares:**
{1, 4, 9, 16, 25, ...}
-/
def Squares : Set ℕ := { n : ℕ | ∃ k : ℕ, k ≥ 1 ∧ n = k^2 }

/--
**The set of k-th powers:**
{1^k, 2^k, 3^k, ...}
-/
def KthPowers (k : ℕ) : Set ℕ := { n : ℕ | ∃ m : ℕ, m ≥ 1 ∧ n = m^k }

/--
**Squares are 2-coloring specific:**
The original question specifically asks about 2-colorings of squares.
-/
def SquaresRamsey2Complete : Prop := IsRamseyComplete Squares 2

/-
## Part III: The Original Conjecture
-/

/--
**Original Question (Burr-Erdős):**
Are the squares Ramsey 2-complete?

Equivalently: In any 2-coloring of {1, 4, 9, 16, ...}, can every sufficiently
large natural number be written as a monochromatic sum of distinct squares?
-/
def OriginalQuestion : Prop := SquaresRamsey2Complete

/--
**Generalized Question:**
For k ≥ 2, are the k-th powers Ramsey r-complete for all r ≥ 2?
-/
def GeneralizedQuestion : Prop :=
  ∀ k r : ℕ, k ≥ 2 → r ≥ 2 → IsRamseyComplete (KthPowers k) r

/-
## Part IV: Historical Results
-/

/--
**Burr's unpublished result (reported by Erdős 1995):**
Burr proved that k-th powers are Ramsey r-complete for all r, k ≥ 2.
This result was never published.
-/
/--
**Conlon-Fox-Pham (2021) - Main Result:**
For every r, k ≥ 2, the set of k-th powers contains a SPARSE Ramsey r-complete
subsequence.

"Sparse" means the counting function satisfies |A ∩ {1,...,N}| ≪ r(log N)².
This is optimal up to constants.
-/
axiom conlon_fox_pham_2021 :
  ∀ k r : ℕ, k ≥ 2 → r ≥ 2 →
    ∃ A : Set ℕ, A ⊆ KthPowers k ∧ IsRamseyComplete A r

/--
**The sparse subsequence result implies the full set is Ramsey complete:**
If A ⊆ B and A is Ramsey r-complete, then B is Ramsey r-complete.
-/
axiom subset_ramsey_complete {A B : Set ℕ} (hAB : A ⊆ B) (hA : IsRamseyComplete A r) :
    IsRamseyComplete B r

/--
**Corollary: k-th powers are Ramsey r-complete:**
Follows immediately from Conlon-Fox-Pham's sparse subsequence result.
-/
theorem kth_powers_ramsey_complete (k r : ℕ) (hk : k ≥ 2) (hr : r ≥ 2) :
    IsRamseyComplete (KthPowers k) r := by
  obtain ⟨A, hAsub, hAcomplete⟩ := conlon_fox_pham_2021 k r hk hr
  exact subset_ramsey_complete hAsub hAcomplete

/-
## Part V: Resolution of Problem 843
-/

/--
**The answer to Erdős Problem #843 is YES:**
The squares are Ramsey 2-complete.
-/
theorem squares_ramsey_2_complete : SquaresRamsey2Complete := by
  -- Squares = KthPowers 2
  have h : Squares = KthPowers 2 := by
    ext n
    simp only [Squares, KthPowers, Set.mem_setOf_eq]
  rw [SquaresRamsey2Complete, h]
  exact kth_powers_ramsey_complete 2 2 (by norm_num) (by norm_num)

/--
**Erdős Problem #843 RESOLVED:**
The answer is YES - squares are Ramsey 2-complete.
-/
theorem erdos_843_resolved : OriginalQuestion := squares_ramsey_2_complete

/-
## Part VI: Stronger Results
-/

/--
**Density bounds for sparse Ramsey complete sequences:**

Conlon-Fox-Pham proved:
- Upper bound: There exists r-Ramsey complete A with |A ∩ [1,N]| ≪ r(log N)²
- Lower bound: Any r-Ramsey complete A satisfies |A ∩ [1,N]| ≫ (log N)²

So (log N)² is the threshold for Ramsey completeness.
-/
/--
**Burr-Erdős upper bound (1985):**
There exists a Ramsey 2-complete sequence A with |A ∩ [1,N]| ≪ (log N)³.
-/
/-
## Part VII: Related Results and Context

**CFP improved the upper bound to (log N)²** — this is optimal up to constants.

**Related Problems:**
- Problem 54: Minimum density of Ramsey complete sequences
- Problem 55: Subset sums and completeness
- Erdős offered a combined $350 for three Ramsey completeness problems

**Intuition: Why squares are Ramsey 2-complete:**
1. Squares grow quadratically, so they're not too sparse
2. Every large integer has many representations as sums of squares
   (by Lagrange's Four Squares Theorem and variants)
3. In any 2-coloring, one color class must contain "enough" squares
4. The combinatorics of subset sums ensures coverage
-/

/--
**Four Squares Theorem (Lagrange):**
Every positive integer is a sum of four squares.
This is related but doesn't directly imply Ramsey completeness.
-/
theorem lagrange_four_squares :
    ∀ n : ℕ, n ≥ 1 → ∃ a b c d : ℕ, n = a^2 + b^2 + c^2 + d^2 := by
  intro n _
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  exact ⟨a, b, c, d, h.symm⟩

/-
## Part IX: Summary
-/

/--
**Summary of Erdős Problem #843:**

**Question:**
Are the squares Ramsey 2-complete?

**Answer:** YES (Burr unpublished; Conlon-Fox-Pham 2021)

**Stronger Result:**
For all r, k ≥ 2, the k-th powers contain a sparse Ramsey r-complete subsequence.
The sparsity bound (log N)² is optimal.

**Prize:** Part of combined $350 for Ramsey completeness problems

**Key Reference:**
Conlon, Fox, Pham: "Subset sums, completeness and colorings" (2021)
-/
theorem erdos_843_summary :
    SquaresRamsey2Complete ∧
    (∀ k r : ℕ, k ≥ 2 → r ≥ 2 → IsRamseyComplete (KthPowers k) r) :=
  ⟨squares_ramsey_2_complete, kth_powers_ramsey_complete⟩

end Erdos843
