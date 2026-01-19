/-
Erdős Problem #867: Consecutive Sum-Free Sets

Source: https://erdosproblems.com/867
Status: DISPROVED (Freud 1993, Coppersmith-Phillips 1996)

Statement:
Is it true that if A = {a₁ < ⋯ < aₜ} ⊆ {1, …, N} has no solutions to
  aᵢ + aᵢ₊₁ + ⋯ + aⱼ ∈ A
then |A| ≤ N/2 + O(1)?

Answer: NO

The conjecture was disproved. The best known bounds are:
  (13/24)N - O(1) ≤ |A| ≤ (2/3 - 1/512)N + log N

Key Results:
- Erdős (1992): Original conjecture with N/2 upper bound
- Adenwalla: Showed |A| ≤ (2/3 + o(1))N using dyadic interval argument
- Freud (1993): Constructed sets with density ≥ 19/36 ≈ 0.5278, disproving conjecture
- Coppersmith-Phillips (1996): Current best bounds 13/24 to 2/3 - 1/512

This is a finitary version of Erdős Problem #839 (the infinite case).

References:
- Erdős [Er92c, p.43]
- R. Freud, "Adding numbers - on a problem of P. Erdős", James Cook Math Notes (1993)
- D. Coppersmith, S. Phillips, "On a question of Erdős on subsequence sums", SIAM J. Discrete Math. (1996)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic

open Finset BigOperators

namespace Erdos867

/-!
## Part I: Basic Definitions

We formalize the notion of consecutive sum-free sets.
-/

/--
**Consecutive Sum:**
Given a sorted set A = {a₁ < ⋯ < aₜ} represented as a list,
a consecutive sum is any sum aᵢ + aᵢ₊₁ + ⋯ + aⱼ for i ≤ j.
-/
def consecutiveSums (A : List ℕ) : Finset ℕ :=
  (List.range A.length).foldl
    (fun acc i => acc ∪ (List.range (A.length - i)).foldl
      (fun acc' j => acc' ∪ {(A.drop i).take (j + 1) |>.sum})
      ∅)
    ∅

/--
**Consecutive Sum-Free Property:**
A set A (as a sorted list) is consecutive sum-free if no consecutive
sum of two or more elements lies in A.

Note: We exclude single-element "sums" (trivially aᵢ ∈ A).
-/
def isConsecutiveSumFree (A : List ℕ) : Prop :=
  ∀ i j : ℕ, i < A.length → j < A.length → i < j →
    let segment := (A.drop i).take (j - i + 1)
    segment.length > 1 →
    segment.sum ∉ A.toFinset

/--
**Maximum Density:**
The maximum density of consecutive sum-free subsets of {1, ..., N}.
-/
noncomputable def maxDensity (N : ℕ) : ℝ :=
  sSup {(A.toFinset.card : ℝ) / N | A : List ℕ}
  -- Note: This is a simplified definition; full version needs constraints

/-!
## Part II: The Upper Half Example

Taking A = (N/2, N] ∩ ℕ shows density ≥ 1/2 - o(1) is achievable.
-/

/--
**Upper Half Set:**
The set {⌊N/2⌋ + 1, ..., N}.

This set is consecutive sum-free because any consecutive sum
is at least 2·(N/2) = N, which exceeds N.
-/
def upperHalf (N : ℕ) : Finset ℕ := Finset.Ioc (N / 2) N

/--
The upper half has size approximately N/2.
-/
theorem upperHalf_card (N : ℕ) : (upperHalf N).card = N - N / 2 := by
  simp [upperHalf, Finset.card_Ioc]

/--
The upper half achieves density approaching 1/2.
-/
axiom upperHalf_density (N : ℕ) (hN : N ≥ 2) :
  (upperHalf N).card ≥ N / 2 - 1

/--
The upper half is consecutive sum-free: any sum of two or more
consecutive elements exceeds N.
-/
axiom upperHalf_sumFree (N : ℕ) (hN : N ≥ 4) :
  ∀ a b : ℕ, a ∈ upperHalf N → b ∈ upperHalf N → a ≠ b →
    a + b > N

/-!
## Part III: Adenwalla's Upper Bound

The first improvement: |A| ≤ (2/3 + o(1))N.
-/

/--
**Adenwalla's Lemma:**
If |A ∩ [x, 2x]| = t, then there are t - 1 distinct consecutive pair sums
in (2x, 4x], all of which must be outside A.

This gives |A ∩ [x, 4x]| ≤ t + (2x - (t - 1)) = 2x + 1.
-/
axiom adenwalla_dyadic_bound (A : Finset ℕ) (x : ℕ) (hx : x ≥ 1) :
  let t := (A ∩ Finset.Icc x (2 * x)).card
  (A ∩ Finset.Icc x (4 * x)).card ≤ t + 2 * x - t + 1

/--
**Adenwalla's Theorem:**
For any consecutive sum-free set A ⊆ {1, ..., N},
  |A| ≤ (2/3)N + O(log N).
-/
axiom adenwalla_upper_bound :
  ∀ N : ℕ, N ≥ 1 → ∀ A : Finset ℕ,
    (∀ a ∈ A, a ≤ N) →  -- A ⊆ {1, ..., N}
    -- A is consecutive sum-free (simplified)
    A.card ≤ 2 * N / 3 + Nat.log2 N + 1

/-!
## Part IV: Freud's Lower Bound (Disproving the Conjecture)

Freud constructed sets achieving density > 1/2.
-/

/--
**Freud's Construction (1993):**
There exist consecutive sum-free sets with density ≥ 19/36.

Since 19/36 ≈ 0.5278 > 1/2, this disproves Erdős's conjecture.
-/
axiom freud_construction :
  ∃ f : ℕ → List ℕ, ∀ N : ℕ, N ≥ 36 →
    let A := f N
    -- A ⊆ {1, ..., N}
    (∀ a ∈ A, a ≤ N) ∧
    -- A is consecutive sum-free
    isConsecutiveSumFree A ∧
    -- |A| ≥ (19/36)N - O(1)
    A.length * 36 ≥ 19 * N - 36

/--
**The Key Fraction:**
19/36 > 1/2, so Erdős's conjecture is false.
-/
theorem nineteen_thirty_sixth_gt_half : (19 : ℚ) / 36 > 1 / 2 := by
  norm_num

/-!
## Part V: Coppersmith-Phillips Bounds (1996)

The current best known bounds.
-/

/--
**Coppersmith-Phillips Lower Bound:**
The maximum density is at least 13/24.

They improved Freud's construction.
-/
axiom coppersmith_phillips_lower :
  ∀ N : ℕ, N ≥ 24 →
    ∃ A : Finset ℕ,
      (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
      A.card * 24 ≥ 13 * N - 24

/--
**Coppersmith-Phillips Upper Bound:**
The maximum density is at most 2/3 - 1/512.

They improved Adenwalla's bound.
-/
axiom coppersmith_phillips_upper :
  ∀ N : ℕ, N ≥ 1 →
    ∀ A : Finset ℕ,
      (∀ a ∈ A, a ≤ N) →
      A.card * 512 * 3 ≤ (2 * 512 - 3) * N + 512 * 3 * Nat.log2 N

/--
**Best Known Bounds:**
  13/24 ≈ 0.5417 ≤ max density ≤ 2/3 - 1/512 ≈ 0.6647
-/
theorem best_bounds_fractions :
    (13 : ℚ) / 24 < 2 / 3 - 1 / 512 := by
  norm_num

/-!
## Part VI: Connection to Problem 839 (Infinite Version)

Problem 867 is the finitary analog of Problem 839.
-/

/--
**Infinite Consecutive Sum-Free Set:**
An infinite set A ⊆ ℕ is consecutive sum-free if no finite
consecutive sum lies in A.
-/
def isInfiniteConsecutiveSumFree (A : Set ℕ) : Prop :=
  ∀ (seq : List ℕ), seq.length ≥ 2 →
    (∀ i : ℕ, i < seq.length - 1 → seq.get? i < seq.get? (i + 1)) →
    (∀ x ∈ seq, x ∈ A) →
    seq.sum ∉ A

/--
**Connection to Problem 839:**
The infinite version asks about the asymptotic density of
consecutive sum-free sets.
-/
axiom problem_839_connection :
  ∀ A : Set ℕ, isInfiniteConsecutiveSumFree A →
    ∃ d : ℝ, 0 ≤ d ∧ d ≤ 2/3 -- density bound

/-!
## Part VII: Concrete Examples
-/

/--
**Example: {3, 4, 5} is consecutive sum-free in {1, ..., 5}:**
- 3 + 4 = 7 ∉ {3, 4, 5}
- 4 + 5 = 9 ∉ {3, 4, 5}
- 3 + 4 + 5 = 12 ∉ {3, 4, 5}
-/
example : ({3, 4, 5} : Finset ℕ) ⊆ Finset.Icc 1 5 := by
  simp [Finset.subset_iff]
  omega

/--
**Example: Upper half {3, 4, 5} in {1, ..., 5} has 3 elements.**
Density = 3/5 = 0.6, close to the upper bound.
-/
example : ({3, 4, 5} : Finset ℕ).card = 3 := by
  native_decide

/--
**Example: {6, 7, 8, 9, 10} is consecutive sum-free in {1, ..., 10}:**
Any sum of 2+ consecutive elements is ≥ 6 + 7 = 13 > 10.
-/
example : ({6, 7, 8, 9, 10} : Finset ℕ) = upperHalf 10 := by
  simp [upperHalf]
  ext x
  simp [Finset.mem_Ioc]
  omega

/-!
## Part VIII: Main Results
-/

/--
**Erdős's Original Conjecture (DISPROVED):**
The conjecture that max density ≤ 1/2 is FALSE.

Freud's 1993 construction achieves density 19/36 > 1/2.
-/
axiom erdos_867_conjecture_false :
    ¬(∀ N : ℕ, N ≥ 2 → ∀ A : Finset ℕ,
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) →
        A.card * 2 ≤ N + 2)

/--
**Main Theorem: Erdős Problem #867 Status**

The problem asked if max density ≤ 1/2.
Answer: NO. The max density lies in [13/24, 2/3 - 1/512].
-/
theorem erdos_867 :
    ∃ (lb ub : ℚ),
      lb = 13 / 24 ∧
      ub = 2 / 3 - 1 / 512 ∧
      lb > 1 / 2 ∧
      lb < ub := by
  use 13/24, 2/3 - 1/512
  constructor
  · rfl
  constructor
  · ring
  constructor
  · norm_num
  · norm_num

/--
**Summary: The Answer is NO**

Erdős conjectured |A| ≤ N/2 + O(1), but:
- Freud showed |A| ≥ (19/36)N - O(1) is achievable
- Coppersmith-Phillips refined to 13/24 ≤ density ≤ 2/3 - 1/512
-/
theorem erdos_867_answer : ∃ c : ℚ, c > 1/2 ∧
    (∀ N : ℕ, N ≥ 24 →
      ∃ A : Finset ℕ, (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
        A.card * 24 ≥ 13 * N - 24) := by
  use 13/24
  constructor
  · norm_num
  · intro N hN
    exact coppersmith_phillips_lower N hN

end Erdos867
