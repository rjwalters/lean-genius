/-
  Erdős Problem #434: Extremal Frobenius Problem

  Source: https://erdosproblems.com/434
  Status: SOLVED (Kiss 2002)

  Statement:
  Let k ≤ n. What choice of A ⊆ {1, ..., n} of size |A| = k maximizes the
  number of integers not representable as the sum of finitely many elements
  from A (with repetitions allowed)? Is it {n, n-1, ..., n-k+1}?

  Answer: YES
  The maximal choice is indeed {n, n-1, ..., n-k+1}, as proved by Kiss (2002).

  Historical Context:
  This problem is closely related to the Frobenius problem (also called the
  coin problem or money changing problem). Given a set of positive integers
  with gcd = 1, only finitely many integers are non-representable. The largest
  such integer is the Frobenius number. Problem #434 asks not for the largest,
  but for which set maximizes the COUNT of non-representables.

  Related: Problem #433 (Frobenius numbers for consecutive integers)

  References:
  [Ki02] Kiss, G., "On the extremal Frobenius problem in a new aspect"
         Ann. Univ. Sci. Budapest. Eötvös Sect. Math. (2002), 139-142.

  Tags: number-theory, combinatorics, frobenius-problem
-/

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Tactic

namespace Erdos434

/-! ## Part I: Representability -/

/-- A natural number n is representable by a set A if it can be written as the
    sum of finitely many elements of A (with repetition allowed).

    For example, with A = {3, 5}:
    - 6 is representable (3 + 3)
    - 8 is representable (3 + 5)
    - 7 is NOT representable

    This uses multisets to allow repetition. -/
def IsRepresentableAs (n : ℕ) (A : Set ℕ) : Prop :=
  ∃ (S : Multiset ℕ), (∀ a ∈ S, a ∈ A) ∧ S.sum = n

/-- Zero is always representable (by the empty multiset). -/
theorem zero_representable (A : Set ℕ) : IsRepresentableAs 0 A := by
  use ∅
  simp

/-- Any element of A is representable. -/
theorem mem_representable {a : ℕ} {A : Set ℕ} (ha : a ∈ A) : IsRepresentableAs a A := by
  use {a}
  simp [ha]

/-- If m and n are representable, so is m + n. -/
theorem add_representable {m n : ℕ} {A : Set ℕ}
    (hm : IsRepresentableAs m A) (hn : IsRepresentableAs n A) :
    IsRepresentableAs (m + n) A := by
  obtain ⟨Sm, hSm_sub, hSm_sum⟩ := hm
  obtain ⟨Sn, hSn_sub, hSn_sum⟩ := hn
  use Sm + Sn
  constructor
  · intro a ha
    simp at ha
    cases ha with
    | inl h => exact hSm_sub a h
    | inr h => exact hSn_sub a h
  · simp [hSm_sum, hSn_sum]

/-! ## Part II: The Set of Non-Representable Integers -/

/-- The set of integers not representable by A. -/
def NonRepresentable (A : Set ℕ) : Set ℕ :=
  {n : ℕ | ¬IsRepresentableAs n A}

/-- The count of non-representable integers (may be infinite if gcd(A) > 1). -/
noncomputable def countNonRepresentable (A : Set ℕ) : ℕ∞ :=
  (NonRepresentable A).encard

/-- For finite counting, we use ncard (natural-valued cardinality). -/
noncomputable def nCardNonRepresentable (A : Set ℕ) : ℕ :=
  (NonRepresentable A).ncard

/-! ## Part III: The Frobenius Number -/

/-- The Frobenius number of A: the largest integer not representable by A.
    Only defined when gcd(A) = 1 (ensuring finitely many non-representables).
    Returns 0 if all integers ≥ some N are representable and 0 is the largest
    non-representable, or returns the actual largest. -/
noncomputable def frobeniusNumber (A : Set ℕ) : ℕ :=
  sSup (NonRepresentable A)

/-- A set is "complete" if gcd(A) = 1. Such sets have finitely many
    non-representable integers. -/
def IsComplete (A : Set ℕ) : Prop :=
  A.Nonempty ∧ Nat.gcd (sSup A) (sInf (A \ {sSup A})) = 1

/-! ## Part IV: The Extremal Problem -/

/-- The "top k" set: {n-k+1, n-k+2, ..., n}. -/
def topK (n k : ℕ) : Set ℕ :=
  Set.Icc (n - k + 1) n

/-- The number of elements in topK(n, k) when k ≤ n. -/
theorem topK_card (n k : ℕ) (hk : k ≤ n) (hk_pos : k > 0) :
    (topK n k).ncard = k := by
  sorry

/-- The extremal Frobenius question: does topK maximize non-representables? -/
def ExtremalFrobeniusQuestion (n k : ℕ) : Prop :=
  ∀ A : Set ℕ, A ⊆ Set.Icc 1 n → A.ncard = k →
    nCardNonRepresentable A ≤ nCardNonRepresentable (topK n k)

/-! ## Part V: Small Examples -/

/-- Example: With A = {2, 3}, non-representables are {1}.
    - 0 = empty sum
    - 1 is not representable
    - 2 = 2
    - 3 = 3
    - 4 = 2 + 2
    - 5 = 2 + 3
    - 6 = 3 + 3 = 2 + 2 + 2
    - All larger integers are representable -/
theorem example_2_3 : NonRepresentable {2, 3} = {1} := by
  sorry

/-- Example: With A = {3, 5}, non-representables are {1, 2, 4, 7}.
    The Frobenius number is 7 (largest non-representable). -/
theorem example_3_5_frobenius : frobeniusNumber {3, 5} = 7 := by
  sorry

/-- For topK(5, 2) = {4, 5}, we can compute non-representables.
    - 0 = empty
    - 1, 2, 3 not representable
    - 4 = 4
    - 5 = 5
    - 6, 7 not representable
    - 8 = 4 + 4
    - 9 = 4 + 5
    - 10 = 5 + 5
    - 11 not representable
    - 12 = 4 + 4 + 4
    - And so on... -/
theorem topK_5_2 : topK 5 2 = {4, 5} := by
  ext x
  simp [topK, Set.Icc]
  omega

/-! ## Part VI: Kiss's Theorem (2002) -/

/-- **Kiss (2002)**: The topK set maximizes the count of non-representables.

    For any k ≤ n with k ≥ 1, the set {n-k+1, ..., n} has the maximum
    number of non-representable integers among all k-element subsets
    of {1, ..., n}.

    This is axiomatized as it requires detailed analysis of the
    Frobenius problem for general sets. -/
axiom kiss_2002 (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ExtremalFrobeniusQuestion n k

/-- The answer to Erdős Problem #434 is YES. -/
theorem erdos_434_answer (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∀ A : Set ℕ, A ⊆ Set.Icc 1 n → A.ncard = k →
      nCardNonRepresentable A ≤ nCardNonRepresentable (topK n k) :=
  kiss_2002 n k hn hk hkn

/-! ## Part VII: Why topK is Optimal -/

/-- Intuition: Using larger numbers means fewer representations.

    If A contains small numbers, more integers can be built from them.
    Using only large numbers {n-k+1, ..., n} creates "gaps" in what's
    representable, maximizing non-representables.

    For example, with n = 10, k = 2:
    - A = {1, 2}: Only 0 is non-representable (all positives are sums of 1s and 2s)
    - A = {9, 10}: Many integers are non-representable (1-8, 11-17, etc.) -/
theorem larger_numbers_fewer_reps (n : ℕ) (hn : n ≥ 2) :
    nCardNonRepresentable ({n - 1, n} : Set ℕ) >
    nCardNonRepresentable ({1, 2} : Set ℕ) := by
  sorry

/-! ## Part VIII: Connection to Sylvester-Frobenius -/

/-- The Sylvester-Frobenius theorem: For coprime a, b, the Frobenius number
    is ab - a - b, and the count of non-representables is (a-1)(b-1)/2. -/
axiom sylvester_frobenius (a b : ℕ) (ha : a > 0) (hb : b > 0) (hcop : Nat.Coprime a b) :
    frobeniusNumber {a, b} = a * b - a - b

/-- The number of non-representables for coprime a, b. -/
axiom sylvester_count (a b : ℕ) (ha : a > 0) (hb : b > 0) (hcop : Nat.Coprime a b) :
    nCardNonRepresentable {a, b} = (a - 1) * (b - 1) / 2

/-- For consecutive integers n-1, n (always coprime), the count is
    (n-2)(n-1)/2. This grows quadratically with n. -/
theorem consecutive_count (n : ℕ) (hn : n ≥ 2) :
    nCardNonRepresentable ({n - 1, n} : Set ℕ) = (n - 2) * (n - 1) / 2 := by
  sorry

/-! ## Part IX: The Greedy Construction -/

/-- The greedy approach: always pick the largest available number.
    This produces topK and maximizes non-representables.

    Intuition: Each step adds a number that enables the fewest new
    representations. Large numbers have longer "gaps" before
    multiples fill in the representable set. -/
def greedyConstruct (n k : ℕ) : Set ℕ :=
  Set.Icc (n - k + 1) n

/-- The greedy construction equals topK. -/
theorem greedy_eq_topK (n k : ℕ) : greedyConstruct n k = topK n k := rfl

/-! ## Part X: Bounds on Non-Representables -/

/-- Upper bound: With gcd(A) = 1, non-representables are finite.
    The count is bounded by the Frobenius number. -/
theorem nonrep_finite {A : Set ℕ} (hA : A.Nonempty)
    (hcop : ∃ a b ∈ A, Nat.Coprime a b) :
    (NonRepresentable A).Finite := by
  sorry

/-- For topK(n, k) with k ≥ 2, the non-representable count is finite
    since gcd(n-k+1, n) = gcd(n-k+1, k-1) which is 1 for many choices. -/
theorem topK_finite (n k : ℕ) (hk : k ≥ 2) (hn : n ≥ k) :
    (NonRepresentable (topK n k)).Finite := by
  sorry

/-! ## Part XI: Comparison with Problem #433 -/

/-- Problem #433 asks about the Frobenius number for A = {n, n+1, ..., n+k-1}.
    Problem #434 asks which k-subset of {1, ..., n} maximizes non-representables.

    These are related but distinct:
    - #433: consecutive integers starting at n
    - #434: any k integers from {1, ..., n} -/
def problem433Set (n k : ℕ) : Set ℕ :=
  Set.Icc n (n + k - 1)

/-- The Frobenius number for consecutive integers {n, n+1, ..., n+k-1}
    was studied in Problem #433. -/
axiom frobenius_consecutive (n k : ℕ) (hn : n ≥ 2) (hk : k ≥ 2) :
    frobeniusNumber (problem433Set n k) = (n - 1) * (n + k - 1) / k - 1

/-! ## Part XII: Main Result -/

/-- The complete answer to Erdős Problem #434:

    YES, the choice A = {n-k+1, ..., n} maximizes the count of
    non-representable integers among all k-element subsets of {1, ..., n}.

    This was proved by Kiss (2002). -/
theorem erdos_434_complete :
    ∀ n k : ℕ, 1 ≤ n → 1 ≤ k → k ≤ n →
      ∀ A : Set ℕ, A ⊆ Set.Icc 1 n → A.ncard = k →
        nCardNonRepresentable A ≤ nCardNonRepresentable (topK n k) := by
  intro n k hn hk hkn A hAsub hAcard
  exact kiss_2002 n k hn hk hkn A hAsub hAcard

/-- Corollary: topK achieves the maximum. -/
theorem topK_is_maximum (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) :
    IsGreatest
      {nCardNonRepresentable A | A : Set ℕ // A ⊆ Set.Icc 1 n ∧ A.ncard = k}
      (nCardNonRepresentable (topK n k)) := by
  sorry

end Erdos434

/-!
## Summary

This file formalizes Erdős Problem #434 on the extremal Frobenius problem.

**Status**: SOLVED (Kiss 2002)

**The Problem**: Which k-element subset of {1, ..., n} maximizes the count
of integers not representable as sums of its elements (with repetition)?

**Answer**: The set {n-k+1, ..., n} (the "top k" largest elements)

**What we formalize**:
1. Representability via multisets
2. Non-representable integers and their count
3. The Frobenius number
4. The topK set construction
5. Small examples ({2,3}, {3,5})
6. Kiss's theorem (axiomatized)
7. Connection to Sylvester-Frobenius
8. Bounds on non-representables
9. Relation to Problem #433

**Key insight**: Using larger numbers creates more gaps in representations.
The greedy approach of always picking the largest available number maximizes
the count of non-representable integers.

**Historical Note**: This problem connects to the classical Frobenius
(coin) problem: what is the largest amount that cannot be made with
coins of given denominations? Problem #434 asks not for the largest,
but for how to maximize the COUNT of unreachable amounts.
-/
