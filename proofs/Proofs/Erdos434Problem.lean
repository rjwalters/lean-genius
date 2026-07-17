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

import Mathlib

namespace Erdos434

/- ## Part I: Representability -/

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

/- ## Part II: The Set of Non-Representable Integers -/

/-- The set of integers not representable by A. -/
def NonRepresentable (A : Set ℕ) : Set ℕ :=
  {n : ℕ | ¬IsRepresentableAs n A}

/-- The count of non-representable integers (may be infinite if gcd(A) > 1). -/
noncomputable def countNonRepresentable (A : Set ℕ) : ℕ∞ :=
  (NonRepresentable A).encard

/-- For finite counting, we use ncard (natural-valued cardinality). -/
noncomputable def nCardNonRepresentable (A : Set ℕ) : ℕ :=
  (NonRepresentable A).ncard

/- ## Part III: The Frobenius Number -/

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

/- ## Part IV: The Extremal Problem -/

/-- The "top k" set: {n-k+1, n-k+2, ..., n}. -/
def topK (n k : ℕ) : Set ℕ :=
  Set.Icc (n - k + 1) n

/-- The number of elements in topK(n, k) when k ≤ n. -/
theorem topK_card (n k : ℕ) (hk : k ≤ n) (hk_pos : k > 0) :
    (topK n k).ncard = k := by
  simp only [topK]
  rw [← Finset.coe_Icc, Set.ncard_coe_finset, Nat.card_Icc]
  omega

/-- The extremal Frobenius question: does topK maximize non-representables? -/
def ExtremalFrobeniusQuestion (n k : ℕ) : Prop :=
  ∀ A : Set ℕ, A ⊆ Set.Icc 1 n → A.ncard = k →
    nCardNonRepresentable A ≤ nCardNonRepresentable (topK n k)

/- ## Part V: Sylvester–Frobenius input (Chicken McNugget count)

    The classical Sylvester–Frobenius count for a coprime pair is used by the
    examples below; it is axiomatized (the "half" count `(a-1)(b-1)/2` is a
    genuine combinatorial theorem beyond the scope of this file). The finiteness
    that makes these counts well-defined is proved unconditionally in Part X. -/

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
  have h1 : n - 1 > 0 := by omega
  have h2 : n > 0 := by omega
  have hcop : Nat.Coprime (n - 1) n := by
    rw [Nat.coprime_self_sub_left (by omega : (1 : ℕ) ≤ n)]
    exact Nat.coprime_one_left n
  exact sylvester_count (n - 1) n h1 h2 hcop

/- ## Part VI: Small Examples -/

/-- Example: With A = {2, 3}, non-representables are {1}.
    - 0 = empty sum, 1 is NOT representable (all elements ≥ 2),
    - ≥ 2: use copies of 2 and 3 to reach any value. -/
theorem example_2_3 : NonRepresentable {2, 3} = {1} := by
  ext n
  simp only [NonRepresentable, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- ¬IsRepresentableAs n {2, 3} → n = 1
    intro hnr
    -- n ≠ 0 (0 is representable by empty multiset)
    have h0 : n ≠ 0 := fun h => hnr (h ▸ zero_representable _)
    by_contra hne
    apply hnr
    -- n ≥ 2 → representable
    have h2 : n ≥ 2 := by omega
    -- Strong induction: if n ≥ 2, then either n = 2, n = 3, or n ≥ 4
    -- n = 2: {2}, n = 3: {3}, n ≥ 4: n - 2 ≥ 2 and is representable (IH)
    suffices ∀ m, m ≥ 2 → IsRepresentableAs m ({2, 3} : Set ℕ) from this n h2
    intro m
    induction m using Nat.strong_induction_on with | _ m ih => ?_
    intro hm
    rcases Nat.lt_or_ge m 4 with hlt | hge
    · -- m ∈ {2, 3}
      interval_cases m <;> simp_all
      · exact mem_representable (by simp : (2 : ℕ) ∈ ({2, 3} : Set ℕ))
      · exact mem_representable (by simp : (3 : ℕ) ∈ ({2, 3} : Set ℕ))
    · -- m ≥ 4: m = 2 + (m - 2), and m - 2 ≥ 2
      have : m = 2 + (m - 2) := by omega
      rw [this]
      exact add_representable
        (mem_representable (by simp : (2 : ℕ) ∈ ({2, 3} : Set ℕ)))
        (ih (m - 2) (by omega) (by omega))
  · -- n = 1 → ¬IsRepresentableAs 1 {2, 3}
    intro h; subst h
    intro ⟨S, hS_sub, hS_sum⟩
    -- S is a multiset over {2, 3} with sum 1.
    -- If empty: sum = 0 ≠ 1. If nonempty: every element ≥ 2, so sum ≥ 2 > 1.
    rcases Multiset.empty_or_exists_mem S with hempty | ⟨a, ha⟩
    · simp [hempty] at hS_sum
    · have : a ∈ ({2, 3} : Set ℕ) := hS_sub a ha
      have hage : a ≥ 2 := by simp at this; omega
      have : S.sum ≥ a := Multiset.single_le_sum (fun x hx => by
        have := hS_sub x hx; simp at this; omega) a ha
      omega

/-- Example: With A = {3, 5}, the Frobenius number is 7.
    By Sylvester: 3 * 5 - 3 - 5 = 7. -/
theorem example_3_5_frobenius : frobeniusNumber {3, 5} = 7 := by
  have := sylvester_frobenius 3 5 (by omega) (by omega) (by decide : Nat.Coprime 3 5)
  norm_num at this; exact this

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

/- ## Part VII: Kiss's Theorem (2002) -/

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

/- ## Part VIII: Why topK is Optimal

    Intuition: Using larger numbers means fewer representations.

    If A contains small numbers, more integers can be built from them.
    Using only large numbers {n-k+1, ..., n} creates "gaps" in what's
    representable, maximizing non-representables.

    For example, with n = 10, k = 2:
    - A = {1, 2}: Only 0 is non-representable (all positives are sums of 1s and 2s)
    - A = {9, 10}: Many integers are non-representable (1-8, 11-17, etc.) -/

/-- Using larger numbers creates more non-representable integers.
    Requires n ≥ 3 since at n = 2, both sides equal 0.
    By Sylvester: |NR{n-1,n}| = (n-2)(n-1)/2, |NR{1,2}| = 0. -/
theorem larger_numbers_fewer_reps (n : ℕ) (hn : n ≥ 3) :
    nCardNonRepresentable ({n - 1, n} : Set ℕ) >
    nCardNonRepresentable ({1, 2} : Set ℕ) := by
  -- RHS: nCardNonRepresentable {1, 2} = (1-1)*(2-1)/2 = 0
  have h12 : nCardNonRepresentable ({1, 2} : Set ℕ) = 0 := by
    have hcop : Nat.Coprime 1 2 := by decide
    have := sylvester_count 1 2 (by omega) (by omega) hcop
    simp at this; exact this
  rw [h12]
  -- LHS: nCardNonRepresentable {n-1, n} = (n-2)*(n-1)/2 > 0
  rw [consecutive_count n (by omega)]
  -- (n - 2) * (n - 1) / 2 > 0 for n ≥ 3
  have ha : 1 ≤ n - 2 := by omega
  have hb : 2 ≤ n - 1 := by omega
  have h1 : (n - 2) * (n - 1) ≥ 2 :=
    calc (2 : ℕ) = 1 * 2 := by norm_num
      _ ≤ (n - 2) * (n - 1) := Nat.mul_le_mul ha hb
  omega

/- ## Part IX: The Greedy Construction -/

/-- The greedy approach: always pick the largest available number.
    This produces topK and maximizes non-representables.

    Intuition: Each step adds a number that enables the fewest new
    representations. Large numbers have longer "gaps" before
    multiples fill in the representable set. -/
def greedyConstruct (n k : ℕ) : Set ℕ :=
  Set.Icc (n - k + 1) n

/-- The greedy construction equals topK. -/
theorem greedy_eq_topK (n k : ℕ) : greedyConstruct n k = topK n k := rfl

/- ## Part X: Finiteness of the Non-Representable Set (Chicken McNugget)

    When `A` contains a coprime pair `a, b`, every integer `≥ a·b` is a
    non-negative combination `x·a + y·b` (the Chicken McNugget theorem), so the
    non-representable integers all lie in `Set.Iio (a·b)`, a finite set. Mathlib
    has no numerical-semigroup API, so the combination is built directly from
    `ZMod` unit arithmetic. -/

/-- If `1 ∈ A` then every natural number is representable (as a sum of `n`
    copies of `1`). -/
theorem representable_of_one_mem {A : Set ℕ} (h1 : 1 ∈ A) (n : ℕ) :
    IsRepresentableAs n A :=
  ⟨Multiset.replicate n 1,
    fun a ha => by rw [Multiset.eq_of_mem_replicate ha]; exact h1,
    by rw [Multiset.sum_replicate, smul_eq_mul, mul_one]⟩

/-- **Chicken McNugget theorem (existence form).** For coprime positive `a, b`,
    every `n ≥ a * b` can be written as a non-negative integer combination
    `x * a + y * b`. -/
theorem exists_nat_combo_of_ge {a b : ℕ} (hapos : 0 < a) (hbpos : 0 < b)
    (hcop : Nat.Coprime a b) {n : ℕ} (hn : a * b ≤ n) :
    ∃ x y : ℕ, n = x * a + y * b := by
  haveI : NeZero b := ⟨hbpos.ne'⟩
  -- `a` is a unit mod `b`, so `a * x ≡ n (mod b)` is solvable with `x < b`.
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime a b).mpr hcop
  set x : ℕ := (((u⁻¹ : (ZMod b)ˣ) : ZMod b) * (n : ZMod b)).val with hxdef
  have hxlt : x < b := by rw [hxdef]; exact ZMod.val_lt _
  have hcast : (a : ZMod b) * (x : ZMod b) = (n : ZMod b) := by
    rw [hxdef, ZMod.natCast_zmod_val, ← hu, ← mul_assoc, Units.mul_inv, one_mul]
  -- `x * a ≤ n`, so `n - x * a` is a genuine natural number.
  have hxa : x * a ≤ n := by
    calc x * a ≤ (b - 1) * a := by gcongr <;> omega
      _ ≤ b * a := by gcongr <;> omega
      _ = a * b := by ring
      _ ≤ n := hn
  -- `b ∣ (n - x * a)` from the congruence `a * x ≡ n (mod b)`.
  have hdvd : b ∣ (n - x * a) := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hxa]
    push_cast
    rw [mul_comm (x : ZMod b) (a : ZMod b), hcast, sub_self]
  obtain ⟨y, hy⟩ := hdvd
  rw [Nat.mul_comm b y] at hy
  exact ⟨x, y, by omega⟩

/-- Any `n ≥ a * b` is representable by `A`, provided `A` contains a coprime
    positive pair `a, b`. -/
theorem representable_of_ge_of_mem {A : Set ℕ} {a b : ℕ}
    (ha : a ∈ A) (hb : b ∈ A) (hapos : 0 < a) (hbpos : 0 < b)
    (hcop : Nat.Coprime a b) {n : ℕ} (hn : a * b ≤ n) :
    IsRepresentableAs n A := by
  obtain ⟨x, y, hxy⟩ := exists_nat_combo_of_ge hapos hbpos hcop hn
  refine ⟨Multiset.replicate x a + Multiset.replicate y b, ?_, ?_⟩
  · intro z hz
    rcases Multiset.mem_add.mp hz with h | h
    · rw [Multiset.eq_of_mem_replicate h]; exact ha
    · rw [Multiset.eq_of_mem_replicate h]; exact hb
  · rw [Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_replicate,
        smul_eq_mul, smul_eq_mul]
    omega

/-- If `1 ∈ A`, the non-representable set is empty, hence finite. -/
theorem nonrep_finite_of_one_mem {A : Set ℕ} (h1 : 1 ∈ A) :
    (NonRepresentable A).Finite := by
  have hempty : NonRepresentable A = ∅ := by
    ext m
    simp only [NonRepresentable, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false, not_not]
    exact representable_of_one_mem h1 m
  rw [hempty]; exact Set.finite_empty

/-- Upper bound: With a coprime pair in A, non-representables are finite.
    Every integer `≥ a * b` is representable, so the non-representable set is
    contained in `Set.Iio (a * b)`. A coprime pair involving `0` forces
    `1 ∈ A`, the degenerate case. -/
theorem nonrep_finite {A : Set ℕ} (hA : A.Nonempty)
    (hcop : ∃ a ∈ A, ∃ b ∈ A, Nat.Coprime a b) :
    (NonRepresentable A).Finite := by
  obtain ⟨a, ha, b, hb, hcop⟩ := hcop
  rcases Nat.eq_zero_or_pos a with rfl | hapos
  · rw [(Nat.coprime_zero_left b).mp hcop] at hb
    exact nonrep_finite_of_one_mem hb
  rcases Nat.eq_zero_or_pos b with rfl | hbpos
  · rw [(Nat.coprime_zero_right a).mp hcop] at ha
    exact nonrep_finite_of_one_mem ha
  refine Set.Finite.subset (Set.finite_Iio (a * b)) ?_
  intro m hm
  simp only [Set.mem_Iio]
  by_contra h
  push_neg at h
  exact hm (representable_of_ge_of_mem ha hb hapos hbpos hcop h)

/-- For topK(n, k) with k ≥ 2, the non-representable count is finite
    since the block `{n-k+1, …, n}` contains the coprime consecutive pair
    `n-1, n`. -/
theorem topK_finite (n k : ℕ) (hk : k ≥ 2) (hn : n ≥ k) :
    (NonRepresentable (topK n k)).Finite := by
  refine nonrep_finite ⟨n, by simp only [topK, Set.mem_Icc]; omega⟩
    ⟨n - 1, ?_, n, ?_, ?_⟩
  · simp only [topK, Set.mem_Icc]; omega
  · simp only [topK, Set.mem_Icc]; omega
  · rw [Nat.coprime_self_sub_left (by omega : (1 : ℕ) ≤ n)]
    exact Nat.coprime_one_left n

/- ## Part XI: Comparison with Problem #433 -/

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

/- ## Part XII: Main Result -/

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
      {m | ∃ A : Set ℕ, (A ⊆ Set.Icc 1 n ∧ A.ncard = k) ∧ nCardNonRepresentable A = m}
      (nCardNonRepresentable (topK n k)) := by
  constructor
  · -- topK n k is in the set
    refine ⟨topK n k, ⟨?_, ?_⟩, rfl⟩
    · intro x hx; simp only [topK, Set.mem_Icc] at hx ⊢; omega
    · exact topK_card n k hkn (by omega)
  · -- Upper bound from Kiss's theorem
    rintro m ⟨A, ⟨hAsub, hAcard⟩, rfl⟩
    exact erdos_434_complete n k hn hk hkn A hAsub hAcard

end Erdos434

/-
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
8. Finiteness of the non-representable set (Chicken McNugget, proved)
9. Relation to Problem #433

**Key insight**: Using larger numbers creates more gaps in representations.
The greedy approach of always picking the largest available number maximizes
the count of non-representable integers.

**Historical Note**: This problem connects to the classical Frobenius
(coin) problem: what is the largest amount that cannot be made with
coins of given denominations? Problem #434 asks not for the largest,
but for how to maximize the COUNT of unreachable amounts.
-/
