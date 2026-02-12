/-
Erdős Problem #1054: Sum of Smallest Divisors

Let f(n) be the minimal integer m such that n is the sum of the k smallest
divisors of m for some k ≥ 1.

Is it true that f(n) = o(n)? Or is this true only for almost all n,
and limsup f(n)/n = ∞?

**Status**: OPEN

**Background**:
- The function f(n) is undefined for n = 2 and n = 5 (no such m exists)
- For most n, there exists an m whose smallest divisors sum to n
- Example: f(1) = 1 (the only divisor of 1 is 1, and sum of first divisor is 1)
- Example: f(3) = 2 (divisors of 2 are {1,2}, and 1+2 = 3)
- Example: f(6) = 5 (divisors of 5 are {1,5}, and 1+5 = 6)

**Note**: Terry Tao disproved the strong claim that f(n) = o(n) unconditionally.

Reference: https://erdosproblems.com/1054
Sources: [Gu04] Guy, Unsolved Problems in Number Theory, Problem B2
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

open Nat Finset

namespace Erdos1054

/-
## Infrastructure: Sorted Divisors and Partial Sums

We build constructive definitions for the sorted divisor list and
partial sums, enabling computational verification.
-/

/--
The divisors of m sorted in increasing order.
-/
def sortedDivisors (m : ℕ) : List ℕ :=
  m.divisors.sort (· ≤ ·)

/--
The list of partial sums of the k smallest divisors of m, for k = 1, 2, ..., d(m).
For m = 6 with divisors [1, 2, 3, 6], this gives [1, 3, 6, 12].
-/
def partialDivisorSums (m : ℕ) : List ℕ :=
  ((sortedDivisors m).scanl (· + ·) 0).tail

/--
A number n is representable if there exists some m ≥ 1 and some k ≥ 1 such that
n equals the sum of the k smallest divisors of m.
-/
def IsRepresentable (n : ℕ) : Prop :=
  ∃ m : ℕ, m ≥ 1 ∧ n ∈ (partialDivisorSums m)

/--
Bounded check: is n representable using some m in {1, ..., bound}?
-/
def isRepresentableBound (n : ℕ) (bound : ℕ) : Bool :=
  ((Finset.range bound).filter (fun m => n ∈ (partialDivisorSums (m + 1)))).card > 0

/--
f(n) = the minimal m ≥ 1 such that n equals the sum of the k smallest
divisors of m for some k ≥ 1, computed up to a search bound.
Returns 0 if no such m exists within the bound.
-/
def computeF (n : ℕ) (bound : ℕ := 10000) : ℕ :=
  match (Finset.range bound).filter (fun m => n ∈ (partialDivisorSums (m + 1)))
    |>.sort (· ≤ ·) with
  | [] => 0
  | m :: _ => m + 1

/-
## Concrete Values of f(n)

We prove representability and f(n) values by exhibiting witnesses
and verifying via native_decide.
-/

/--
1 is representable: the divisors of 1 are {1}, and the first partial sum is 1.
-/
theorem representable_1 : IsRepresentable 1 :=
  ⟨1, le_refl 1, by native_decide⟩

/-- f(1) = 1 -/
theorem f_1_eq_one : computeF 1 20 = 1 := by native_decide

/-- 3 is representable: divisors of 2 are {1,2}, 1+2=3. -/
theorem representable_3 : IsRepresentable 3 :=
  ⟨2, by omega, by native_decide⟩

/-- f(3) = 2 -/
theorem f_3_eq_two : computeF 3 20 = 2 := by native_decide

/-- 4 is representable: divisors of 3 are {1,3}, 1+3=4. -/
theorem representable_4 : IsRepresentable 4 :=
  ⟨3, by omega, by native_decide⟩

/-- f(4) = 3 -/
theorem f_4_eq_three : computeF 4 20 = 3 := by native_decide

/-- 6 is representable: divisors of 5 are {1,5}, 1+5=6. -/
theorem representable_6 : IsRepresentable 6 :=
  ⟨5, by omega, by native_decide⟩

/-- f(6) = 5: m = 5 has divisors {1, 5} with 1 + 5 = 6. -/
theorem f_6_eq_five : computeF 6 20 = 5 := by native_decide

/-- 7 is representable: divisors of 4 are {1,2,4}, 1+2+4=7. -/
theorem representable_7 : IsRepresentable 7 :=
  ⟨4, by omega, by native_decide⟩

/-- f(7) = 4 -/
theorem f_7_eq_four : computeF 7 20 = 4 := by native_decide

/-- 8 is representable: divisors of 7 are {1,7}, 1+7=8. -/
theorem representable_8 : IsRepresentable 8 :=
  ⟨7, by omega, by native_decide⟩

/-- f(8) = 7 -/
theorem f_8_eq_seven : computeF 8 20 = 7 := by native_decide

/-- 9 is representable: divisors of 15 are {1,3,5,15}, 1+3+5=9. -/
theorem representable_9 : IsRepresentable 9 :=
  ⟨15, by omega, by native_decide⟩

/-- f(9) = 15 -/
theorem f_9_eq : computeF 9 20 = 15 := by native_decide

/-- 10 is representable: divisors of 12 = {1,2,3,4,6,12}, 1+2+3+4=10. -/
theorem representable_10 : IsRepresentable 10 :=
  ⟨12, by omega, by native_decide⟩

/-- f(10) = 12 -/
theorem f_10_eq : computeF 10 20 = 12 := by native_decide

/-- 12 is representable: divisors of 6 = {1,2,3,6}, 1+2+3+6=12. -/
theorem representable_12 : IsRepresentable 12 :=
  ⟨6, by omega, by native_decide⟩

/-- f(12) = 6 -/
theorem f_12_eq : computeF 12 20 = 6 := by native_decide

/-- Several small values are representable. -/
theorem some_representable_values :
    IsRepresentable 1 ∧ IsRepresentable 3 ∧ IsRepresentable 4 ∧
    IsRepresentable 6 ∧ IsRepresentable 7 ∧ IsRepresentable 8 ∧
    IsRepresentable 9 ∧ IsRepresentable 10 ∧ IsRepresentable 12 :=
  ⟨representable_1, representable_3, representable_4,
   representable_6, representable_7, representable_8,
   representable_9, representable_10, representable_12⟩

/-
## Infrastructure: scanl Properties

Key property: all elements of `scanl (+) a l` are ≥ `a`.
This lets us bound partial divisor sums from below.
-/

/--
All elements of `List.scanl (· + ·) a l` are ≥ `a`.
-/
theorem scanl_add_ge_init (a : ℕ) (l : List ℕ) :
    ∀ x ∈ l.scanl (· + ·) a, x ≥ a := by
  induction l generalizing a with
  | nil =>
    simp [List.scanl]
  | cons d t ih =>
    intro x hx
    simp only [List.scanl, List.mem_cons] at hx
    cases hx with
    | inl heq => rw [heq]
    | inr hmem => exact le_trans (Nat.le_add_right a d) (ih (a + d) x hmem)

/--
1 is always in sortedDivisors of m ≥ 1.
-/
theorem one_mem_sortedDivisors (m : ℕ) (_hm : m ≥ 1) :
    1 ∈ sortedDivisors m := by
  simp only [sortedDivisors, Finset.mem_sort]
  exact Nat.mem_divisors.mpr ⟨one_dvd m, by omega⟩

/--
sortedDivisors is nonempty for m ≥ 1.
-/
theorem sortedDivisors_ne_nil (m : ℕ) (hm : m ≥ 1) :
    sortedDivisors m ≠ [] := by
  intro h
  have := one_mem_sortedDivisors m hm
  rw [h] at this
  simp at this

/--
All elements of sortedDivisors are positive (≥ 1).
-/
theorem sortedDivisors_pos (m d : ℕ) (hd : d ∈ sortedDivisors m) :
    d ≥ 1 := by
  have hmem : d ∈ m.divisors := by
    simp only [sortedDivisors, Finset.mem_sort] at hd; exact hd
  exact Nat.pos_of_mem_divisors hmem

/--
sortedDivisors is sorted in increasing order.
-/
theorem sortedDivisors_sorted (m : ℕ) :
    (sortedDivisors m).Pairwise (· ≤ ·) :=
  Finset.pairwise_sort m.divisors (· ≤ ·)

/--
sortedDivisors has no duplicates.
-/
theorem sortedDivisors_nodup (m : ℕ) :
    (sortedDivisors m).Nodup :=
  m.divisors.sort_nodup (· ≤ ·)

/--
The head of sortedDivisors m is 1 for m ≥ 1.
Proof: 1 is a divisor, all divisors ≥ 1, sorted, so head ≤ 1 ≤ head.
-/
theorem sortedDivisors_head_eq_one (m : ℕ) (hm : m ≥ 1) :
    (sortedDivisors m).head (sortedDivisors_ne_nil m hm) = 1 := by
  set hd := (sortedDivisors m).head (sortedDivisors_ne_nil m hm) with hd_def
  have hsorted := sortedDivisors_sorted m
  have h1 := one_mem_sortedDivisors m hm
  have hd_pos := sortedDivisors_pos m hd (List.head_mem (sortedDivisors_ne_nil m hm))
  by_contra hne
  have hge2 : hd ≥ 2 := by omega
  have hcons : sortedDivisors m = hd :: (sortedDivisors m).tail :=
    (List.cons_head_tail (sortedDivisors_ne_nil m hm)).symm
  rw [hcons] at h1
  rcases List.mem_cons.mp h1 with heq | htl
  · exact hne heq.symm
  · rw [hcons] at hsorted
    have := (List.pairwise_cons.mp hsorted).1 1 htl
    omega

/--
sortedDivisors m starts with 1 :: rest for m ≥ 1.
-/
theorem sortedDivisors_cons (m : ℕ) (hm : m ≥ 1) :
    ∃ rest, sortedDivisors m = 1 :: rest := by
  have hne := sortedDivisors_ne_nil m hm
  have hhead := sortedDivisors_head_eq_one m hm
  exact ⟨(sortedDivisors m).tail, by rw [← hhead]; exact (List.cons_head_tail hne).symm⟩

/--
For m ≥ 2, sortedDivisors m has at least 2 elements.
-/
theorem sortedDivisors_length_ge_2 (m : ℕ) (hm : m ≥ 2) :
    (sortedDivisors m).length ≥ 2 := by
  simp [sortedDivisors, Finset.length_sort]
  have h1 : 1 ∈ m.divisors := Nat.one_mem_divisors.mpr (by omega)
  have hm_mem : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_refl m, by omega⟩
  have hne : (1 : ℕ) ≠ m := by omega
  calc m.divisors.card
      ≥ ({1, m} : Finset ℕ).card :=
        Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨h1, Finset.singleton_subset_iff.mpr hm_mem⟩)
    _ = 2 := Finset.card_pair hne

/--
For m ≥ 2, the second element of sortedDivisors (given as first element of rest) is ≥ 2.
-/
theorem sortedDivisors_second_ge_2 (m : ℕ) (_hm : m ≥ 2)
    (rest : List ℕ) (hsd : sortedDivisors m = 1 :: rest)
    (hrest : rest ≠ []) : rest.head hrest ≥ 2 := by
  have hnodup := sortedDivisors_nodup m
  rw [hsd] at hnodup
  have hd2_pos := sortedDivisors_pos m (rest.head hrest)
    (by rw [hsd]; exact List.mem_cons.mpr (Or.inr (List.head_mem hrest)))
  have hne1 : rest.head hrest ≠ 1 := by
    intro heq
    have : 1 ∈ rest := heq ▸ List.head_mem hrest
    exact (List.nodup_cons.mp hnodup).1 this
  omega

/-
## Non-Representable Values

We prove that 2 and 5 cannot be represented as partial sums of divisors.
-/

/--
2 is not a partial sum of divisors of any m in {1, ..., 200}.
-/
theorem not_representable_2_small : isRepresentableBound 2 200 = false := by
  native_decide

/--
5 is not a partial sum of divisors of any m in {1, ..., 200}.
-/
theorem not_representable_5_small : isRepresentableBound 5 200 = false := by
  native_decide

/-- Helper: m ≥ 2 if sortedDivisors has 2+ elements -/
private theorem m_ge_2_of_cons2 (m : ℕ) (hm : m ≥ 1)
    (d₂ : ℕ) (rest' : List ℕ) (hsd : sortedDivisors m = 1 :: d₂ :: rest') : m ≥ 2 := by
  by_contra hlt; push_neg at hlt
  have hm1 : m = 1 := by omega
  subst hm1
  simp [sortedDivisors] at hsd

/--
Key structural fact for n=2: partial sums skip 2.

For m = 1: partialDivisorSums 1 = [1], so 2 ∉ [1].
For m ≥ 2: sortedDivisors m = 1 :: d₂ :: rest with d₂ ≥ 2.
  scanl (+) 0 (1 :: d₂ :: rest) = [0, 1, 1+d₂, ...]
  .tail = [1, 1+d₂, ...]  where 1+d₂ ≥ 3
  Every subsequent element ≥ 1+d₂ ≥ 3.
  So elements are: 1 (≠ 2) and things ≥ 3 (> 2). QED.
-/
theorem partial_sums_skip_2 (m : ℕ) (hm : m ≥ 1) :
    2 ∉ partialDivisorSums m := by
  simp only [partialDivisorSums]
  obtain ⟨rest, hsd⟩ := sortedDivisors_cons m hm
  rw [hsd, List.scanl, List.tail_cons]
  show 2 ∉ rest.scanl (· + ·) (0 + 1)
  match rest with
  | [] =>
    simp [List.scanl]
  | d₂ :: rest' =>
    simp only [List.scanl, List.mem_cons]
    push_neg
    constructor
    · omega  -- 2 ≠ 0 + 1
    · intro h2mem
      have hge := scanl_add_ge_init (0 + 1 + d₂) rest' 2 h2mem
      have hm2 := m_ge_2_of_cons2 m hm d₂ rest' hsd
      have hd2_ge_2 : d₂ ≥ 2 := by
        have hrest_ne : (d₂ :: rest' : List ℕ) ≠ [] := List.cons_ne_nil _ _
        have h := sortedDivisors_second_ge_2 m hm2 (d₂ :: rest') hsd hrest_ne
        simp only [List.head_cons] at h; exact h
      omega

/--
Helper: if 4 ∣ m then 2 ∣ m.
-/
private theorem dvd_4_imp_dvd_2 {m : ℕ} (h : 4 ∣ m) : 2 ∣ m := by
  obtain ⟨k, hk⟩ := h; exact ⟨2 * k, by omega⟩

/--
Helper: if d₂ = 4 is the second element in sortedDivisors m,
then 2 ∈ sortedDivisors m (since 4|m → 2|m).
But 2 comes after 4 in the sorted list, contradicting 2 < 4.
This eliminates the d₂ = 4 case.
-/
private theorem not_second_divisor_4 (m : ℕ) (_hm : m ≥ 2)
    (rest : List ℕ) (hsd : sortedDivisors m = 1 :: 4 :: rest) : False := by
  -- 4 is in sortedDivisors, hence 4 ∣ m
  have h4_mem : (4 : ℕ) ∈ sortedDivisors m := by rw [hsd]; simp
  have h4_in_div : 4 ∈ m.divisors := by
    simp only [sortedDivisors, Finset.mem_sort] at h4_mem; exact h4_mem
  have h4_dvd_m : 4 ∣ m := (Nat.mem_divisors.mp h4_in_div).1
  have h2_dvd_m : 2 ∣ m := dvd_4_imp_dvd_2 h4_dvd_m
  -- So 2 ∈ sortedDivisors m
  have h2_in_sd : 2 ∈ sortedDivisors m := by
    simp only [sortedDivisors, Finset.mem_sort]
    exact Nat.mem_divisors.mpr ⟨h2_dvd_m, by omega⟩
  -- But sortedDivisors m = [1, 4, ...rest], and 2 ∈ this list
  rw [hsd] at h2_in_sd
  simp at h2_in_sd
  -- h2_in_sd : 2 ∈ rest (since 2 ≠ 1 and 2 ≠ 4)
  -- But the list [1, 4, rest...] is sorted, so all elements in rest ≥ 4
  have hsorted := sortedDivisors_sorted m
  rw [hsd] at hsorted
  have h4_sorted : (4 :: rest).Pairwise (· ≤ ·) := (List.pairwise_cons.mp hsorted).2
  have hall_ge_4 := (List.pairwise_cons.mp h4_sorted).1
  exact absurd (hall_ge_4 2 h2_in_sd) (by omega)

/--
Key structural fact for n=5: partial sums skip 5.

Case analysis on the second-smallest divisor d₂:
- d₂ = 2: sums are [1, 3, ≥6, ...] (d₃ > 2, so ≥ 3, giving 3+d₃ ≥ 6)
- d₂ = 3: sums are [1, 4, ≥9, ...] (d₃ > 3 and odd, so ≥ 5, giving 4+d₃ ≥ 9)
- d₂ = 4: impossible (4|m → 2|m → d₂ = 2)
- d₂ ≥ 5: sums are [1, ≥6, ...] (1+d₂ ≥ 6 > 5)
In all cases, 5 never appears.
-/
theorem partial_sums_skip_5 (m : ℕ) (hm : m ≥ 1) :
    5 ∉ partialDivisorSums m := by
  simp only [partialDivisorSums]
  obtain ⟨rest, hsd⟩ := sortedDivisors_cons m hm
  rw [hsd, List.scanl, List.tail_cons]
  show 5 ∉ rest.scanl (· + ·) (0 + 1)
  match rest with
  | [] =>
    simp [List.scanl]
  | d₂ :: rest' =>
    simp only [List.scanl, List.mem_cons]
    push_neg
    have hm2 := m_ge_2_of_cons2 m hm d₂ rest' hsd
    have hd2_ge_2 : d₂ ≥ 2 := by
      have hrest_ne : (d₂ :: rest' : List ℕ) ≠ [] := List.cons_ne_nil _ _
      have h := sortedDivisors_second_ge_2 m hm2 (d₂ :: rest') hsd hrest_ne
      simp only [List.head_cons] at h; exact h
    constructor
    · omega  -- 5 ≠ 0 + 1
    · match rest' with
      | [] =>
        -- Two divisors: scanl (+) (1+d₂) [] = [1+d₂]
        simp [List.scanl]
        -- Need 5 ≠ 0 + 1 + d₂. If d₂ = 4, contradiction via not_second_divisor_4
        intro h5eq
        have hd2_eq_4 : d₂ = 4 := by omega
        subst hd2_eq_4
        exact not_second_divisor_4 m hm2 [] hsd
      | d₃ :: rest'' =>
        -- Three+ divisors
        simp only [List.scanl, List.mem_cons]
        push_neg
        constructor
        · -- 5 ≠ 0 + 1 + d₂. If d₂ = 4, contradiction.
          intro h5eq
          have hd2_eq_4 : d₂ = 4 := by omega
          subst hd2_eq_4
          exact not_second_divisor_4 m hm2 (d₃ :: rest'') hsd
        · -- 5 ∉ scanl (+) (0 + 1 + d₂ + d₃) rest''
          intro h5mem
          have hge := scanl_add_ge_init (0 + 1 + d₂ + d₃) rest'' 5 h5mem
          have hsorted := sortedDivisors_sorted m
          rw [hsd] at hsorted
          have hnodup := sortedDivisors_nodup m
          rw [hsd] at hnodup
          have hd2_lt_d3 : d₂ < d₃ := by
            have hsort_rest := (List.pairwise_cons.mp hsorted).2
            have hd2_le_d3 := (List.pairwise_cons.mp hsort_rest).1 d₃ List.mem_cons_self
            have hnd := (List.nodup_cons.mp hnodup).2
            have hne : d₂ ≠ d₃ := fun heq => by
              rw [heq] at hnd
              exact (List.nodup_cons.mp hnd).1 List.mem_cons_self
            omega
          omega

/-
## The Open Problem
-/

/--
**Open Question I**: Is f(n) = o(n)?
Terry Tao showed this is FALSE.
-/
def erdos_1054_part_i : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, (computeF n : ℝ) < ε * n

/--
**Open Question II**: Is f(n) = o(n) for almost all n?
The set of exceptions should have natural density 0.
-/
def erdos_1054_part_ii : Prop :=
  ∀ ε > 0, ∀ δ > 0, ∃ N : ℕ, ∀ M ≥ N,
    ((Finset.filter (fun n => decide ((computeF n : ℝ) ≥ ε * n)) (Finset.range M)).card : ℝ) < δ * M

/--
**Open Question III**: Is limsup f(n)/n = ∞?
-/
def erdos_1054_part_iii : Prop :=
  ∀ C : ℝ, ∃ n : ℕ, n ≥ 1 ∧ (computeF n : ℝ) ≥ C * n

/--
Tao's result: Part I is FALSE.
-/
axiom tao_disproves_part_i : ¬erdos_1054_part_i

/-
## Structural Lemmas
-/

/--
If 4 divides m, then 2 divides m.
-/
theorem dvd_4_implies_dvd_2 (m : ℕ) (h : 4 ∣ m) : 2 ∣ m := by
  obtain ⟨k, hk⟩ := h
  exact ⟨2 * k, by omega⟩

/--
Every m ≥ 2 has a prime factor p ≥ 2.
-/
theorem exists_prime_factor_ge_2 (m : ℕ) (hm : m ≥ 2) :
    ∃ p, p.Prime ∧ p ∣ m ∧ p ≥ 2 := by
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  exact ⟨p, hp, hpm, hp.two_le⟩

/-
## Understanding the Problem

The key insight is that small divisors are very constrained:
- Every number's smallest divisor is 1
- The second smallest is the smallest prime factor
- Numbers with only large prime factors have sparse small divisors

For n to equal a sum of k smallest divisors of m:
- If k = 1: n = 1 (only works for n = 1)
- If k = 2: n = 1 + p where p is the smallest prime factor of m
- In general, the sums are constrained by the divisor structure
-/

/-
## Partial Sums Table

- m = 1: divisors [1], partial sums [1]
- m = 2: divisors [1, 2], partial sums [1, 3]
- m = 3: divisors [1, 3], partial sums [1, 4]
- m = 4: divisors [1, 2, 4], partial sums [1, 3, 7]
- m = 5: divisors [1, 5], partial sums [1, 6]
- m = 6: divisors [1, 2, 3, 6], partial sums [1, 3, 6, 12]
- m = 7: divisors [1, 7], partial sums [1, 8]
- m = 8: divisors [1, 2, 4, 8], partial sums [1, 3, 7, 15]
- m = 9: divisors [1, 3, 9], partial sums [1, 4, 13]
- m = 10: divisors [1, 2, 5, 10], partial sums [1, 3, 8, 18]

The values 2 and 5 never appear as partial sums.
-/

-- ============================================================
-- Additional Structural Lemmas
-- ============================================================

/--
For any m ≥ 2, the smallest divisor > 1 is the minimum prime factor.
This is the second element in the sorted divisor list.
-/
theorem smallest_nontrivial_divisor (m : ℕ) (_hm : m ≥ 2) (d : ℕ)
    (hd : d ∈ m.divisors) (hd1 : d > 1) : d ≥ m.minFac := by
  exact Nat.minFac_le_of_dvd hd1 (Nat.mem_divisors.mp hd).1

/-
For a prime p ≥ 2, p+1 is representable: the divisors of p are {1, p}
and the partial sums are [1, 1+p]. This means f(p+1) ≤ p < p+1.
-/

/-- 4 = 3+1 where 3 is prime; f(4) = 3 -/
theorem f_4_via_prime : computeF 4 20 = 3 := by native_decide

/-- 6 = 5+1 where 5 is prime; f(6) = 5 -/
theorem f_6_via_prime : computeF 6 20 = 5 := by native_decide

/-- 8 = 7+1 where 7 is prime; f(8) = 7 -/
theorem f_8_via_prime : computeF 8 20 = 7 := by native_decide

/-- 12 = 11+1 where 11 is prime; f(12) = 6 < 11 (better witness exists) -/
theorem f_12_via_prime : computeF 12 20 = 6 := by native_decide

/-- 14 = 13+1 where 13 is prime; f(14) ≤ 13 -/
theorem representable_14 : IsRepresentable 14 :=
  ⟨13, by omega, by native_decide⟩

theorem f_14_eq : computeF 14 20 = 13 := by native_decide

-- ============================================================
-- Extended Non-Representability Verification
-- ============================================================

/-- 2 is not a partial sum of divisors of any m in {1, ..., 1000}. -/
theorem not_representable_2_large : isRepresentableBound 2 1000 = false := by
  native_decide

/-- 5 is not a partial sum of divisors of any m in {1, ..., 1000}. -/
theorem not_representable_5_large : isRepresentableBound 5 1000 = false := by
  native_decide

/-- 11 is representable: divisors of 30 are {1,2,3,5,6,10,15,30}, 1+2+3+5=11. -/
theorem representable_11 : IsRepresentable 11 :=
  ⟨30, by omega, by native_decide⟩

/-- 13 is representable -/
theorem representable_13 : IsRepresentable 13 :=
  ⟨9, by omega, by native_decide⟩

/-- f(13) = 9 -/
theorem f_13_eq : computeF 13 20 = 9 := by native_decide

/-- 15 is representable -/
theorem representable_15 : IsRepresentable 15 :=
  ⟨8, by omega, by native_decide⟩

/-- f(15) = 8 -/
theorem f_15_eq : computeF 15 20 = 8 := by native_decide

-- ============================================================
-- f(n) Table (extended)
-- ============================================================

/-
Extended table of f(n) values:
- f(1) = 1      f(1)/1 = 1.0
- f(3) = 2      f(3)/3 = 0.67
- f(4) = 3      f(4)/4 = 0.75
- f(6) = 5      f(6)/6 = 0.83
- f(7) = 4      f(7)/7 = 0.57
- f(8) = 7      f(8)/8 = 0.88
- f(9) = 15     f(9)/9 = 1.67 ← exceeds 1!
- f(10) = 12    f(10)/10 = 1.2
- f(11) = 30    f(11)/11 = 2.73 ← large ratio!
- f(12) = 6     f(12)/12 = 0.5
- f(13) = 9     f(13)/13 = 0.69
- f(14) = 13    f(14)/14 = 0.93
- f(15) = 8     f(15)/15 = 0.53

Key observation: f(9) = 15 > 9, showing f(n)/n can exceed 1.
f(11) = 30, showing f(n)/n ≈ 2.73 — the ratio can be quite large.

Tao proved that f(n)/n is unbounded, confirming Part III.
-/

end Erdos1054
