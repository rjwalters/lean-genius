/-
Erdős Problem #884: Divisor Gap Sums

Source: https://erdosproblems.com/884
Status: OPEN
Reference: Erdős [Er98], related to Problem #144

Statement:
Let d₁ < d₂ < ... < d_t be the divisors of n. Is it true that
  Σ_{1≤i<j≤t} 1/(d_j - d_i) ≪ 1 + Σ_{1≤i<t} 1/(d_{i+1} - d_i)
with an absolute implied constant?

The left side sums over ALL pairs of divisors; the right side sums only over
CONSECUTIVE divisors. The question asks whether the all-pairs sum is controlled
by the consecutive-pairs sum (plus 1) up to a universal constant.

Terence Tao has indicated this problem appears tractable.
-/

import Mathlib

open Nat Finset BigOperators

namespace Erdos884

/-
# Erdős Problem 884: Divisor Gap Sums

*Reference:* [erdosproblems.com/884](https://www.erdosproblems.com/884)

For a positive integer n with divisors d₁ < d₂ < ··· < d_t, this problem asks whether
the sum over all pairs 1/(d_j - d_i) is bounded by an absolute constant times
(1 + sum over consecutive pairs 1/(d_{i+1} - d_i)).
-/

/- ## Divisor Lists -/

/-- The divisors of n as a sorted list. -/
def divisorList (n : ℕ) : List ℕ :=
  (n.divisors.sort (· ≤ ·))

/-- Number of divisors τ(n). -/
def numDivisors (n : ℕ) : ℕ := n.divisors.card

/-- Access the i-th divisor (0-indexed). -/
def divisor (n i : ℕ) : ℕ :=
  (divisorList n).getD i 0

/- ## Helper Lemmas -/

/-- Length of divisorList equals numDivisors. -/
theorem divisorList_length (n : ℕ) : (divisorList n).length = numDivisors n := by
  unfold divisorList numDivisors
  exact Finset.length_sort (· ≤ ·)

/-- Convert getD to getElem when index is in bounds. -/
private theorem getD_zero_eq_getElem (l : List ℕ) (k : ℕ) (h : k < l.length) :
    l.getD k 0 = l[k] := by
  induction l generalizing k with
  | nil => simp at h
  | cons a t ih =>
    cases k with
    | zero => rfl
    | succ k' => exact ih k' (by simpa using h)

/-- The divisor list is pairwise strictly increasing. -/
theorem divisorList_pairwise_lt (n : ℕ) : (divisorList n).Pairwise (· < ·) := by
  unfold divisorList
  have hle := Finset.pairwise_sort n.divisors (· ≤ ·)
  have hnd := n.divisors.sort_nodup (· ≤ ·)
  rw [List.pairwise_iff_getElem] at hle ⊢
  intro i j hi hj hij
  have hle' := hle i j hi hj hij
  have hne := (List.pairwise_iff_getElem.mp hnd) i j hi hj hij
  omega

/-- The divisor list contains exactly the positive divisors. -/
theorem mem_divisorList_iff (n d : ℕ) (hn : n > 0) :
    d ∈ divisorList n ↔ d ∣ n ∧ d > 0 := by
  unfold divisorList
  rw [Finset.mem_sort, Nat.mem_divisors]
  constructor
  · rintro ⟨hdvd, hne⟩
    refine ⟨hdvd, ?_⟩
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; simp at hdvd; exact absurd hdvd hne
    · exact h
  · rintro ⟨hdvd, _⟩
    exact ⟨hdvd, by omega⟩

/-- In a pairwise (· < ·) ℕ list, getD respects the strict order. -/
private theorem pairwise_getD_lt {l : List ℕ} (hs : l.Pairwise (· < ·))
    {i j : ℕ} (hij : i < j) (hj : j < l.length) :
    l.getD i 0 < l.getD j 0 := by
  have hi : i < l.length := Nat.lt_trans hij hj
  rw [getD_zero_eq_getElem l i hi, getD_zero_eq_getElem l j hj]
  exact (List.pairwise_iff_getElem.mp hs) i j hi hj hij

/-- In a pairwise (· < ·) ℕ list, getD respects the weak order. -/
private theorem pairwise_getD_le {l : List ℕ} (hs : l.Pairwise (· < ·))
    {i j : ℕ} (hij : i ≤ j) (hj : j < l.length) :
    l.getD i 0 ≤ l.getD j 0 := by
  rcases eq_or_lt_of_le hij with h | h
  · subst h; exact le_refl _
  · exact le_of_lt (pairwise_getD_lt hs h hj)

/- ## Divisor Gaps -/

/-- Consecutive divisor gap: d_{i+1} - d_i. -/
def consecutiveGap (n i : ℕ) : ℕ :=
  divisor n (i + 1) - divisor n i

/-- General divisor gap: d_j - d_i for any pair. -/
def generalGap (n i j : ℕ) : ℕ :=
  divisor n j - divisor n i

/-- Consecutive gaps are positive for sorted divisors. -/
theorem consecutiveGap_pos (n i : ℕ) (_hn : n > 1) (hi : i + 1 < numDivisors n) :
    consecutiveGap n i > 0 := by
  unfold consecutiveGap divisor
  have hlen := divisorList_length n
  have hi1 : i + 1 < (divisorList n).length := by omega
  have hlt := pairwise_getD_lt (divisorList_pairwise_lt n) (by omega : i < i + 1) hi1
  omega

/-- General gaps with i < j are positive. -/
theorem generalGap_pos (n i j : ℕ) (_hn : n > 1) (hij : i < j) (hj : j < numDivisors n) :
    generalGap n i j > 0 := by
  unfold generalGap divisor
  have hlen := divisorList_length n
  have hj' : j < (divisorList n).length := by omega
  have hlt := pairwise_getD_lt (divisorList_pairwise_lt n) hij hj'
  omega

/- ## The Two Sums -/

/-- All-pairs sum: Σ_{0≤i<j<t} 1/(d_j - d_i).
    This sums over all C(τ(n), 2) pairs of divisors. -/
noncomputable def allPairsSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (numDivisors n),
    ∑ j ∈ Finset.Ioo i (numDivisors n),
      (1 : ℝ) / (generalGap n i j)

/-- Consecutive-pairs sum: Σ_{0≤i<t-1} 1/(d_{i+1} - d_i).
    This sums over the τ(n) - 1 consecutive gaps. -/
noncomputable def consecutivePairsSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (numDivisors n - 1),
    (1 : ℝ) / (consecutiveGap n i)

/- ## The Main Conjecture -/

/-- Erdős Problem #884 (OPEN):
    Does there exist an absolute constant C such that for all n ≥ 2,
    allPairsSum(n) ≤ C · (1 + consecutivePairsSum(n))? -/
def ErdosConjecture884 : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n > 1 →
    allPairsSum n ≤ C * (1 + consecutivePairsSum n)

/-- The conjecture is axiomatized as the problem is OPEN. -/
axiom erdos_884 : ErdosConjecture884

/- ## Basic Properties -/

/-- The all-pairs sum is non-negative (sum of 1/gap ≥ 0). -/
theorem allPairsSum_nonneg (n : ℕ) : allPairsSum n ≥ 0 := by
  unfold allPairsSum
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact div_nonneg one_pos.le (Nat.cast_nonneg _)

/-- The consecutive-pairs sum is non-negative (sum of 1/gap ≥ 0). -/
theorem consecutivePairsSum_nonneg (n : ℕ) : consecutivePairsSum n ≥ 0 := by
  unfold consecutivePairsSum
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg one_pos.le (Nat.cast_nonneg _)

/-- Number of terms in consecutive-pairs sum: τ(n) - 1. -/
theorem consecutivePairsSum_num_terms (n : ℕ) (_hn : n > 0) :
    (Finset.range (numDivisors n - 1)).card = numDivisors n - 1 := by
  simp

/- ## Examples -/

/-- For n = 6, divisors are [1, 2, 3, 6]. -/
theorem divisors_6 : divisorList 6 = [1, 2, 3, 6] := by native_decide

/-- For prime p, divisors are [1, p].
    Proof: p.divisors = {1, p} by Nat.Prime.divisors, giving a sorted list
    of length 2 with elements 1 and p. Since 1 < p, the sorted order is [1, p]. -/
theorem divisors_prime (p : ℕ) (hp : p.Prime) :
    divisorList p = [1, p] := by
  have hp1 : (1 : ℕ) ≠ p := hp.one_lt.ne
  -- The sorted list has length 2 and contains exactly 1 and p
  have hlen : (divisorList p).length = 2 := by
    rw [divisorList_length]; unfold numDivisors; rw [hp.divisors]
    rw [Finset.card_pair hp1]
  have hmem : ∀ x, x ∈ divisorList p ↔ x = 1 ∨ x = p := by
    intro x; rw [mem_divisorList_iff _ _ hp.pos]
    constructor
    · intro ⟨hdvd, _⟩; exact hp.eq_one_or_self_of_dvd x hdvd
    · rintro (rfl | rfl)
      · exact ⟨one_dvd _, by omega⟩
      · exact ⟨dvd_refl _, hp.pos⟩
  -- Extract the two elements and use sortedness + membership to determine order
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rw [hab]
  have hsorted := divisorList_pairwise_lt p; rw [hab] at hsorted
  have h_lt : a < b := (List.pairwise_cons.mp hsorted).1 b (List.mem_singleton.mpr rfl)
  have ha : a = 1 ∨ a = p := (hmem a).mp (by rw [hab]; simp)
  have hb : b = 1 ∨ b = p := (hmem b).mp (by rw [hab]; simp)
  have hp2 := hp.one_lt
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> first | rfl | omega

/-- For primes, allPairsSum = consecutivePairsSum (trivially: only one pair).
    Proof: numDivisors p = 2, so both sums have exactly one term with the same gap. -/
theorem prime_case_equality (p : ℕ) (hp : p.Prime) :
    allPairsSum p = consecutivePairsSum p := by
  have hnd : numDivisors p = 2 := by
    unfold numDivisors; rw [hp.divisors]
    rw [Finset.card_pair hp.one_lt.ne]
  -- Both sums reduce to 1/(divisor p 1 - divisor p 0) = 1/(p - 1)
  unfold allPairsSum consecutivePairsSum
  rw [hnd]
  -- Simplify Ioo finsets and range sums
  have h1 : Finset.Ioo 0 2 = {1} := by decide
  have h2 : Finset.Ioo 1 2 = ∅ := by decide
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
             h1, h2, Finset.sum_singleton, Finset.sum_empty,
             add_zero, zero_add]
  -- generalGap p 0 1 = consecutiveGap p 0 definitionally (both = divisor p 1 - divisor p 0)
  have : generalGap p 0 1 = consecutiveGap p 0 := rfl
  rw [this]

/- ## Structural Lemmas -/

/-- Any general gap is at least the corresponding consecutive gap.
    d_j - d_i ≥ d_{i+1} - d_i since divisors are increasing.
    Requires j to be in range (otherwise getD returns 0 and the inequality fails). -/
theorem gap_lower_bound (n i j : ℕ) (hij : i < j) (hj : j < numDivisors n) :
    generalGap n i j ≥ consecutiveGap n i := by
  unfold generalGap consecutiveGap divisor
  apply Nat.sub_le_sub_right
  have hlen := divisorList_length n
  have hj' : j < (divisorList n).length := by omega
  exact pairwise_getD_le (divisorList_pairwise_lt n) (by omega : i + 1 ≤ j) hj'

/-- For coprime m, n: τ(mn) = τ(m) · τ(n). -/
/- Note: Nat.Coprime.divisors_mul was removed/renamed in Mathlib v4.26.0.
   This theorem was proved in the original file but needs API update. -/
theorem numDivisors_mul_coprime (m n : ℕ) (_hm : m > 0) (_hn : n > 0)
    (_hcop : Nat.Coprime m n) :
    numDivisors (m * n) = numDivisors m * numDivisors n := by
  sorry

/- ## Connections -/

/-- The harmonic sum over divisors: σ_{-1}(n) = Σ_{d|n} 1/d. -/
noncomputable def divisorHarmonicSum (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (1 : ℝ) / d

/-- The conjecture statement matches the informal problem. -/
theorem erdos_884_statement : ErdosConjecture884 ↔
    ∃ C : ℝ, C > 0 ∧ ∀ n > 1, allPairsSum n ≤ C * (1 + consecutivePairsSum n) := by
  rfl

end Erdos884
