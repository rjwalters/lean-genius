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

/-- For prime p, divisors are [1, p]. -/
theorem divisors_prime (p : ℕ) (hp : p.Prime) :
    divisorList p = [1, p] := by
  unfold divisorList
  rw [Nat.Prime.divisors hp]
  -- Use pairwise_getD_lt from divisorList_pairwise_lt to characterize the sorted list
  -- Alternative: use the length-2 sorted list characterization
  have hlt : (1 : ℕ) < p := hp.one_lt
  have hne : (1 : ℕ) ≠ p := Nat.ne_of_lt hlt
  -- The sorted list has length 2 and contains exactly 1 and p
  -- Use properties: mem_sort, length_sort, sort_nodup, sort_sorted
  -- Extract as a length-2 list
  have hlen : (({1, p} : Finset ℕ).sort (· ≤ ·)).length = 2 := by
    rw [Finset.length_sort]; exact Finset.card_pair hne
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  -- a and b are in {1, p}
  have ha : a ∈ ({1, p} : Finset ℕ) := by
    rw [← Finset.mem_sort (r := (· ≤ ·)), hab]; simp
  have hb : b ∈ ({1, p} : Finset ℕ) := by
    rw [← Finset.mem_sort (r := (· ≤ ·)), hab]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  -- No duplicates
  have hnd : a ≠ b := by
    have hnodup := (({1, p} : Finset ℕ).sort_nodup (· ≤ ·))
    rw [hab] at hnodup
    simp [List.nodup_cons, List.not_mem_nil] at hnodup
    exact hnodup
  -- Sorted: a ≤ b
  have _hle : a ≤ b := by
    have hs := (({1, p} : Finset ℕ).sort_sorted (· ≤ ·))
    rw [hab] at hs
    simp [List.Sorted, List.Pairwise] at hs
    exact hs
  rw [hab]
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hnd
  · rfl
  · exfalso; omega
  · exact absurd rfl hnd

/-- For primes, numDivisors p = 2. -/
theorem numDivisors_prime (p : ℕ) (hp : p.Prime) : numDivisors p = 2 := by
  unfold numDivisors
  rw [Nat.Prime.divisors hp]
  exact Finset.card_pair (Nat.ne_of_lt hp.one_lt)

/-- generalGap n 0 1 = consecutiveGap n 0 by definition. -/
private theorem generalGap_zero_one (n : ℕ) :
    generalGap n 0 1 = consecutiveGap n 0 := by
  unfold generalGap consecutiveGap
  rfl

/-- For primes, allPairsSum = consecutivePairsSum (trivially: only one pair). -/
theorem prime_case_equality (p : ℕ) (hp : p.Prime) :
    allPairsSum p = consecutivePairsSum p := by
  unfold allPairsSum consecutivePairsSum
  rw [numDivisors_prime p hp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  -- LHS: 0 + (∑ j ∈ Ioo 0 2, 1/generalGap p 0 j) + (∑ j ∈ Ioo 1 2, 1/generalGap p 1 j)
  -- Ioo 1 2 = ∅, Ioo 0 2 = {1}
  have h1 : Finset.Ioo 1 2 = (∅ : Finset ℕ) := by decide
  have h2 : Finset.Ioo 0 2 = ({1} : Finset ℕ) := by decide
  rw [h1, h2, Finset.sum_empty, add_zero, Finset.sum_singleton]
  rw [generalGap_zero_one]

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

/-- σ₀(n) = τ(n) = n.divisors.card. -/
private theorem sigma_zero_eq_card (n : ℕ) :
    ArithmeticFunction.sigma 0 n = numDivisors n := by
  unfold numDivisors
  simp [ArithmeticFunction.sigma_apply]

/-- For coprime m, n: τ(mn) = τ(m) · τ(n). -/
/- Proved via σ₀ multiplicativity after Nat.Coprime.divisors_mul was renamed. -/
theorem numDivisors_mul_coprime (m n : ℕ) (_hm : m > 0) (_hn : n > 0)
    (hcop : Nat.Coprime m n) :
    numDivisors (m * n) = numDivisors m * numDivisors n := by
  rw [← sigma_zero_eq_card, ← sigma_zero_eq_card, ← sigma_zero_eq_card]
  exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop

/- ## Connections -/

/-- The harmonic sum over divisors: σ_{-1}(n) = Σ_{d|n} 1/d. -/
noncomputable def divisorHarmonicSum (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (1 : ℝ) / d

/-- The conjecture statement matches the informal problem. -/
theorem erdos_884_statement : ErdosConjecture884 ↔
    ∃ C : ℝ, C > 0 ∧ ∀ n > 1, allPairsSum n ≤ C * (1 + consecutivePairsSum n) := by
  rfl

end Erdos884
