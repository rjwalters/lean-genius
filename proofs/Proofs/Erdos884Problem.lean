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

/-- Strict monotonicity of divisor indexing. -/
theorem divisor_strictMono (n : ℕ) {i j : ℕ} (hij : i < j) (hj : j < numDivisors n) :
    divisor n i < divisor n j := by
  unfold divisor
  have hlen := divisorList_length n
  exact pairwise_getD_lt (divisorList_pairwise_lt n) hij (by omega)

/-- In a strictly increasing ℕ list, elements grow by at least one per index step. -/
private theorem pairwise_lt_getD_ge_diff {l : List ℕ} (hs : l.Pairwise (· < ·))
    {i j : ℕ} (hij : i ≤ j) (hj : j < l.length) :
    l.getD i 0 + (j - i) ≤ l.getD j 0 := by
  induction j with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le hij with rfl | hik
    · omega
    · have hk : k < l.length := by omega
      have ih_res := ih (by omega : i ≤ k) hk
      have hlt := pairwise_getD_lt hs (by omega : k < k + 1) hj
      omega

/-- The general gap d_j - d_i is at least j - i (divisors grow by ≥ 1 per step). -/
theorem generalGap_ge_diff (n : ℕ) {i j : ℕ} (hij : i ≤ j) (hj : j < numDivisors n) :
    j - i ≤ generalGap n i j := by
  unfold generalGap divisor
  have hlen := divisorList_length n
  have h := pairwise_lt_getD_ge_diff (divisorList_pairwise_lt n) hij (by omega)
  omega

/- ## Telescoping -/

/-- Additive decomposition of general gaps at a midpoint.
    d_k - d_i = (d_j - d_i) + (d_k - d_j) when i ≤ j ≤ k. -/
theorem generalGap_add_mid (n : ℕ) {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (hk : k < numDivisors n) :
    generalGap n i k = generalGap n i j + generalGap n j k := by
  unfold generalGap divisor
  have hlen := divisorList_length n
  have h1 := pairwise_getD_le (divisorList_pairwise_lt n) hjk (by omega)
  have h2 := pairwise_getD_le (divisorList_pairwise_lt n) hij (by omega)
  omega

/-- The general gap telescopes into a sum of consecutive gaps.
    d_j - d_i = Σ_{k=i}^{j-1} (d_{k+1} - d_k). -/
theorem generalGap_telescope (n : ℕ) {i j : ℕ} (hij : i ≤ j) (hj : j < numDivisors n) :
    generalGap n i j = ∑ k ∈ Finset.Ico i j, consecutiveGap n k := by
  have hlen := divisorList_length n
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; simp [generalGap]
  | succ j ih =>
    rcases eq_or_lt_of_le hij with rfl | hlt
    · simp [generalGap]
    · have hij' : i ≤ j := by omega
      have hj' : j < numDivisors n := by omega
      -- Split Ico i (j+1) = Ico i j ∪ {j}
      have hsplit : Finset.Ico i (j + 1) = insert j (Finset.Ico i j) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [hsplit, Finset.sum_insert (by simp [Finset.mem_Ico]; omega)]
      rw [ih hij' hj', add_comm]
      -- d_{j+1} - d_i = (d_j - d_i) + (d_{j+1} - d_j)
      exact generalGap_add_mid n hij' (Nat.le_succ j) (by omega)

/-- Any interior consecutive gap is dominated by the general gap.
    d_{k+1} - d_k ≤ d_j - d_i for i ≤ k < j. -/
theorem consecutiveGap_le_generalGap (n : ℕ) {i j k : ℕ}
    (hik : i ≤ k) (hkj : k < j) (hj : j < numDivisors n) :
    consecutiveGap n k ≤ generalGap n i j := by
  calc consecutiveGap n k
      ≤ generalGap n k j := gap_lower_bound n k j hkj hj
    _ ≤ generalGap n i j := by
        have := generalGap_add_mid n hik (le_of_lt hkj) hj
        omega

/- ## Per-Pair Bounds -/

/-- Index bound: each pair's contribution 1/(d_j - d_i) is bounded by 1/(j - i),
    since divisors are strictly increasing (grow at least 1 per step).
    This is the key step toward showing allPairsSum ≤ Σ_{s=1}^{τ-1} (τ-s)/s. -/
theorem reciprocal_gap_index_bound (n : ℕ) {i j : ℕ} (hn : n > 1) (hij : i < j)
    (hj : j < numDivisors n) :
    (1 : ℝ) / (generalGap n i j : ℝ) ≤ 1 / ((j - i : ℕ) : ℝ) := by
  have hge := generalGap_ge_diff n (le_of_lt hij) hj
  have hgap_pos := generalGap_pos n i j hn hij hj
  have hji_pos : (0 : ℕ) < j - i := by omega
  rw [div_le_div_iff (by exact_mod_cast hgap_pos : (0 : ℝ) < (generalGap n i j : ℝ))
      (by exact_mod_cast hji_pos : (0 : ℝ) < ((j - i : ℕ) : ℝ))]
  simp only [one_mul]
  exact_mod_cast hge

/-- Consecutive bound: each pair's contribution 1/(d_j - d_i) is bounded by the
    reciprocal of the first consecutive gap 1/(d_{i+1} - d_i), since general gaps
    dominate consecutive gaps. Combined with the index bound, these give:
    1/(d_j - d_i) ≤ min(1/(j-i), 1/g_i). -/
theorem reciprocal_gap_consecutive_bound (n : ℕ) {i j : ℕ} (hn : n > 1) (hij : i < j)
    (hj : j < numDivisors n) :
    (1 : ℝ) / (generalGap n i j : ℝ) ≤ 1 / (consecutiveGap n i : ℝ) := by
  have hge := gap_lower_bound n i j hij hj
  have hgap_pos := generalGap_pos n i j hn hij hj
  have hcons_pos := consecutiveGap_pos n i hn (by omega : i + 1 < numDivisors n)
  rw [div_le_div_iff (by exact_mod_cast hgap_pos : (0 : ℝ) < (generalGap n i j : ℝ))
      (by exact_mod_cast hcons_pos : (0 : ℝ) < (consecutiveGap n i : ℝ))]
  simp only [one_mul]
  exact_mod_cast hge

/- ## Connections -/

/-- The harmonic sum over divisors: σ_{-1}(n) = Σ_{d|n} 1/d. -/
noncomputable def divisorHarmonicSum (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, (1 : ℝ) / d

/-- The conjecture statement matches the informal problem. -/
theorem erdos_884_statement : ErdosConjecture884 ↔
    ∃ C : ℝ, C > 0 ∧ ∀ n > 1, allPairsSum n ≤ C * (1 + consecutivePairsSum n) := by
  rfl

/- ## Sum-Level Bound -/

/-- For n > 1, n has at least 2 divisors (1 and n). -/
private theorem numDivisors_ge_two (n : ℕ) (hn : n > 1) : numDivisors n ≥ 2 := by
  unfold numDivisors
  have h1 : (1 : ℕ) ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩
  have hn' : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl n, by omega⟩
  exact Finset.one_lt_card.mpr ⟨1, h1, n, hn', by omega⟩

/-- getD past the end of a ℕ list returns 0 (the default). -/
private theorem list_getD_zero_of_ge (l : List ℕ) (k : ℕ) (h : l.length ≤ k) :
    l.getD k 0 = 0 := by
  induction l generalizing k with
  | nil => simp [List.getD]
  | cons a t ih =>
    cases k with
    | zero => simp at h
    | succ k' =>
      simp only [List.getD, List.get?]
      exact ih (by simpa using h)

/-- Out-of-bounds divisor access returns 0. -/
private theorem divisor_eq_zero_of_ge (n k : ℕ) (hk : numDivisors n ≤ k) :
    divisor n k = 0 := by
  unfold divisor
  exact list_getD_zero_of_ge _ _ (by rw [divisorList_length]; exact hk)

/-- Consecutive gap at position τ(n)−1 is 0 (next divisor is out of bounds). -/
private theorem consecutiveGap_last_eq_zero (n : ℕ) (hn : n > 1) :
    consecutiveGap n (numDivisors n - 1) = 0 := by
  have hτ := numDivisors_ge_two n hn
  unfold consecutiveGap
  rw [show numDivisors n - 1 + 1 = numDivisors n by omega]
  rw [divisor_eq_zero_of_ge n (numDivisors n) le_rfl]
  exact Nat.zero_sub _

/-- Sum-level bound: the all-pairs sum is at most (τ(n)−1) times the consecutive-pairs sum.
    Each 1/(dⱼ−dᵢ) ≤ 1/(d_{i+1}−dᵢ), and for each i there are at most τ−1 values of j > i.
    This is a partial result toward Erdős 884 (which asks for an absolute constant). -/
theorem allPairsSum_le_tau_mul_consecutive (n : ℕ) (hn : n > 1) :
    allPairsSum n ≤ ((numDivisors n - 1 : ℕ) : ℝ) * consecutivePairsSum n := by
  have hτ := numDivisors_ge_two n hn
  set τ := numDivisors n with hτ_def
  -- Step 1: Bound each pair term and convert inner sum to nsmul
  have bound_step : allPairsSum n ≤
      ∑ i ∈ Finset.range τ,
        (Finset.Ioo i τ).card • ((1 : ℝ) / ↑(consecutiveGap n i)) := by
    unfold allPairsSum
    apply Finset.sum_le_sum; intro i _
    rw [← Finset.sum_const]
    apply Finset.sum_le_sum; intro j hj
    have ⟨hij, hjτ⟩ := Finset.mem_Ioo.mp hj
    exact reciprocal_gap_consecutive_bound n hn hij hjτ
  -- Step 2: card(Ioo i τ) ≤ τ - 1
  have card_bound : ∀ i, (Finset.Ioo i τ).card ≤ τ - 1 := by
    intro i
    have hsub : Finset.Ioo i τ ⊆ Finset.Ico 1 τ := by
      intro j; simp only [Finset.mem_Ioo, Finset.mem_Ico]; omega
    have hcard : (Finset.Ico 1 τ).card = τ - 1 := by
      have := Finset.card_Ico (α := ℕ) 1 τ; omega
    exact (Finset.card_le_card hsub).trans (le_of_eq hcard)
  -- Step 3: Last term vanishes
  have last_zero : (1 : ℝ) / ↑(consecutiveGap n (τ - 1)) = 0 := by
    rw [consecutiveGap_last_eq_zero n hn, Nat.cast_zero, div_zero]
  -- Combine via calc
  calc allPairsSum n
      ≤ ∑ i ∈ Finset.range τ,
          (Finset.Ioo i τ).card • ((1 : ℝ) / ↑(consecutiveGap n i)) := bound_step
    _ ≤ ∑ i ∈ Finset.range τ,
          (τ - 1) • ((1 : ℝ) / ↑(consecutiveGap n i)) := by
        apply Finset.sum_le_sum; intro i _
        exact nsmul_le_nsmul_left (div_nonneg one_pos.le (Nat.cast_nonneg _)) (card_bound i)
    _ = (τ - 1) • ∑ i ∈ Finset.range τ, (1 : ℝ) / ↑(consecutiveGap n i) := by
        rw [Finset.smul_sum]
    _ = (τ - 1) • (∑ i ∈ Finset.range (τ - 1), (1 : ℝ) / ↑(consecutiveGap n i) +
          (1 : ℝ) / ↑(consecutiveGap n (τ - 1))) := by
        congr 1; conv_lhs => rw [show τ = (τ - 1) + 1 by omega]
        exact Finset.sum_range_succ _ _
    _ = (τ - 1) • (consecutivePairsSum n + 0) := by
        unfold consecutivePairsSum; rw [last_zero]
    _ = (τ - 1) • consecutivePairsSum n := by rw [add_zero]
    _ = ↑(τ - 1 : ℕ) * consecutivePairsSum n := nsmul_eq_mul _ _

/-- Unconditional index-based bound: allPairsSum is bounded by the index double sum
    Σ_{0≤i<j<τ} 1/(j-i), independent of the divisor structure of n. Combined with a
    closed-form harmonic estimate Σ_{i,j} 1/(j-i) = Σ_{k=1}^{τ-1} (τ-k)/k ≤ τ·H_{τ-1},
    this yields an unconditional O(τ log τ) bound on allPairsSum. Companion to
    allPairsSum_le_tau_mul_consecutive but does not depend on consecutivePairsSum. -/
theorem allPairsSum_le_indexSum (n : ℕ) (hn : n > 1) :
    allPairsSum n ≤
      ∑ i ∈ Finset.range (numDivisors n),
        ∑ j ∈ Finset.Ioo i (numDivisors n),
          (1 : ℝ) / ((j - i : ℕ) : ℝ) := by
  unfold allPairsSum
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro j hj
  have ⟨hij, hjτ⟩ := Finset.mem_Ioo.mp hj
  exact reciprocal_gap_index_bound n hn hij hjτ

end Erdos884
