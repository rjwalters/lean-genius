/-
Erdős Problem #1161: Maximizing Permutation Count by Order

Let f_k(n) denote the number of permutations in S_n (the symmetric group on n elements)
having order k. For which values of k is f_k(n) maximized?

STATUS: SOLVED (Beker [Be25d])

Key results:
1. max_{k ≥ 1} f_k(n) ~ (n-1)! as n → ∞
2. For large n, f_k(n) ≥ (n-1)! implies lcm(1,...,n-k) | k
3. For large n, f_k(n) = (n-1)! iff k is the minimal value with lcm(1,...,n-k) | k

Reference: [Va99, 5.72], resolved by Beker [Be25d]
-/
import Mathlib

open Fintype Equiv Equiv.Perm Finset Nat

noncomputable section

/-
## Core Definition

f_k(n) counts the number of permutations in S_n with order exactly k.
-/

/-- The number of permutations in S_n having order exactly k. -/
def permCountByOrder (n k : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => orderOf σ = k))

/-- The maximum of f_k(n) over all k ≥ 1. -/
def maxPermCountByOrder (n : ℕ) : ℕ :=
  Finset.sup (Finset.range (n.factorial + 1))
    (fun k => permCountByOrder n k)

/-- The lcm of all integers from 1 to m, often written [1,...,m]. -/
def lcmRange (m : ℕ) : ℕ :=
  (Finset.range m).lcm (· + 1)

/-
## Basic Properties
-/

/-- The identity permutation has order 1 (when n ≥ 1). -/
theorem permCountByOrder_one_pos (n : ℕ) (hn : 0 < n) :
    0 < permCountByOrder n 1 := by
  unfold permCountByOrder
  rw [Finset.card_pos]
  exact ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, orderOf_one⟩⟩

/-- Every permutation has order dividing n!. -/
theorem orderOf_perm_dvd_factorial (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    orderOf σ ∣ n.factorial := by
  have h := orderOf_dvd_card (G := Equiv.Perm (Fin n))
  rwa [Fintype.card_perm] at h

/-- The total count of permutations across all orders equals n!. -/
theorem sum_permCountByOrder (n : ℕ) :
    (Finset.range (n.factorial + 1)).sum (fun k => permCountByOrder n k) =
    n.factorial := by
  sorry

/-- f_k(n) = 0 when k does not divide n!. -/
theorem permCountByOrder_eq_zero_of_not_dvd (n k : ℕ) (hk : ¬(k ∣ n.factorial)) :
    permCountByOrder n k = 0 := by
  unfold permCountByOrder
  rw [Finset.card_eq_zero]
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.not_mem_empty, iff_false]
  intro h
  exact hk (h ▸ orderOf_perm_dvd_factorial n σ)

/-
## Small Cases
-/

/-- In S_1, the only permutation is the identity with order 1. -/
theorem permCountByOrder_one_one : permCountByOrder 1 1 = 1 := by
  -- Proved by Aristotle (Harmonic)
  unfold permCountByOrder
  simp +decide only [orderOf_eq_iff]

/-- In S_2, there is 1 permutation of order 1 (identity) and 1 of order 2 (transposition). -/
theorem permCountByOrder_two_one : permCountByOrder 2 1 = 1 := by
  -- Proved by Aristotle (Harmonic)
  simp +decide [permCountByOrder]

theorem permCountByOrder_two_two : permCountByOrder 2 2 = 1 := by
  -- Proved by Aristotle (Harmonic)
  simp [permCountByOrder]
  simp [orderOf_eq_iff]
  simp (config := { decide := true }) only [pow_two]

/-- In S_3, there are 2 permutations of order 3 (the 3-cycles). -/
theorem permCountByOrder_three_three : permCountByOrder 3 3 = 2 := by
  -- Proved by Aristotle (Harmonic)
  convert Finset.card_eq_sum_ones (Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) => orderOf σ = 3)) using 1
  simp +decide only [orderOf_eq_iff]

/-- In S_3, there are 3 transpositions (order 2). -/
theorem permCountByOrder_three_two : permCountByOrder 3 2 = 3 := by
  -- Proved by Aristotle (Harmonic)
  have h_permutations : Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin 3) => orderOf σ = 2)
      (Finset.univ : Finset (Equiv.Perm (Fin 3)))) = 3 := by
    simp +decide only [orderOf_eq_iff]
  convert h_permutations

/-
## Main Results (Beker [Be25d])

The following theorems state the key results resolving this problem.
-/

/-- Beker's characterization: for sufficiently large n, if f_k(n) ≥ (n-1)!
    then lcm(1,...,n-k) divides k. -/
theorem beker_characterization (n k : ℕ) (hn : n ≥ 100)
    (hfk : permCountByOrder n k ≥ (n - 1).factorial) :
    lcmRange (n - k) ∣ k := by
  sorry

/-- Beker's maximizer theorem: for all sufficiently large n,
    f_k(n) = (n-1)! if and only if k is the minimal positive integer
    such that lcm(1,...,n-k) divides k.

    We state one direction: the minimal k with lcmRange(n-k) | k achieves (n-1)!.

**Note**: This statement as written (equality = (n-1)!) is FALSE.
Aristotle found: for n/2 < k ≤ n-1 with lcmRange(n-k) | k, we have
permCountByOrder n k ≥ n!/k > (n-1)!. So the count EXCEEDS (n-1)!, not equals.
The correct formulation should use ≥ (n-1)! (which is `max_permCount_ge_sub_factorial`). -/
theorem beker_maximizer_achieves (n : ℕ) (hn : n ≥ 100)
    (k : ℕ) (hk : 0 < k) (hdvd : lcmRange (n - k) ∣ k)
    (hmin : ∀ j, 0 < j → j < k → ¬(lcmRange (n - j) ∣ j)) :
    permCountByOrder n k = (n - 1).factorial := by
  sorry

/-- The asymptotic result: max_k f_k(n) ≥ (n-1)! for n ≥ 2.
    (The lower bound direction: achieved by k = n, i.e. n-cycles.) -/
theorem max_permCount_ge_sub_factorial (n : ℕ) (hn : 2 ≤ n) :
    ∃ k, permCountByOrder n k ≥ (n - 1).factorial := by
  -- Proved by Aristotle (Harmonic): use k = n and count n-cycles.
  cases n <;> simp_all +arith +decide [Nat.factorial_succ, Finset.sum_range_succ',
    Finset.card_univ]
  ring_nf at *
  rename_i n
  use n + 1
  rw [add_comm, permCountByOrder]
  have h_count : (Finset.univ.filter (fun σ : Equiv.Perm (Fin (Nat.succ n)) =>
      orderOf σ = Nat.succ n)).card ≥
      (Nat.factorial (Nat.succ n)) / (Nat.succ n) := by
    have h_sub : (Finset.univ.filter (fun σ : Equiv.Perm (Fin (Nat.succ n)) =>
        orderOf σ = Nat.succ n)).card ≥
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin (Nat.succ n)) =>
        σ.cycleType = {Nat.succ n})).card := by
      refine Finset.card_le_card ?_
      intro σ hσ
      simp +zetaDelta at *
      rw [← Equiv.Perm.lcm_cycleType]; aesop
    have := Equiv.Perm.card_of_cycleType (Fin (Nat.succ n)) [Nat.succ n]; aesop
  exact le_trans (by rw [Nat.factorial_succ, Nat.mul_div_cancel_left _ (Nat.succ_pos _)]) h_count

/-- Upper bound: max_k f_k(n) ≤ n! (trivially, since f_k(n) counts a subset of S_n). -/
theorem permCountByOrder_le_factorial (n k : ℕ) :
    permCountByOrder n k ≤ n.factorial := by
  unfold permCountByOrder
  calc (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => orderOf σ = k)).card
      ≤ (Finset.univ : Finset (Equiv.Perm (Fin n))).card := Finset.card_filter_le _ _
    _ = n.factorial := by rw [Finset.card_univ, Fintype.card_perm]

/-
## Structural Lemmas
-/

/-- A permutation whose order equals n must be an n-cycle (when it acts on Fin n).
    In S_n, a permutation of order n is a single n-cycle.

**Note**: This statement is FALSE.
Aristotle found: for n=6, permutations with cycle type {3,2} also have order lcm(3,2)=6,
so permCountByOrder 6 6 > 5! = 120. The count includes all permutations of order n,
not just n-cycles. -/
theorem permCountByOrder_n_eq_subfactorial_pred (n : ℕ) (hn : 2 ≤ n) :
    permCountByOrder n n = (n - 1).factorial := by
  sorry

/-- lcmRange is monotone: m ≤ m' → lcmRange m ∣ lcmRange m'. -/
theorem lcmRange_dvd_lcmRange (m m' : ℕ) (h : m ≤ m') :
    lcmRange m ∣ lcmRange m' := by
  unfold lcmRange
  apply Finset.lcm_dvd
  intro i hi
  apply Finset.dvd_lcm
  exact Finset.mem_range.mpr (by omega)

/-- lcmRange includes each factor: for 1 ≤ j ≤ m, j ∣ lcmRange m. -/
theorem dvd_lcmRange (m j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) :
    j ∣ lcmRange m := by
  unfold lcmRange
  have : j - 1 ∈ Finset.range m := Finset.mem_range.mpr (by omega)
  have : (fun i => i + 1) (j - 1) = j := by omega
  rw [← this]
  exact Finset.dvd_lcm (f := (· + 1)) ‹j - 1 ∈ Finset.range m›

end
