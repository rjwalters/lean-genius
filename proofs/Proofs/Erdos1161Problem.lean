/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d19d476c-6695-4f8a-be92-c5e0a57c4d3c

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem sum_permCountByOrder (n : ℕ) :
    (Finset.range (n.factorial + 1)).sum (fun k => permCountByOrder n k) =
    n.factorial

- theorem permCountByOrder_one_one : permCountByOrder 1 1 = 1

- theorem permCountByOrder_two_one : permCountByOrder 2 1 = 1

- theorem permCountByOrder_two_two : permCountByOrder 2 2 = 1

- theorem permCountByOrder_three_three : permCountByOrder 3 3 = 2

- theorem permCountByOrder_three_two : permCountByOrder 3 2 = 3

- theorem max_permCount_ge_sub_factorial (n : ℕ) (hn : 2 ≤ n) :
    ∃ k, permCountByOrder n k ≥ (n - 1).factorial

The following was negated by Aristotle:

- theorem permCountByOrder_n_eq_subfactorial_pred (n : ℕ) (hn : 2 ≤ n) :
    permCountByOrder n n = (n - 1).factorial

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

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
  have h : orderOf σ ∣ Fintype.card (Equiv.Perm (Fin n)) := orderOf_dvd_card
  simp only [Fintype.card_perm, Fintype.card_fin] at h
  exact h

/-- The total count of permutations across all orders equals n!. -/
theorem sum_permCountByOrder (n : ℕ) :
    (Finset.range (n.factorial + 1)).sum (fun k => permCountByOrder n k) =
    n.factorial := by
  unfold permCountByOrder;
  rw [ ← Finset.card_eq_sum_card_fiberwise ];
  · simp +decide [ Finset.card_univ, Fintype.card_perm ];
  · intro σ hσ;
    simp +zetaDelta at *;
    exact Nat.lt_succ_of_le ( orderOf_le_card_univ.trans ( by simp +decide [ Fintype.card_perm ] ) )

/-- f_k(n) = 0 when k does not divide n!. -/
theorem permCountByOrder_eq_zero_of_not_dvd (n k : ℕ) (hk : ¬(k ∣ n.factorial)) :
    permCountByOrder n k = 0 := by
  unfold permCountByOrder
  rw [Finset.card_eq_zero]
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  intro h
  exact hk (h ▸ orderOf_perm_dvd_factorial n σ)

/-
## Small Cases
-/

/-- In S_1, the only permutation is the identity with order 1. -/
theorem permCountByOrder_one_one : permCountByOrder 1 1 = 1 := by
  unfold permCountByOrder;
  simp +decide [ orderOf_eq_one_iff ]

/-- In S_2, there is 1 permutation of order 1 (identity) and 1 of order 2 (transposition). -/
theorem permCountByOrder_two_one : permCountByOrder 2 1 = 1 := by
  unfold permCountByOrder;
  simp +decide only [orderOf_eq_one_iff]

theorem permCountByOrder_two_two : permCountByOrder 2 2 = 1 := by
  -- In S_2, there is exactly one permutation of order 2, which is the transposition (1 2).
  simp [permCountByOrder];
  -- Let's calculate the set of permutations in $S_2$ with order 2.
  simp +decide [orderOf_eq_iff]

/-- In S_3, there are 2 permutations of order 3 (the 3-cycles). -/
theorem permCountByOrder_three_three : permCountByOrder 3 3 = 2 := by
  unfold permCountByOrder;
  simp +decide only [orderOf_eq_iff]

/-- In S_3, there are 3 transpositions (order 2). -/
theorem permCountByOrder_three_two : permCountByOrder 3 2 = 3 := by
  unfold permCountByOrder;
  simp +decide only [orderOf_eq_iff]

/-
## Main Results (Beker [Be25d])

Beker's characterization and maximizer theorems are deep combinatorial results
from [Be25d]. They are not provable from Mathlib and are stated here as axioms
to capture the formal problem resolution.
-/

/-- Beker's characterization: for sufficiently large n, if f_k(n) ≥ (n-1)!
    then lcm(1,...,n-k) divides k. [Beker, Be25d] -/
/-- Beker's maximizer theorem: for all sufficiently large n,
    f_k(n) = (n-1)! if and only if k is the minimal positive integer
    such that lcm(1,...,n-k) divides k.
    We state one direction: the minimal k with lcmRange(n-k) | k achieves (n-1)!.
    [Beker, Be25d] -/
/-- max_k f_k(n) ≥ (n-1)! for n ≥ 2.
    Direct proof: the (n-1)! many n-cycles in S_n each have order n.
    This proof does NOT depend on Beker's axioms above. -/
theorem max_permCount_ge_sub_factorial (n : ℕ) (hn : 2 ≤ n) :
    ∃ k, permCountByOrder n k ≥ (n - 1).factorial := by
  -- Take k = n: every n-cycle has order n, and there are (n-1)! of them
  refine ⟨n, ?_⟩
  unfold permCountByOrder
  -- {σ | cycleType σ = {n}} ⊆ {σ | orderOf σ = n}
  have h_le : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ.cycleType = {n})).card ≤
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => orderOf σ = n)).card := by
    apply Finset.card_le_card
    intro σ hσ
    have := Equiv.Perm.lcm_cycleType σ; aesop
  -- |{σ | cycleType σ = {n}}| = n!/n
  have h_ct : (Finset.univ.filter
      (fun σ : Equiv.Perm (Fin n) => σ.cycleType = {n})).card = n.factorial / n := by
    have := Equiv.Perm.card_of_cycleType (Fin n) [n]; aesop
  -- n!/n = (n-1)!
  have h_div : n.factorial / n = (n - 1).factorial := by
    have : n.factorial = n * (n - 1).factorial := by
      have := Nat.factorial_succ (n - 1)
      rwa [show n - 1 + 1 = n from by omega] at this
    rw [this, Nat.mul_div_cancel_left _ (by omega : 0 < n)]
  linarith

/-- Upper bound: max_k f_k(n) ≤ n! (trivially, since f_k(n) counts a subset of S_n). -/
theorem permCountByOrder_le_factorial (n k : ℕ) :
    permCountByOrder n k ≤ n.factorial := by
  unfold permCountByOrder
  calc (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => orderOf σ = k)).card
      ≤ (Finset.univ : Finset (Equiv.Perm (Fin n))).card := Finset.card_filter_le _ _
    _ = n.factorial := by rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

/-
## Structural Lemmas

Note: The statement `permCountByOrder n n = (n-1)!` does NOT hold for composite n.
Counterexample: permCountByOrder 6 6 = 240 ≠ 120 = 5!.
At n = 6, both 6-cycles (120 perms) and (3,2,1)-type permutations (120 perms) have order 6.
The correct statement holds when n is prime (see `permCountByOrder_prime_self`).
-/

/-- For prime p, a permutation of Fin p with order p must be a p-cycle.
    Since p is prime, the only partition of cycle lengths with lcm = p is {p}. -/
private lemma cycleType_eq_singleton_of_prime_order {p : ℕ} (hp : p.Prime)
    (σ : Equiv.Perm (Fin p)) (h_ord : orderOf σ = p) :
    σ.cycleType = {p} := by
  -- Every element of cycleType divides p and is ≥ 2, so equals p (since p is prime)
  have h_eq_p : ∀ n ∈ σ.cycleType, n = p := by
    intro n hn
    have h_dvd : n ∣ p := h_ord ▸ Equiv.Perm.dvd_of_mem_cycleType hn
    have h_ge : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    exact (hp.eq_one_or_self_of_dvd n h_dvd).resolve_left (by omega)
  -- Sum of cycleType = support.card ≤ p
  have h_sum_le : σ.cycleType.sum ≤ p := by
    rw [Equiv.Perm.sum_cycleType]
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Fintype.card_fin p)
  -- σ ≠ 1 (since orderOf σ = p ≥ 2)
  have h_ne : σ ≠ 1 := by
    intro h; rw [h, orderOf_one] at h_ord; exact absurd h_ord hp.one_lt.ne
  -- cycleType is nonempty (σ has at least one non-trivial cycle)
  have h_nonempty : σ.cycleType ≠ 0 := by
    intro h
    have h_card : σ.support.card = 0 := by rw [← Equiv.Perm.sum_cycleType]; simp [h]
    have h_empty : σ.support = ∅ := Finset.card_eq_zero.mp h_card
    simp only [Finset.eq_empty_iff_forall_not_mem, Equiv.Perm.mem_support, not_not] at h_empty
    exact h_ne (Equiv.Perm.ext (fun x => by simp [h_empty x]))
  -- Get an element from the nonempty multiset
  have ⟨a, ha⟩ : ∃ a, a ∈ σ.cycleType := by
    by_contra h; push_neg at h
    exact h_nonempty (Multiset.eq_zero_of_forall_notMem h)
  have ha_eq : a = p := h_eq_p a ha
  -- Express cycleType as a ::ₘ rest
  set rest := σ.cycleType.erase a
  have h_cons : σ.cycleType = a ::ₘ rest := (Multiset.cons_erase ha).symm
  -- Show rest must be empty (otherwise sum > p)
  suffices rest = 0 by rw [h_cons, this, ha_eq]; rfl
  by_contra h_rest
  have ⟨b, hb⟩ : ∃ b, b ∈ rest := by
    by_contra h; push_neg at h
    exact h_rest (Multiset.eq_zero_of_forall_notMem h)
  have hb_eq : b = p := h_eq_p b (h_cons ▸ Multiset.mem_cons.mpr (Or.inr hb))
  -- b ≤ rest.sum (since b ∈ rest, rest.sum = b + (rest.erase b).sum ≥ b)
  have hb_le : b ≤ rest.sum := by
    calc b ≤ b + (rest.erase b).sum := Nat.le_add_right b _
      _ = rest.sum := by rw [← Multiset.sum_cons, Multiset.cons_erase hb]
  -- a + b ≤ a + rest.sum = σ.cycleType.sum ≤ p
  have h_ge : a + b ≤ σ.cycleType.sum := by
    rw [h_cons, Multiset.sum_cons]; exact Nat.add_le_add_left hb_le a
  linarith [ha_eq, hb_eq, hp.one_lt]

/-- For prime p, the number of permutations in S_p with order exactly p equals (p-1)!.
    The only permutations of S_p with order p are the p-cycles, and there are (p-1)! of them.

    This does NOT generalize to composite n. Counterexample: permCountByOrder 6 6 = 240 ≠ 5!.
    For composite n, permutations with multiple cycle types can achieve order n. -/
theorem permCountByOrder_prime_self (p : ℕ) (hp : p.Prime) :
    permCountByOrder p p = (p - 1).factorial := by
  unfold permCountByOrder
  -- {σ | orderOf σ = p} = {σ | cycleType σ = {p}} for prime p
  have h_eq : (Finset.univ.filter (fun σ : Equiv.Perm (Fin p) => orderOf σ = p)) =
              (Finset.univ.filter (fun σ : Equiv.Perm (Fin p) => σ.cycleType = {p})) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨cycleType_eq_singleton_of_prime_order hp σ,
           fun h => by rw [← Equiv.Perm.lcm_cycleType, h]; simp⟩
  rw [h_eq]
  -- Count p-cycles = p!/p = (p-1)!
  have h_count : (Finset.univ.filter
      (fun σ : Equiv.Perm (Fin p) => σ.cycleType = {p})).card = p.factorial / p := by
    have h2 : 2 ≤ p := hp.two_le
    have := Equiv.Perm.card_of_cycleType (Fin p) [p]
    simp_all
  rw [h_count]
  -- p! / p = (p-1)!  since p! = p * (p-1)!
  have h_pos : 0 < p := hp.pos
  have h_fact : p.factorial = p * (p - 1).factorial := by
    have := Nat.factorial_succ (p - 1)
    rwa [show p - 1 + 1 = p from by omega] at this
  rw [h_fact, Nat.mul_div_cancel_left _ h_pos]

/-- lcmRange is monotone: m ≤ m' → lcmRange m ∣ lcmRange m'. -/
theorem lcmRange_dvd_lcmRange (m m' : ℕ) (h : m ≤ m') :
    lcmRange m ∣ lcmRange m' := by
  unfold lcmRange
  apply Finset.lcm_dvd
  intro i hi
  apply Finset.dvd_lcm
  exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) h)

/-- lcmRange includes each factor: for 1 ≤ j ≤ m, j ∣ lcmRange m. -/
theorem dvd_lcmRange (m j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) :
    j ∣ lcmRange m := by
  unfold lcmRange
  have : j - 1 ∈ Finset.range m := Finset.mem_range.mpr (by omega)
  have : (fun i => i + 1) (j - 1) = j := by dsimp; omega
  rw [← this]
  exact Finset.dvd_lcm (f := (· + 1)) ‹j - 1 ∈ Finset.range m›

end