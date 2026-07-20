/-
# Erdős Problem #771 — the high-`m` plateau: value `n − 1` on `T(n−1) < m ≤ T(n)`

Let `f_m(n)` be the maximum size of a subset `S ⊆ {1,…,n}` no nonempty subset of which
sums to `m`.  The cluster already pins the two extreme regimes exactly:

* small `m` (`1 ≤ m ≤ n`): `f_m(n) = n − ⌈m/2⌉` (`Erdos771GeneralUpperBound`/`…LowerBound`);
* the single boundary point `m = T(n) := ∑_{a=1}^{n} a` gives `f_m(n) = n − 1`
  (`maxAvoidingSize_total_boundary`, PR #39104).

Everything in the **intermediate regime** `n < m ≤ T(n)` was otherwise open.  This file
resolves the *top interval* of that regime in one clean statement:

> **For `T(n−1) < m ≤ T(n)` (equivalently the `n` largest representable targets), the exact
> maximum is `n − 1`.**

* **Attainment.**  The witness `{1,…,n−1}` has total sum `T(n−1) < m`, so *no* subset of it
  can reach `m`; it has size `n − 1`.
* **Optimality.**  The subset sums of `{1,…,n}` cover the whole interval `[0, T(n)]`
  (`exists_subset_sum_Icc`, the arithmetic core proved here by a greedy induction), so the
  full set `{1,…,n}` itself realizes `m` — hence any `m`-avoiding set is a *proper* subset and
  has size `≤ n − 1`.

This subsumes the single point `m = T(n)` (`hmlow` is then `T(n−1) < T(n)`, true because the
extra term is `n ≥ 1`) and extends it to the whole top interval `(T(n−1), T(n)]`, which for
`n = 4` is exactly `{7,8,9,10}` — matching the hand computation that `f_m(4) = 3` there while
`f_5(4) = 2` (that lower point lies below `T(3) = 6` and stays genuinely harder).

All results are `0`-sorry / `0`-axiom on top of Mathlib and `Erdos771Construction`.
-/
import Mathlib
import Proofs.Erdos771Construction

open Finset

namespace Erdos771HighRegime

open Erdos771Construction

/-- **Arithmetic core — coverage of `[0, T(n)]` by subset sums of `{1,…,n}`.**
Every `m ≤ ∑_{a=1}^{n} a` is realized as `∑ A` for some `A ⊆ {1,…,n}`.  Greedy induction on
`n`: if `m` fits inside `{1,…,n−1}` use the inductive witness; otherwise include `n` and
represent the remainder `m − n` (which is `≤ T(n−1)`) inductively. -/
theorem exists_subset_sum_Icc (n : ℕ) :
    ∀ m, m ≤ ∑ x ∈ Finset.Icc 1 n, x → ∃ A ⊆ Finset.Icc 1 n, ∑ x ∈ A, x = m := by
  induction n with
  | zero =>
    intro m hm
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty] at hm
    exact ⟨∅, Finset.empty_subset _, by simp [Nat.le_zero.mp hm]⟩
  | succ k ih =>
    intro m hm
    have hsplit : ∑ x ∈ Finset.Icc 1 (k + 1), x = (∑ x ∈ Finset.Icc 1 k, x) + (k + 1) :=
      Finset.sum_Icc_succ_top (by omega) (fun x => x)
    by_cases hmk : m ≤ ∑ x ∈ Finset.Icc 1 k, x
    · obtain ⟨A, hA, hAsum⟩ := ih m hmk
      exact ⟨A, hA.trans (Finset.Icc_subset_Icc_right (by omega)), hAsum⟩
    · push Not at hmk
      -- `k ≤ T(k)`, so `m > T(k) ≥ k` forces `m ≥ k + 1` (needed to peel off `k + 1`).
      have hk : k ≤ ∑ x ∈ Finset.Icc 1 k, x := by
        rcases Nat.eq_zero_or_pos k with rfl | hpos
        · simp
        · exact Finset.single_le_sum (f := fun x => x) (fun _ _ => Nat.zero_le _)
            (Finset.mem_Icc.mpr ⟨hpos, le_refl k⟩)
      have hle : m - (k + 1) ≤ ∑ x ∈ Finset.Icc 1 k, x := by omega
      obtain ⟨A, hA, hAsum⟩ := ih (m - (k + 1)) hle
      have hnotin : (k + 1) ∉ A := by
        intro h
        have := hA h
        rw [Finset.mem_Icc] at this
        omega
      refine ⟨insert (k + 1) A, ?_, ?_⟩
      · intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · rw [Finset.mem_Icc]; omega
        · exact Finset.Icc_subset_Icc_right (by omega) (hA hx)
      · rw [Finset.sum_insert hnotin, hAsum]
        omega

/-- **Optimality (high-`m` regime).**  For `1 ≤ m ≤ T(n)`, any `m`-avoiding subset of `{1,…,n}`
has size `≤ n − 1`.  Because `exists_subset_sum_Icc` realizes `m` inside the *full* set
`{1,…,n}`, the full set is not `m`-avoiding, so an `m`-avoiding `S` is a proper subset. -/
theorem avoid_high_card_le (n m : ℕ) (hm1 : 1 ≤ m) (hmT : m ≤ ∑ x ∈ Icc_n n, x)
    (S : Finset ℕ) (hS : S ⊆ Icc_n n) (hav : AvoidSum S m) : S.card ≤ n - 1 := by
  -- `m` is a positive subset sum of `{1,…,n}`.
  obtain ⟨A, hA, hAsum⟩ := exists_subset_sum_Icc n m hmT
  have hmInSums : m ∈ subsetSums (Icc_n n) := by
    rw [subsetSums, Finset.mem_filter, Finset.mem_image]
    exact ⟨⟨A, Finset.mem_powerset.mpr hA, hAsum⟩, by omega⟩
  by_contra hcard
  push Not at hcard
  -- `S.card > n − 1` together with `S ⊆ {1,…,n}` forces `S = {1,…,n}`.
  have hSeq : S = Icc_n n :=
    Finset.eq_of_subset_of_card_le hS (by rw [Icc_n, Nat.card_Icc]; omega)
  rw [hSeq] at hav
  exact hav hmInSums

/-- **Attainment (high-`m` regime).**  Whenever `m > T(n−1) = ∑_{a=1}^{n−1} a`, the witness
`{1,…,n−1}` avoids `m`: its every subset sum is `≤ T(n−1) < m`.  It has size `n − 1`. -/
theorem exists_avoid_high_card (n m : ℕ) (hn : 1 ≤ n)
    (hmlow : ∑ x ∈ Icc_n (n - 1), x < m) :
    ∃ S ⊆ Icc_n n, AvoidSum S m ∧ S.card = n - 1 := by
  refine ⟨Icc_n (n - 1), Finset.Icc_subset_Icc_right (by omega), ?_, ?_⟩
  · -- `AvoidSum`: no nonempty subset of `{1,…,n−1}` sums to `m`.
    intro hmem
    rw [subsetSums, Finset.mem_filter, Finset.mem_image] at hmem
    obtain ⟨⟨A, hApow, hAsum⟩, _⟩ := hmem
    rw [Finset.mem_powerset] at hApow
    have hAle : ∑ x ∈ A, x ≤ ∑ x ∈ Icc_n (n - 1), x :=
      Finset.sum_le_sum_of_subset hApow
    omega
  · rw [Icc_n, Nat.card_Icc]; omega

/-- **Exact maximum on the high-`m` plateau.**  For `1 ≤ n` and `T(n−1) < m ≤ T(n)` (with
`T(k) = ∑_{a=1}^{k} a`), the largest `m`-avoiding subset of `{1,…,n}` has size *exactly*
`n − 1`: one of that size exists, and none is larger.  This extends the single boundary
point `m = T(n)` to the whole top interval `(T(n−1), T(n)]` of the intermediate regime. -/
theorem high_regime_exact (n m : ℕ) (hn : 1 ≤ n)
    (hmlow : ∑ x ∈ Icc_n (n - 1), x < m) (hmT : m ≤ ∑ x ∈ Icc_n n, x) :
    (∃ S ⊆ Icc_n n, AvoidSum S m ∧ S.card = n - 1) ∧
      (∀ S ⊆ Icc_n n, AvoidSum S m → S.card ≤ n - 1) := by
  have hm1 : 1 ≤ m := by omega
  exact ⟨exists_avoid_high_card n m hn hmlow,
    fun S hS hav => avoid_high_card_le n m hm1 hmT S hS hav⟩

end Erdos771HighRegime
