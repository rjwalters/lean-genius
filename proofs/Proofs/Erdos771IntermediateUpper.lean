/-
# Erdős Problem #771 — an intermediate-regime upper bound `f_m(n) ≤ ⌊m/2⌋`

Let `f_m(n)` be the largest size of an `m`-avoiding subset of `{1,…,n}` (a subset none of whose
nonempty subsets sums to `m`).  The cluster already pins the exact value at both ends of the range
of `m`:

* **small `m`** (`1 ≤ m ≤ n`):        `f_m(n) = n − ⌈m/2⌉`   (`Erdos771GeneralUpper/LowerBound`);
* **high `m`** (`T(n−1) < m ≤ T(n)`, `T(k) = k(k+1)/2`): `f_m(n) = n − 1`  (`Erdos771HighRegime`).

Everything in the **intermediate regime** `n < m ≤ T(n−1)` is otherwise open — this is the genuine
"matching-number" core, where the value is governed by the maximum number of pairwise-disjoint
representations of `m` inside `{1,…,n}` (pairs, triples, …).

This file proves the **pair-only upper bound for the bottom slice** `n < m ≤ 2n` of that regime.
The mechanism is the same disjoint family of representations used in the small-`m` proof, but with
the singleton block `{m}` (no longer a subset of `{1,…,n}` once `m > n`) dropped and the pair index
restricted so that both endpoints stay in range:

    {i, m−i}   for   m − n ≤ i < ⌈m/2⌉.

These `⌈m/2⌉ − (m − n)` pairs are pairwise disjoint subsets of `{1,…,n}`, each summing to `m`, so an
`m`-avoiding set omits at least one element from each:

    f_m(n) ≤ n − (⌈m/2⌉ − (m − n)) = ⌊m/2⌋      (for `n < m ≤ 2n`).

Combined with the always-valid `f_m(n) ≤ n − 1` from the high regime (every `m ≤ T(n)` is a subset
sum of `{1,…,n}`), this gives `f_m(n) ≤ min(n − 1, ⌊m/2⌋)`, a strict improvement over `n − 1` for
`m ≤ 2n − 3`.

**Tightness.**  The bound is *exact* at the bottom of the regime (machine-checked ground truth:
`f_5(4) = 2 = ⌊5/2⌋`, `f_6(5) = 3 = ⌊6/2⌋`, `f_7(6) = 3`, `f_8(6) = 4`, …), but becomes loose as `m`
approaches `2n`, because triples then contribute additional disjoint representations that the
pair-only family misses (e.g. `f_9(5) = 3 < 4 = ⌊9/2⌋`).  Pinning the exact value throughout
`n < m ≤ T(n−1)` remains the open matching-number problem.

All results are `0`-sorry / `0`-axiom on top of Mathlib, `Erdos771Construction`, and
`Erdos771GeneralUpperBound` (whose `blk` family, `blk_sum`, `blk_disjoint`, and `sum_mem_subsetSums`
are reused verbatim).
-/
import Mathlib
import Proofs.Erdos771Construction
import Proofs.Erdos771GeneralUpperBound

open Finset

namespace Erdos771IntermediateUpper

open Erdos771Construction
open Erdos771GeneralUpperBound

/-! ## The pair blocks stay inside `{1,…,n}` in the intermediate regime -/

/-- For `n < m ≤ 2n` and `m − n ≤ i < ⌈m/2⌉`, the block `blk m i = {i, m − i}` is a subset of
    `{1,…,n}`.  The lower index bound `m − n ≤ i` forces `m − i ≤ n`; the upper bound `i < ⌈m/2⌉`
    together with `m ≤ 2n` forces `i ≤ n`; and `m > n` forces `i ≥ 1`, so the block is the genuine
    two-element pair rather than the singleton `{m}`. -/
theorem blk_subset_high {m i n : ℕ} (hnm : n < m) (hm2n : m ≤ 2 * n)
    (hi1 : m - n ≤ i) (hi2 : i < (m + 1) / 2) : blk m i ⊆ Icc_n n := by
  intro x hx
  rw [mem_blk] at hx
  rw [Icc_n, Finset.mem_Icc]
  rcases hx with ⟨h0, rfl⟩ | ⟨_, rfl | rfl⟩ <;> omega

/-! ## The intermediate-regime upper bound -/

/-- **Intermediate-regime optimality bound for Erdős #771.**  For `1 ≤ n` and `n < m ≤ 2n`, every
    `m`-avoiding subset `S ⊆ {1,…,n}` has

        |S| ≤ n − (⌈m/2⌉ − (m − n)).

    Proof: the `⌈m/2⌉ − (m − n)` pairs `blk m i = {i, m − i}` for `m − n ≤ i < ⌈m/2⌉` are pairwise
    disjoint subsets of `{1,…,n}`, each summing to `m`.  Since `S` avoids `m`, no pair is contained
    in `S`, so each contributes at least one element of the deleted set `D = {1,…,n} ∖ S`.
    Disjointness makes these deletions distinct, so `|D| ≥ ⌈m/2⌉ − (m − n)`. -/
theorem avoid_card_le_intermediate (n m : ℕ) (hn : 1 ≤ n) (hnm : n < m) (hm2n : m ≤ 2 * n)
    (S : Finset ℕ) (hS : S ⊆ Icc_n n) (hav : AvoidSum S m) :
    S.card ≤ n - ((m + 1) / 2 - (m - n)) := by
  set I := Finset.Ico (m - n) ((m + 1) / 2) with hI
  set K := (m + 1) / 2 - (m - n) with hKdef
  have hIcard : I.card = K := by rw [hI, Nat.card_Ico]
  set D : Finset ℕ := (Icc_n n) \ S with hD
  set F : ℕ → Finset ℕ := fun i => blk m i ∩ D with hF
  -- Each pair meets `D` in at least one element.
  have hFpos : ∀ i ∈ I, 1 ≤ (F i).card := by
    intro i hi
    rw [hI, Finset.mem_Ico] at hi
    obtain ⟨hi1, hi2⟩ := hi
    have hnsub : ¬ blk m i ⊆ S := by
      intro hsub
      apply hav
      have := sum_mem_subsetSums S (blk m i) hsub (by rw [blk_sum (by omega) hi2]; omega)
      rwa [blk_sum (by omega) hi2] at this
    rw [Finset.not_subset] at hnsub
    obtain ⟨x, hxblk, hxS⟩ := hnsub
    have hsub : blk m i ⊆ Icc_n n := blk_subset_high hnm hm2n hi1 hi2
    have hxD : x ∈ F i := by
      rw [hF, Finset.mem_inter, hD, Finset.mem_sdiff]
      exact ⟨hxblk, hsub hxblk, hxS⟩
    exact Finset.card_pos.mpr ⟨x, hxD⟩
  -- The `F i` are pairwise disjoint (subsets of disjoint blocks).
  have hFdisj : (↑I : Set ℕ).PairwiseDisjoint F := by
    intro i hi j hj hij
    rw [Finset.mem_coe, hI, Finset.mem_Ico] at hi hj
    exact (blk_disjoint hi.2 hj.2 hij).mono Finset.inter_subset_left Finset.inter_subset_left
  have hbUsub : I.biUnion F ⊆ D := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, _, hxi⟩ := hx
    exact (Finset.inter_subset_right : F i ⊆ D) hxi
  have hcardD : K ≤ D.card := by
    calc K = ∑ _i ∈ I, 1 := by rw [Finset.sum_const, hIcard]; ring
      _ ≤ ∑ i ∈ I, (F i).card := Finset.sum_le_sum hFpos
      _ = (I.biUnion F).card := (Finset.card_biUnion hFdisj).symm
      _ ≤ D.card := Finset.card_le_card hbUsub
  have hcardIcc : (Icc_n n).card = n := by rw [Icc_n, Nat.card_Icc]; omega
  have hcardS_le : S.card ≤ n := hcardIcc ▸ Finset.card_le_card hS
  have hDcard : D.card = n - S.card := by
    rw [hD, Finset.card_sdiff_of_subset hS, hcardIcc]
  omega

/-- **Closed form.**  In the intermediate regime the pair-only bound is exactly `⌊m/2⌋`:
    `n − (⌈m/2⌉ − (m − n)) = ⌊m/2⌋` whenever `n < m ≤ 2n`. -/
theorem avoid_card_le_intermediate_closed (n m : ℕ) (hn : 1 ≤ n) (hnm : n < m) (hm2n : m ≤ 2 * n)
    (S : Finset ℕ) (hS : S ⊆ Icc_n n) (hav : AvoidSum S m) :
    S.card ≤ m / 2 := by
  have h := avoid_card_le_intermediate n m hn hnm hm2n S hS hav
  have hcf : n - ((m + 1) / 2 - (m - n)) = m / 2 := by omega
  omega

/-- **Consistency with the high regime.**  At the very top of the pair-only range, `m = 2n − 1`,
    the bound `⌊m/2⌋` equals `n − 1`, matching `Erdos771HighRegime`; the pair-only family stops
    improving on `n − 1` precisely there (and above). -/
theorem intermediate_top_matches_high (n : ℕ) (hn : 2 ≤ n) (S : Finset ℕ)
    (hS : S ⊆ Icc_n n) (hav : AvoidSum S (2 * n - 1)) :
    S.card ≤ n - 1 := by
  have h := avoid_card_le_intermediate_closed n (2 * n - 1) (by omega) (by omega) (by omega) S hS hav
  have : (2 * n - 1) / 2 = n - 1 := by omega
  omega

end Erdos771IntermediateUpper
