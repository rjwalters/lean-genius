/-
# Erdős Problem #771 — the general optimality bound `f_m(n) ≤ n − ⌈m/2⌉`

The self-contained `Erdos771Construction.lean` pins, one value of `m` at a time, the largest
`m`-avoiding subset of `{1,…,n}`:

    m = 1, 2 → n − 1,     m = 3, 4 → n − 2      (the `n − ⌈m/2⌉` staircase).

This file proves the **general upper bound behind every rung at once**: for `1 ≤ m ≤ n`, any
`S ⊆ {1,…,n}` avoiding the subset sum `m` has

    |S| ≤ n − ⌈m/2⌉.

The mechanism is a *disjoint family of representations* of `m`.  The `⌈m/2⌉` sets

    {m},   {1, m−1},   {2, m−2},   …,   {i, m−i},   …   (i < ⌈m/2⌉)

are pairwise disjoint subsets of `{1,…,n}`, each summing to `m`.  An `m`-avoiding set cannot
contain any of them, so it must **omit at least one element from each** — and because the blocks
are disjoint, these are `⌈m/2⌉` distinct omitted elements of `{1,…,n}`.  Hence at least `⌈m/2⌉`
elements are deleted, giving `|S| ≤ n − ⌈m/2⌉`.

This subsumes the four hand-proved cases (`avoid_one_card_le` … `avoid_four_card_le`) uniformly,
and settles the whole "small-`m`" regime `m ≤ n`.  The deep asymptotics
`f(n) = (1/2 + o(1)) n / log n` are unaffected and remain out of scope.

All results are `0`-sorry / `0`-axiom on top of Mathlib and `Erdos771Construction`.
-/
import Mathlib
import Proofs.Erdos771Construction

open Finset

namespace Erdos771GeneralUpperBound

open Erdos771Construction

/-! ## A general subset-sum membership helper -/

/-- If `A ⊆ S` has positive sum, that sum is a (positive) subset sum of `S`.  Generalises
    `subsetSums_self_mem` from singletons to arbitrary subsets. -/
theorem sum_mem_subsetSums (S A : Finset ℕ) (hA : A ⊆ S) (hpos : 0 < ∑ a ∈ A, a) :
    (∑ a ∈ A, a) ∈ subsetSums S := by
  rw [subsetSums, Finset.mem_filter, Finset.mem_image]
  exact ⟨⟨A, Finset.mem_powerset.mpr hA, rfl⟩, hpos⟩

/-! ## The disjoint family of representations of `m` -/

/-- The `i`-th representation block of `m`: `{m}` for `i = 0`, and the pair `{i, m−i}` for
    `i ≥ 1`.  For `1 ≤ i < ⌈m/2⌉` this is a two-element subset of `{1,…,m−1}` summing to `m`. -/
def blk (m i : ℕ) : Finset ℕ := if i = 0 then {m} else {i, m - i}

theorem mem_blk {m i x : ℕ} :
    x ∈ blk m i ↔ (i = 0 ∧ x = m) ∨ (i ≠ 0 ∧ (x = i ∨ x = m - i)) := by
  unfold blk
  split_ifs with h
  · simp [h]
  · simp [h, Finset.mem_insert, Finset.mem_singleton]

/-- Each block sums to `m` (for `1 ≤ m` and `i < ⌈m/2⌉`, so the pair is genuinely two distinct
    positive elements). -/
theorem blk_sum {m i : ℕ} (_hm : 1 ≤ m) (hi : i < (m + 1) / 2) :
    ∑ a ∈ blk m i, a = m := by
  unfold blk
  split_ifs with h
  · simp
  · have hi0 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr h
    have hne : i ≠ m - i := by omega
    rw [Finset.sum_pair hne]
    omega

/-- Every block lies inside `{1,…,n}` when `m ≤ n`. -/
theorem blk_subset {m i n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (hi : i < (m + 1) / 2) :
    blk m i ⊆ Icc_n n := by
  intro x hx
  rw [mem_blk] at hx
  rw [Icc_n, Finset.mem_Icc]
  rcases hx with ⟨_, rfl⟩ | ⟨h0, rfl | rfl⟩ <;> omega

/-- The blocks are pairwise disjoint over `i < ⌈m/2⌉`. -/
theorem blk_disjoint {m i j : ℕ} (hi : i < (m + 1) / 2) (hj : j < (m + 1) / 2)
    (hij : i ≠ j) : Disjoint (blk m i) (blk m j) := by
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rw [mem_blk] at hxi hxj
  omega

/-! ## The general upper bound -/

/-- **General optimality bound for Erdős #771 (small-`m` regime).**  For `1 ≤ m ≤ n`, every
    `m`-avoiding subset of `{1,…,n}` has size at most `n − ⌈m/2⌉`.

    Proof: the `⌈m/2⌉` blocks `blk m 0, …, blk m (⌈m/2⌉−1)` are pairwise-disjoint subsets of
    `{1,…,n}`, each summing to `m`.  Since `S` avoids `m`, no block is contained in `S`, so each
    block contributes at least one element of the deleted set `D = {1,…,n} ∖ S`.  Disjointness
    turns these into `⌈m/2⌉` distinct deletions, so `|D| ≥ ⌈m/2⌉` and `|S| = n − |D| ≤ n − ⌈m/2⌉`. -/
theorem avoid_card_le_general (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n) (S : Finset ℕ)
    (hS : S ⊆ Icc_n n) (hav : AvoidSum S m) :
    S.card ≤ n - (m + 1) / 2 := by
  set K := (m + 1) / 2 with hK
  set D : Finset ℕ := (Icc_n n) \ S with hD
  -- The intersections `blk m i ∩ D`, one per block.
  set F : ℕ → Finset ℕ := fun i => blk m i ∩ D with hF
  -- Each block meets `D` in at least one element.
  have hFpos : ∀ i ∈ Finset.range K, 1 ≤ (F i).card := by
    intro i hi
    rw [Finset.mem_range] at hi
    -- `blk m i ⊄ S`, else its sum `m` would be a subset sum of `S`.
    have hnsub : ¬ blk m i ⊆ S := by
      intro hsub
      apply hav
      have := sum_mem_subsetSums S (blk m i) hsub (by rw [blk_sum hm hi]; omega)
      rwa [blk_sum hm hi] at this
    -- So some `x ∈ blk m i` with `x ∉ S`; since `blk ⊆ Icc_n n`, `x ∈ D`.
    rw [Finset.not_subset] at hnsub
    obtain ⟨x, hxblk, hxS⟩ := hnsub
    have hxD : x ∈ F i := by
      rw [hF, Finset.mem_inter, hD, Finset.mem_sdiff]
      exact ⟨hxblk, blk_subset hm hmn hi hxblk, hxS⟩
    exact Finset.card_pos.mpr ⟨x, hxD⟩
  -- The `F i` are pairwise disjoint (subsets of disjoint blocks).
  have hFdisj : (↑(Finset.range K) : Set ℕ).PairwiseDisjoint F := by
    intro i hi j hj hij
    rw [Finset.mem_coe, Finset.mem_range] at hi hj
    exact (blk_disjoint hi hj hij).mono Finset.inter_subset_left Finset.inter_subset_left
  -- Their disjoint union sits inside `D`, so `|D| ≥ Σ |F i| ≥ K`.
  have hbUsub : (Finset.range K).biUnion F ⊆ D := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, _, hxi⟩ := hx
    exact (Finset.inter_subset_right : F i ⊆ D) hxi
  have hcardD : K ≤ D.card := by
    calc K = ∑ _i ∈ Finset.range K, 1 := by rw [Finset.sum_const, Finset.card_range]; ring
      _ ≤ ∑ i ∈ Finset.range K, (F i).card := Finset.sum_le_sum hFpos
      _ = ((Finset.range K).biUnion F).card := (Finset.card_biUnion hFdisj).symm
      _ ≤ D.card := Finset.card_le_card hbUsub
  -- `|D| = n − |S|`, and `|S| ≤ n`, so `|S| ≤ n − K`.
  have hcardIcc : (Icc_n n).card = n := by rw [Icc_n, Nat.card_Icc]; omega
  have hcardS_le : S.card ≤ n := hcardIcc ▸ Finset.card_le_card hS
  have hDcard : D.card = n - S.card := by
    rw [hD, Finset.card_sdiff_of_subset hS, hcardIcc]
  omega

/-- **Consistency check.**  The general bound reproduces the four hand-proved rungs:
    at `m = 1, 2` it gives `n − 1`, at `m = 3, 4` it gives `n − 2`. -/
theorem avoid_card_le_general_matches_ladder (n : ℕ) (S : Finset ℕ) (hS : S ⊆ Icc_n n) :
    (2 ≤ n → AvoidSum S 2 → S.card ≤ n - 1) ∧
    (4 ≤ n → AvoidSum S 4 → S.card ≤ n - 2) := by
  refine ⟨fun hn hav => ?_, fun hn hav => ?_⟩
  · have := avoid_card_le_general n 2 (by norm_num) hn S hS hav
    simpa using this
  · have := avoid_card_le_general n 4 (by norm_num) hn S hS hav
    simpa using this

end Erdos771GeneralUpperBound
