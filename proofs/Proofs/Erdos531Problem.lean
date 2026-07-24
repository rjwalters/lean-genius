/-
Erdős Problem #531: Folkman's Theorem - Monochromatic Subset Sums

Let F(k) be the minimal N such that if we two-colour {1,...,N}, there is a set A
of size k such that all non-empty subset sums are monochromatic. Estimate F(k).

**Status**: Bounds established, exact growth rate open
- Lower bound: F(k) ≥ 2^{2^{k-1}/k} (Balogh-Eberhard-Narayanan-Treglown-Wagner 2017)
- Upper bound: F(k) exists (Folkman's theorem)

Reference: https://erdosproblems.com/531
-/

import Mathlib
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Basic
import Mathlib.Order.BoundedOrder.Basic

namespace Erdos531

/-
## Overview

This problem concerns Folkman's theorem, a fundamental result in Ramsey theory
about monochromatic subset sums in colorings of integers.

### Background

Given any two-coloring of {1,...,N}, Folkman's theorem guarantees that for
sufficiently large N, there exists a k-element subset A such that all 2^k - 1
non-empty subset sums have the same color.

This is related to:
- Schur's theorem: avoiding x + y = z
- Rado's theorem: general linear equations
- Van der Waerden's theorem: arithmetic progressions
-/

/-- A two-coloring of natural numbers. -/
def Coloring := ℕ → Bool

/-- The set of all non-empty subset sums of a finite set. -/
def SubsetSums (A : Finset ℕ) : Finset ℕ :=
  (A.powerset.filter (· ≠ ∅)).image (Finset.sum · id)

/-- All subset sums have the same color. -/
def MonochromaticSubsetSums (c : Coloring) (A : Finset ℕ) : Prop :=
  ∃ col : Bool, ∀ s ∈ SubsetSums A, c s = col

/-- F(k) is the minimum N such that any 2-coloring of {1,...,N} has
    a k-element set with monochromatic subset sums. -/
def ExistsMonochromaticSet (N k : ℕ) : Prop :=
  ∀ c : Coloring, ∃ A : Finset ℕ, A.card = k ∧ (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
    MonochromaticSubsetSums c A

/-- The set of valid N values for a given k. -/
def ValidN (k : ℕ) : Set ℕ := {N : ℕ | ExistsMonochromaticSet N k}

/-- F(k) is the minimum valid N. -/
noncomputable def F (k : ℕ) : ℕ := sInf (ValidN k)

/-
## Folkman's Theorem

The existence of F(k) is Folkman's theorem. We derive it here as a genuine
theorem (no axiom) from two Mathlib results:

1. **Hindman's theorem** (`Hindman.FS_partition_regular`): in any finite cover
   of an FS-set (the set of finite sums of a stream), some part contains an
   FS-set. Applying this to the stream 1, 2, 3, … and the cover of its finite
   sums by the two color classes (intersected with the positive integers)
   yields a stream `b` whose finite sums are all positive and monochromatic.
   Grouping `b` into consecutive blocks, each one longer than the previous
   block's sum, makes the block sums strictly increasing; the sums of `k`
   blocks then form a `k`-element set of positive integers all of whose
   nonempty subset sums lie in `FS b`, hence are monochromatic.
2. **Rado's selection principle** (`Finset.rado_selection`): the compactness
   step. If no single `N` worked uniformly, the bad colorings `c_N` chosen for
   each `N` could be stitched into one coloring `χ` of ℕ agreeing with some
   `c_N` on any prescribed finite set; a monochromatic `k`-set for `χ` (from
   step 1) would then be monochromatic for some bad `c_N` with all elements
   `≤ N`, a contradiction.
-/

/-- Every element of `A` is itself a subset sum of `A`, via the singleton subset. -/
theorem self_mem_subsetSums {A : Finset ℕ} {a : ℕ} (ha : a ∈ A) : a ∈ SubsetSums A := by
  simp only [SubsetSums, Finset.mem_image, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨{a}, ⟨Finset.singleton_subset_iff.mpr ha, Finset.singleton_ne_empty a⟩, by simp⟩

open Hindman in
/-- Every finite sum from a stream of positive naturals is positive. -/
theorem fs_pos {a : Stream' ℕ} {m : ℕ} (hm : m ∈ FS a) : (∀ i, 1 ≤ a.get i) → 1 ≤ m := by
  induction hm with
  | head' a => exact fun ha => ha 0
  | tail' a m h ih => exact fun ha => ih fun i => ha (i + 1)
  | cons' a m h ih =>
    exact fun ha => le_trans (ih fun i => ha (i + 1)) (Nat.le_add_left m a.head)

/-- Block boundaries for the Folkman construction: `(folkmanBlocks b j).1` is the
start index of the `j`-th block of the stream `b` and `(folkmanBlocks b j).2` its
length. Each block is one longer than the previous block's sum, which forces the
block sums to be strictly increasing when all entries of `b` are positive. -/
def folkmanBlocks (b : Stream' ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | j + 1 =>
    ((folkmanBlocks b j).1 + (folkmanBlocks b j).2,
      (∑ i ∈ Finset.Ico (folkmanBlocks b j).1
        ((folkmanBlocks b j).1 + (folkmanBlocks b j).2), b.get i) + 1)

/-- The `j`-th block of indices. -/
def blockFinset (b : Stream' ℕ) (j : ℕ) : Finset ℕ :=
  Finset.Ico (folkmanBlocks b j).1 ((folkmanBlocks b j).1 + (folkmanBlocks b j).2)

/-- The sum of the stream `b` over the `j`-th block. -/
def blockSum (b : Stream' ℕ) (j : ℕ) : ℕ := ∑ i ∈ blockFinset b j, b.get i

theorem folkmanBlocks_succ_fst (b : Stream' ℕ) (j : ℕ) :
    (folkmanBlocks b (j + 1)).1 = (folkmanBlocks b j).1 + (folkmanBlocks b j).2 := by
  simp [folkmanBlocks]

theorem folkmanBlocks_succ_snd (b : Stream' ℕ) (j : ℕ) :
    (folkmanBlocks b (j + 1)).2 = blockSum b j + 1 := by
  simp [folkmanBlocks, blockSum, blockFinset]

theorem blockLen_pos (b : Stream' ℕ) (j : ℕ) : 1 ≤ (folkmanBlocks b j).2 := by
  cases j with
  | zero => simp [folkmanBlocks]
  | succ j => rw [folkmanBlocks_succ_snd]; omega

theorem blockFinset_nonempty (b : Stream' ℕ) (j : ℕ) : (blockFinset b j).Nonempty :=
  Finset.nonempty_Ico.mpr (by have := blockLen_pos b j; omega)

/-- When all entries of `b` are positive, each block sum is at least the block length. -/
theorem blockLen_le_blockSum (b : Stream' ℕ) (hb : ∀ i, 1 ≤ b.get i) (j : ℕ) :
    (folkmanBlocks b j).2 ≤ blockSum b j := by
  have h := Finset.card_nsmul_le_sum (blockFinset b j) (fun i => b.get i) 1
    (fun i _ => hb i)
  simpa [blockFinset, blockSum, Nat.card_Ico, smul_eq_mul] using h

theorem blockSum_pos (b : Stream' ℕ) (hb : ∀ i, 1 ≤ b.get i) (j : ℕ) :
    1 ≤ blockSum b j :=
  le_trans (blockLen_pos b j) (blockLen_le_blockSum b hb j)

/-- The block sums are strictly increasing: each block is longer than the
previous block's sum, and every entry is at least 1. -/
theorem blockSum_strictMono (b : Stream' ℕ) (hb : ∀ i, 1 ≤ b.get i) :
    StrictMono (blockSum b) := by
  apply strictMono_nat_of_lt_succ
  intro j
  have h1 := blockLen_le_blockSum b hb (j + 1)
  rw [folkmanBlocks_succ_snd] at h1
  omega

theorem blockStart_mono (b : Stream' ℕ) : Monotone fun j => (folkmanBlocks b j).1 := by
  apply monotone_nat_of_le_succ
  intro j
  rw [folkmanBlocks_succ_fst]
  exact Nat.le_add_right _ _

/-- Distinct blocks are disjoint (they are consecutive intervals). -/
theorem blockFinset_disjoint (b : Stream' ℕ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (blockFinset b i) (blockFinset b j) := by
  wlog h : i < j generalizing i j
  · exact (this (Ne.symm hij) (by omega)).symm
  rw [Finset.disjoint_left]
  intro x hxi hxj
  simp only [blockFinset, Finset.mem_Ico] at hxi hxj
  have h2 : (folkmanBlocks b i).1 + (folkmanBlocks b i).2 ≤ (folkmanBlocks b j).1 := by
    rw [← folkmanBlocks_succ_fst]
    exact blockStart_mono b h
  omega

open Hindman in
theorem blockSum_mem_FS (b : Stream' ℕ) (j : ℕ) : blockSum b j ∈ FS b :=
  FS.finsetSum b (blockFinset b j) (blockFinset_nonempty b j)

open Hindman in
/-- **Infinite Folkman theorem** (via Hindman's theorem): every 2-coloring of ℕ
admits, for every `k`, a `k`-element set of positive integers all of whose
nonempty subset sums are monochromatic. -/
theorem exists_monochromatic_of_coloring (c : Coloring) (k : ℕ) :
    ∃ A : Finset ℕ, A.card = k ∧ (∀ a ∈ A, 1 ≤ a) ∧ MonochromaticSubsetSums c A := by
  -- the stream 1, 2, 3, … of positive integers
  have ha : ∀ i, 1 ≤ Stream'.get (fun n => n + 1 : Stream' ℕ) i :=
    fun i => Nat.le_add_left 1 i
  -- cover the finite sums of that stream by the two color classes,
  -- intersected with the positive integers
  have scov : FS (fun n => n + 1 : Stream' ℕ) ⊆
      ⋃₀ {{x : ℕ | 1 ≤ x ∧ c x = true}, {x : ℕ | 1 ≤ x ∧ c x = false}} := by
    intro x hx
    have hx1 : 1 ≤ x := fs_pos hx ha
    rcases Bool.eq_false_or_eq_true (c x) with h | h
    · exact Set.mem_sUnion.mpr ⟨_, Set.mem_insert _ _, hx1, h⟩
    · exact Set.mem_sUnion.mpr ⟨_, Set.mem_insert_of_mem _ rfl, hx1, h⟩
  obtain ⟨cl, hcl, b, hb⟩ := FS_partition_regular (fun n => n + 1 : Stream' ℕ) _
    ((Set.finite_singleton _).insert _) scov
  obtain ⟨col, rfl⟩ : ∃ col : Bool, cl = {x : ℕ | 1 ≤ x ∧ c x = col} := by
    rcases Set.mem_insert_iff.mp hcl with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, Set.mem_singleton_iff.mp h⟩
  have hbFS : ∀ x ∈ FS b, 1 ≤ x ∧ c x = col := fun x hx => hb hx
  have hbpos : ∀ i, 1 ≤ b.get i := fun i => (hbFS _ (FS.singleton b i)).1
  refine ⟨(Finset.range k).image (blockSum b), ?_, ?_, col, ?_⟩
  · rw [Finset.card_image_of_injective _ (blockSum_strictMono b hbpos).injective,
      Finset.card_range]
  · intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    exact (hbFS _ (blockSum_mem_FS b j)).1
  · -- every nonempty subset sum is a sum of `b` over a union of disjoint
    -- blocks, hence lies in `FS b` and carries the color `col`
    intro s hs
    simp only [SubsetSums, Finset.mem_image, Finset.mem_filter, Finset.mem_powerset] at hs
    obtain ⟨t, ⟨hts, htne⟩, rfl⟩ := hs
    obtain ⟨u, hu, rfl⟩ := Finset.subset_image_iff.mp hts
    have hinj : ∀ x ∈ u, ∀ y ∈ u, blockSum b x = blockSum b y → x = y :=
      fun x _ y _ hxy => (blockSum_strictMono b hbpos).injective hxy
    have hune : u.Nonempty := by
      rcases Finset.eq_empty_or_nonempty u with rfl | h
      · simp at htne
      · exact h
    have hbiune : (u.biUnion (blockFinset b)).Nonempty := by
      obtain ⟨j, hj⟩ := hune
      obtain ⟨i, hi⟩ := blockFinset_nonempty b j
      exact ⟨i, Finset.mem_biUnion.mpr ⟨j, hj, hi⟩⟩
    have hdisj : (↑u : Set ℕ).PairwiseDisjoint (blockFinset b) :=
      fun i _ j _ hij => blockFinset_disjoint b hij
    have hsum : ∑ x ∈ Finset.image (blockSum b) u, id x
        = ∑ i ∈ u.biUnion (blockFinset b), b.get i := by
      rw [Finset.sum_image hinj, Finset.sum_biUnion hdisj]
      simp [blockSum]
    calc c (∑ x ∈ Finset.image (blockSum b) u, id x)
        = c (∑ i ∈ u.biUnion (blockFinset b), b.get i) := by rw [hsum]
      _ = col := (hbFS _ (FS.finsetSum b _ hbiune)).2

/-- **Folkman's Theorem**: F(k) exists for all k. Derived from Hindman's theorem
together with Rado's selection principle (the compactness step); both are
Mathlib theorems, so this carries no axioms beyond Lean's foundations. -/
theorem folkman_theorem :
    ∀ k : ℕ, k ≥ 1 → ∃ N : ℕ, ExistsMonochromaticSet N k := by
  intro k _
  by_contra hcon
  push Not at hcon
  -- for every `N` pick a coloring with no monochromatic `k`-set inside `{1, …, N}`
  have hbad : ∀ N : ℕ, ∃ cb : Coloring, ∀ A : Finset ℕ,
      ¬(A.card = k ∧ (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧ MonochromaticSubsetSums cb A) := by
    intro N
    obtain ⟨cb, hcb⟩ := not_forall.mp (hcon N)
    exact ⟨cb, not_exists.mp hcb⟩
  choose cN hcN using hbad
  -- stitch the bad colorings together with Rado's selection principle
  obtain ⟨χ, hχ⟩ := Finset.rado_selection (fun s => cN (s.sup id))
  obtain ⟨A, hcard, hpos, col, hcol⟩ := exists_monochromatic_of_coloring χ k
  obtain ⟨t, hst, hagree⟩ := hχ (SubsetSums A)
  refine hcN (t.sup id) A ⟨hcard, ?_, col, ?_⟩
  · intro x hx
    exact ⟨hpos x hx, Finset.le_sup (f := id) (hst (self_mem_subsetSums hx))⟩
  · intro s hs
    rw [← hagree s hs]
    exact hcol s hs

/-- F(k) is well-defined (the set ValidN k is non-empty). -/
theorem F_well_defined (k : ℕ) (hk : k ≥ 1) : (ValidN k).Nonempty :=
  folkman_theorem k hk

/-
## Lower Bounds

### Erdős-Spencer (1989)
Proved F(k) ≥ 2^{ck²/log k} for some constant c > 0.

### Balogh-Eberhard-Narayanan-Treglown-Wagner (2017)
Improved to F(k) ≥ 2^{2^{k-1}/k}.
-/

/-  Erdős-Spencer lower bound: F(k) ≥ 2^{ck²/log k}. -/
/-- Balogh et al. (2017): F(k) ≥ 2^{2^{k-1}/k}. -/
axiom balogh_2017 :
  ∀ k : ℕ, k ≥ 1 → F k ≥ 2^(2^(k-1) / k)

/-
## Small Cases

For small k, we can compute or bound F(k) directly.
-/

/-- The only non-empty subset sum of a singleton `{n}` is `n` itself. -/
theorem mem_subsetSums_singleton {n s : ℕ} (h : s ∈ SubsetSums {n}) : s = n := by
  simp only [SubsetSums, Finset.mem_image, Finset.mem_filter, Finset.mem_powerset] at h
  obtain ⟨t, ⟨ht_sub, ht_ne⟩, ht_sum⟩ := h
  have ht : t = {n} := by
    rcases Finset.subset_singleton_iff.mp ht_sub with h0 | h1
    · exact absurd h0 ht_ne
    · exact h1
  subst ht
  simp only [Finset.sum_singleton, id_eq] at ht_sum
  exact ht_sum.symm

/-- `1 ∈ ValidN 1`: for `k = 1` the singleton `{1}` always works, since its only
    subset sum is `1`, which is trivially monochromatic. -/
theorem one_mem_validN_one : (1 : ℕ) ∈ ValidN 1 := by
  intro c
  refine ⟨{1}, Finset.card_singleton 1, ?_, c 1, ?_⟩
  · intro a ha
    rw [Finset.mem_singleton] at ha; subst ha
    exact ⟨le_refl 1, le_refl 1⟩
  · intro s hs
    rw [mem_subsetSums_singleton hs]

/-- `1` lower-bounds `ValidN 1`: any valid `N` admits a non-empty `1`-element set
    with elements in `[1, N]`, forcing `N ≥ 1`. -/
theorem validN_one_ge_one {N : ℕ} (hN : N ∈ ValidN 1) : 1 ≤ N := by
  obtain ⟨A, hcard, hbound, _⟩ := hN (fun _ => true)
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by rw [hcard]; norm_num)
  exact (hbound a ha).1.trans (hbound a ha).2

/-- F(1) = 1: Any element forms a monochromatic 1-element set. -/
theorem F_1 : F 1 = 1 := by
  have hmem : (1 : ℕ) ∈ ValidN 1 := one_mem_validN_one
  have hle : F 1 ≤ 1 := Nat.sInf_le hmem
  have hge : 1 ≤ F 1 := validN_one_ge_one (Nat.sInf_mem ⟨1, hmem⟩)
  exact le_antisymm hle hge

/-- For a distinct pair `{a, b}`, monochromaticity of all subset sums is exactly
    `c b = c a ∧ c (a + b) = c a`: the non-empty subsets of a pair are `{a}`,
    `{b}`, `{a, b}`, with sums `a`, `b`, `a + b`. -/
theorem monochromaticSubsetSums_pair_iff (c : Coloring) {a b : ℕ} (hab : a ≠ b) :
    MonochromaticSubsetSums c {a, b} ↔ c b = c a ∧ c (a + b) = c a := by
  constructor
  · rintro ⟨col, hcol⟩
    have hmem_a : a ∈ SubsetSums {a, b} := by
      rw [SubsetSums, Finset.mem_image]
      refine ⟨{a}, ?_, by simp⟩
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.singleton_subset_iff.mpr (Finset.mem_insert_self a {b}),
        Finset.singleton_ne_empty a⟩
    have hmem_b : b ∈ SubsetSums {a, b} := by
      rw [SubsetSums, Finset.mem_image]
      refine ⟨{b}, ?_, by simp⟩
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.singleton_subset_iff.mpr
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self b)),
        Finset.singleton_ne_empty b⟩
    have hmem_ab : a + b ∈ SubsetSums {a, b} := by
      rw [SubsetSums, Finset.mem_image]
      refine ⟨{a, b}, ?_, by simp [Finset.sum_pair hab]⟩
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.Subset.refl _, Finset.insert_ne_empty a {b}⟩
    rw [hcol a hmem_a, hcol b hmem_b, hcol (a + b) hmem_ab]
    exact ⟨rfl, rfl⟩
  · rintro ⟨hba, hsum⟩
    refine ⟨c a, ?_⟩
    intro s hs
    rw [SubsetSums, Finset.mem_image] at hs
    obtain ⟨t, htf, hts⟩ := hs
    rw [Finset.mem_filter, Finset.mem_powerset] at htf
    obtain ⟨hsub, hne⟩ := htf
    by_cases ha' : a ∈ t <;> by_cases hb' : b ∈ t
    · have ht : t = {a, b} := by
        apply Finset.Subset.antisymm hsub
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact ha'
        · rw [Finset.mem_singleton] at hx'; subst hx'; exact hb'
      subst ht
      rw [Finset.sum_pair hab] at hts
      simp only [id_eq] at hts
      rw [← hts]; exact hsum
    · have ht : t = {a} := by
        apply Finset.Subset.antisymm
        · intro x hx
          rcases Finset.mem_insert.mp (hsub hx) with rfl | hx'
          · exact Finset.mem_singleton_self _
          · rw [Finset.mem_singleton] at hx'; subst hx'; exact absurd hx hb'
        · exact Finset.singleton_subset_iff.mpr ha'
      subst ht
      simp only [Finset.sum_singleton, id_eq] at hts
      rw [← hts]
    · have ht : t = {b} := by
        apply Finset.Subset.antisymm
        · intro x hx
          rcases Finset.mem_insert.mp (hsub hx) with rfl | hx'
          · exact absurd hx ha'
          · rw [Finset.mem_singleton] at hx'; subst hx'
            exact Finset.mem_singleton_self _
        · exact Finset.singleton_subset_iff.mpr hb'
      subst ht
      simp only [Finset.sum_singleton, id_eq] at hts
      rw [← hts]; exact hba
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      rcases Finset.mem_insert.mp (hsub hx) with rfl | hx'
      · exact absurd hx ha'
      · rw [Finset.mem_singleton] at hx'; subst hx'; exact absurd hx hb'

/-- Bool-level check: some distinct pair `{i+1, j+1} ⊆ {1,…,8}` of colour `col`
    (under `v : Fin 8 → Bool`, `v i` = colour of `i+1`) has element sum `s`. -/
def monoPairSumCheck (v : Fin 8 → Bool) (s : ℕ) (col : Bool) : Bool :=
  (List.finRange 8).any fun i =>
    (List.finRange 8).any fun j =>
      decide (i.val < j.val) && decide (i.val + j.val + 2 = s) &&
        (v i == col) && (v j == col)

/-- Bool-level check that a colouring of `{1,…,8}` is *forced*: either some
    distinct pair with sum ≤ 8 is already monochromatic, or some sum
    `s ∈ {9,…,16}` carries both a `true`-monochromatic and a
    `false`-monochromatic pair — so no colour of `s` avoids a pair. -/
def forcedCheck (v : Fin 8 → Bool) : Bool :=
  ((List.finRange 8).any fun i =>
    (List.finRange 8).any fun j =>
      decide (i.val < j.val) &&
        (if h : i.val + j.val + 2 ≤ 8 then
          (v i == v j) && (v ⟨i.val + j.val + 1, by omega⟩ == v i)
        else false))
  ||
  ((List.range 8).any fun k =>
    monoPairSumCheck v (k + 9) true && monoPairSumCheck v (k + 9) false)

set_option maxRecDepth 8192 in
/-- Exhaustive kernel check over all `2^8 = 256` colourings of `{1,…,8}`:
    every one is forced. Pure `decide` — no `native_decide`, no new axioms. -/
theorem forcedCheck_all : ∀ v : Fin 8 → Bool, forcedCheck v = true := by decide

/-- `8 ∈ ValidN 2`: every 2-colouring of `ℕ` admits a distinct pair
    `{a, b} ⊆ {1,…,8}` whose subset sums `a`, `b`, `a + b` are monochromatic. -/
theorem eight_mem_validN_two : (8 : ℕ) ∈ ValidN 2 := by
  intro c
  have hb := forcedCheck_all (fun i : Fin 8 => c (i.val + 1))
  simp only [forcedCheck, Bool.or_eq_true] at hb
  rcases hb with h | h
  · -- a direct pair with sum ≤ 8
    obtain ⟨i, -, hi⟩ := List.any_eq_true.mp h
    obtain ⟨j, -, hj⟩ := List.any_eq_true.mp hi
    rw [Bool.and_eq_true] at hj
    obtain ⟨hij', hd⟩ := hj
    have hij : i.val < j.val := of_decide_eq_true hij'
    have hi8 := i.isLt
    have hj8 := j.isLt
    by_cases hs : i.val + j.val + 2 ≤ 8
    · rw [dif_pos hs, Bool.and_eq_true] at hd
      obtain ⟨hvv, hvs⟩ := hd
      have h1 : c (j.val + 1) = c (i.val + 1) := (beq_iff_eq.mp hvv).symm
      have h2 : c (i.val + j.val + 1 + 1) = c (i.val + 1) := beq_iff_eq.mp hvs
      refine ⟨{i.val + 1, j.val + 1}, Finset.card_pair (by omega), ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact ⟨by omega, by omega⟩
        · rw [Finset.mem_singleton] at hx'; subst hx'
          exact ⟨by omega, by omega⟩
      · refine (monochromaticSubsetSums_pair_iff c (by omega)).mpr ⟨h1, ?_⟩
        have hrw : i.val + 1 + (j.val + 1) = i.val + j.val + 1 + 1 := by omega
        rw [hrw]
        exact h2
    · rw [dif_neg hs] at hd
      exact absurd hd (by simp)
  · -- a conflict sum s = k + 9: both colours of s are excluded, so whichever
    -- colour `c (k+9)` takes completes one of the two recorded pairs
    obtain ⟨k, -, hk⟩ := List.any_eq_true.mp h
    rw [Bool.and_eq_true] at hk
    obtain ⟨ht, hf⟩ := hk
    simp only [monoPairSumCheck] at ht hf
    obtain ⟨i₁, -, hi₁⟩ := List.any_eq_true.mp ht
    obtain ⟨j₁, -, hj₁⟩ := List.any_eq_true.mp hi₁
    obtain ⟨i₂, -, hi₂⟩ := List.any_eq_true.mp hf
    obtain ⟨j₂, -, hj₂⟩ := List.any_eq_true.mp hi₂
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hj₁ hj₂
    obtain ⟨⟨⟨hij₁, hsum₁⟩, hci₁⟩, hcj₁⟩ := hj₁
    obtain ⟨⟨⟨hij₂, hsum₂⟩, hci₂⟩, hcj₂⟩ := hj₂
    have hb₁ := i₁.isLt; have hb₂ := j₁.isLt
    have hb₃ := i₂.isLt; have hb₄ := j₂.isLt
    cases hcs : c (k + 9)
    · -- c (k+9) = false: the false-coloured pair completes
      refine ⟨{i₂.val + 1, j₂.val + 1}, Finset.card_pair (by omega), ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact ⟨by omega, by omega⟩
        · rw [Finset.mem_singleton] at hx'; subst hx'
          exact ⟨by omega, by omega⟩
      · refine (monochromaticSubsetSums_pair_iff c (by omega)).mpr ⟨?_, ?_⟩
        · rw [hci₂, hcj₂]
        · have hrw : i₂.val + 1 + (j₂.val + 1) = k + 9 := by omega
          rw [hrw, hcs, hci₂]
    · -- c (k+9) = true: the true-coloured pair completes
      refine ⟨{i₁.val + 1, j₁.val + 1}, Finset.card_pair (by omega), ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact ⟨by omega, by omega⟩
        · rw [Finset.mem_singleton] at hx'; subst hx'
          exact ⟨by omega, by omega⟩
      · refine (monochromaticSubsetSums_pair_iff c (by omega)).mpr ⟨?_, ?_⟩
        · rw [hci₁, hcj₁]
        · have hrw : i₁.val + 1 + (j₁.val + 1) = k + 9 := by omega
          rw [hrw, hcs, hci₁]

/-- The explicit colouring defeating `N = 7`: colour `3, 5, 6, 7` red (`true`)
    and everything else — in particular `1, 2, 4` and all sums `≥ 8` — blue
    (`false`). Red pair sums land in `{8,…,13}` (blue), blue pair sums land in
    `{3, 5, 6}` (red). -/
def witnessColoring : Coloring := fun n =>
  decide (n = 3 ∨ n = 5 ∨ n = 6 ∨ n = 7)

/-- `7 ∉ ValidN 2`: the witness colouring leaves every distinct pair in
    `{1,…,7}` non-monochromatic. -/
theorem seven_not_mem_validN_two : (7 : ℕ) ∉ ValidN 2 := by
  intro h
  obtain ⟨A, hcard, hbound, hmono⟩ := h witnessColoring
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  obtain ⟨h1, h2⟩ := (monochromaticSubsetSums_pair_iff witnessColoring hab).mp hmono
  obtain ⟨ha1, ha7⟩ := hbound a (Finset.mem_insert_self a {b})
  obtain ⟨hb1, hb7⟩ := hbound b (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
  interval_cases a <;> interval_cases b <;> revert hab h1 h2 <;> decide

/-- `ValidN k` is upward closed: a witness set for `N` also lies in `{1,…,M}`
    for any `M ≥ N`. -/
theorem validN_mono {k N M : ℕ} (hNM : N ≤ M) (hN : N ∈ ValidN k) : M ∈ ValidN k := by
  intro c
  obtain ⟨A, hcard, hbound, hmono⟩ := hN c
  exact ⟨A, hcard, fun a ha => ⟨(hbound a ha).1, (hbound a ha).2.trans hNM⟩, hmono⟩

/-- F(2) = 8. **Correction (2026-07-10):** an earlier draft claimed `F 2 = 3`.
    That value is FALSE for the distinct-pair Folkman number defined here (a set
    `A` of `k = 2` *distinct* elements `{a, b}` with `a, b, a+b` monochromatic).
    An exhaustive check of all 2-colourings gives F(2) = 8, not 3:

    * `N = 7` fails — the colouring
        `1,2,4 ↦ B`, `3,5,6,7 ↦ R` (and `≥ 8 ↦ B`)
      leaves every 2-subset `{a,b} ⊆ {1,…,7}` with `{a, b, a+b}` non-monochromatic;
    * `N = 8` succeeds — every 2-colouring of `{1,…,8}` forces some distinct pair
      `{a, b}` with `a, b, a+b` all one colour.

    (In particular `3 ∉ ValidN 2`: the colouring `3 ↦ R`, everything else `B`
    defeats all three pairs of `{1,2,3}`, namely `{1,2}`, `{1,3}`, `{2,3}`.)

    The finite-coloring reduction is carried out below: `forcedCheck_all` kernel-
    checks all 256 restrictions of a colouring to `{1,…,8}`, certifying that each
    either contains a direct monochromatic pair (sum ≤ 8) or pins a sum
    `s ∈ {9,…,16}` on which two opposite-coloured pairs collide — so either
    colour of `s` completes a pair. -/
theorem F_2 : F 2 = 8 := by
  have h8 : (8 : ℕ) ∈ ValidN 2 := eight_mem_validN_two
  have h7 : (7 : ℕ) ∉ ValidN 2 := seven_not_mem_validN_two
  have hne : (ValidN 2).Nonempty := ⟨8, h8⟩
  rcases Nat.lt_or_ge (F 2) 8 with hlt | hge
  · have hmem : F 2 ∈ ValidN 2 := Nat.sInf_mem hne
    exact absurd (validN_mono (by omega) hmem) h7
  · exact le_antisymm (Nat.sInf_le h8) hge

/-  F(3) ≥ 11: Lower bound for 3-element sets. -/
/-
## Upper Bounds

The original upper bounds from Folkman's proof are very weak.
Improvements have been made using probabilistic methods.
-/

/-  Folkman's original upper bound is at least tower-type. -/
/-
## Connection to Rado's Theorem

Folkman's theorem follows from Rado's theorem about partition regularity
of systems of linear equations.

The equation system is:
- For each non-empty S ⊆ {1,...,k}: Σᵢ∈S xᵢ = yₛ
- We want all yₛ to be monochromatic.

Rado's theorem guarantees this for any k.
-/

/-  Folkman follows from Rado's theorem. -/
/-
## The Main Question

The central open question is the precise growth rate of F(k).

Known:
- F(k) ≥ 2^{2^{k-1}/k} (doubly exponential lower bound)
- F(k) is finite (Folkman's theorem)

The gap between lower and upper bounds is enormous.
-/

/-- The growth rate of F(k) is at least doubly exponential. -/
theorem F_growth_doubly_exponential :
    ∀ k : ℕ, k ≥ 1 → F k ≥ 2^(2^(k-1) / k) :=
  balogh_2017

/-- Summary of Erdős Problem #531. -/
theorem erdos_531_summary (k : ℕ) (hk : k ≥ 1) :
    (ValidN k).Nonempty ∧ F k ≥ 2^(2^(k-1) / k) :=
  ⟨F_well_defined k hk, balogh_2017 k hk⟩

/-
## Proof Techniques

The lower bound proofs use:
1. Probabilistic counting arguments
2. Careful analysis of subset sum structure
3. Balancing conditions on colorings

The proof by Balogh et al. (2017) uses a clever inductive construction
that exploits the multiplicative structure of subset sums.
-/

/-- The main result: F(k) exists with doubly exponential lower bound. -/
theorem erdos_531 :
    ∀ k : ℕ, k ≥ 1 → (ValidN k).Nonempty :=
  fun k hk => folkman_theorem k hk

end Erdos531
