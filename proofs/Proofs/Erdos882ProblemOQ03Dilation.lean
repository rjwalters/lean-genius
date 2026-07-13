/-
# Erdős Problem #882 — OQ-03: Dilation covariance of the subset-sum structure

Erdős Problem #882 asks for the largest `A ⊆ {1,…,n}` whose non-empty subset
sums are pairwise non-dividing (answer: `(1+o(1)) log₂ n`).  The structural
layer in `Erdos882ProblemOQ03` establishes downward closure, the counting
anchor `|subsetSums A| ≤ 2^|A| − 1`, and the distinct-subset-sum regime.

This file adds an orthogonal **symmetry** layer: how the whole structure
behaves under the *dilation* action `A ↦ k·A := {k·a : a ∈ A}`.  Scaling every
element by a fixed `k ≥ 1` is the natural `(ℕ_{≥1}, ×)`-action on subsets, and
it is *covariant* with every ingredient of the Erdős #882 problem:

  * `dilate_one`, `dilate_dilate`   — dilation is a monoid action
                                       (`1·A = A`, `k·(j·A) = (kj)·A`);
  * `dilate_card`                    — dilation preserves cardinality (`k ≥ 1`);
  * `sum_dilate`                     — `∑(k·A) = k·∑A`;
  * `subsetSums_dilate`              — **the sum map commutes with dilation**:
                                       `subsetSums (k·A) = k·(subsetSums A)`;
  * `divisibilityFree_image_mul_iff` — divisibility-freeness is dilation-invariant
                                       (`k·a ∣ k·b ↔ a ∣ b`);
  * `distinctSubsetSums_dilate_iff`  — having distinct subset sums is
                                       dilation-invariant;
  * `validSubset_dilate_iff`         — **the scaling law**
                                       `ValidSubset (k·n) (k·A) ↔ ValidSubset n A`.

The headline is `validSubset_dilate_iff`: the Erdős #882 extremal problem at
scale `n` embeds *exactly* into scale `k·n` via dilation — validity is neither
gained nor lost.  In particular an optimal divisibility-free-subset-sum set for
`{1,…,n}` dilates to one of the *same size* inside `{1,…,k·n}`, so the extremal
function is monotone along the dilation orbit.  This is the exact companion of
the downward-closure (`validSubset_subset`) and heredity (`DivisibilityFree.mono`)
tools: those pass to sub-configurations, this rescales them.

Self-contained: the five predicates are re-declared here (the parent file
predates the current Mathlib toolchain), so this contribution stands on its own.

Reference: Erdős Problem #882, https://erdosproblems.com/882
-/

import Mathlib

namespace Erdos882OQ03Dilation

open Finset BigOperators

/-- All non-empty subsets of a finite set. -/
def nonemptySubsets (A : Finset ℕ) : Finset (Finset ℕ) :=
  A.powerset.filter (· ≠ ∅)

/-- The set of all non-empty subset sums `{∑_{a ∈ S} a : ∅ ≠ S ⊆ A}`. -/
def subsetSums (A : Finset ℕ) : Finset ℕ :=
  (nonemptySubsets A).image (fun S => S.sum id)

/-- No two distinct elements of a set divide each other. -/
def DivisibilityFree (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬(a ∣ b) ∧ ¬(b ∣ a)

/-- `A` is a valid subset of `{1,…,n}` with divisibility-free subset sums. -/
def ValidSubset (n : ℕ) (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) ∧ DivisibilityFree (subsetSums A)

/-- `A` realises the maximum `2^{|A|} − 1` distinct non-empty subset sums. -/
def DistinctSubsetSums (A : Finset ℕ) : Prop :=
  (subsetSums A).card = 2 ^ A.card - 1

/-- **Dilation.**  Scale every element of `A` by a factor `k`. -/
def dilate (k : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.image (fun a => k * a)

/-- Multiplication by `k ≥ 1` is injective on `ℕ` — the fact that makes dilation
    a faithful action (for `k = 0` everything collapses to `{0}`). -/
theorem mul_injective {k : ℕ} (hk : 1 ≤ k) : Function.Injective (fun a : ℕ => k * a) :=
  fun _ _ h => Nat.eq_of_mul_eq_mul_left hk h

/-- **Dilation is a monoid action, part 1: identity.**  Scaling by `1` is the
    identity on subsets. -/
theorem dilate_one (A : Finset ℕ) : dilate 1 A = A := by
  unfold dilate; simp

/-- **Dilation is a monoid action, part 2: composition.**  Scaling by `j` then by
    `k` equals scaling by `k·j`. -/
theorem dilate_dilate (k j : ℕ) (A : Finset ℕ) :
    dilate k (dilate j A) = dilate (k * j) A := by
  unfold dilate
  rw [Finset.image_image]
  apply Finset.image_congr
  intro a _
  simp only [Function.comp_apply, Nat.mul_assoc]

/-- **Dilation preserves cardinality** (for `k ≥ 1`): scaling is injective, so
    `|k·A| = |A|`. -/
theorem dilate_card {k : ℕ} (hk : 1 ≤ k) (A : Finset ℕ) :
    (dilate k A).card = A.card :=
  Finset.card_image_of_injective A (mul_injective hk)

/-- The sum of a dilated set scales: `∑ (image (k·) S) = k · ∑ S`.  The injectivity
    of `k·` (`k ≥ 1`) lets `Finset.sum_image` push the sum through the image, then
    `Finset.mul_sum` factors out `k`. -/
theorem sum_image_mul {k : ℕ} (hk : 1 ≤ k) (S : Finset ℕ) :
    (S.image (fun a => k * a)).sum id = k * S.sum id := by
  rw [Finset.sum_image ((mul_injective hk).injOn)]
  simp only [id_eq, Finset.mul_sum]

/-- **The total scales under dilation:** `∑ (k·A) = k · ∑ A`. -/
theorem sum_dilate {k : ℕ} (hk : 1 ≤ k) (A : Finset ℕ) :
    (dilate k A).sum id = k * A.sum id :=
  sum_image_mul hk A

/-- **The sum map commutes with dilation.**  `subsetSums (k·A) = k·(subsetSums A)`:
    the non-empty subsets of `k·A` are exactly the dilations of the non-empty
    subsets of `A` (dilation being injective for `k ≥ 1`), and each such subset's
    sum scales by `k` (`sum_image_mul`).  So the entire subset-sum spectrum of `A`
    is uniformly rescaled by `k`. -/
theorem subsetSums_dilate {k : ℕ} (hk : 1 ≤ k) (A : Finset ℕ) :
    subsetSums (dilate k A) = (subsetSums A).image (fun m => k * m) := by
  apply Finset.Subset.antisymm
  · intro m hm
    simp only [subsetSums, nonemptySubsets, dilate, Finset.mem_image, Finset.mem_filter,
      Finset.mem_powerset] at hm
    obtain ⟨T, ⟨hTsub, hTne⟩, rfl⟩ := hm
    rw [Finset.subset_image_iff] at hTsub
    obtain ⟨S, hSsub, rfl⟩ := hTsub
    have hSne : S ≠ ∅ := by
      rintro rfl
      simp only [Finset.image_empty, ne_eq, not_true_eq_false] at hTne
    rw [Finset.mem_image]
    refine ⟨S.sum id, ?_, ?_⟩
    · simp only [subsetSums, nonemptySubsets, Finset.mem_image, Finset.mem_filter,
        Finset.mem_powerset]
      exact ⟨S, ⟨hSsub, hSne⟩, rfl⟩
    · rw [sum_image_mul hk]
  · intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨s, hs, rfl⟩ := hm
    simp only [subsetSums, nonemptySubsets, Finset.mem_image, Finset.mem_filter,
      Finset.mem_powerset] at hs
    obtain ⟨S, ⟨hSsub, hSne⟩, rfl⟩ := hs
    simp only [subsetSums, nonemptySubsets, dilate, Finset.mem_image, Finset.mem_filter,
      Finset.mem_powerset]
    refine ⟨S.image (fun a => k * a), ⟨Finset.image_subset_image hSsub, ?_⟩, ?_⟩
    · rw [← Finset.nonempty_iff_ne_empty]
      exact (Finset.nonempty_iff_ne_empty.mpr hSne).image _
    · rw [sum_image_mul hk]

/-- **Divisibility-freeness is dilation-invariant.**  Multiplying every element by
    a fixed `k ≥ 1` neither creates nor destroys divisibility relations, because
    `k·a ∣ k·b ↔ a ∣ b`.  So a set is divisibility-free iff its `k`-dilation is. -/
theorem divisibilityFree_image_mul_iff {k : ℕ} (hk : 1 ≤ k) (S : Finset ℕ) :
    DivisibilityFree (S.image (fun a => k * a)) ↔ DivisibilityFree S := by
  have hdvd : ∀ a b : ℕ, (k * a ∣ k * b) ↔ (a ∣ b) :=
    fun a b => Nat.mul_dvd_mul_iff_left hk
  constructor
  · intro h a ha b hb hab
    have hne : k * a ≠ k * b := fun heq => hab (mul_injective hk heq)
    obtain ⟨h1, h2⟩ := h (k * a) (Finset.mem_image_of_mem _ ha)
      (k * b) (Finset.mem_image_of_mem _ hb) hne
    exact ⟨fun hd => h1 ((hdvd a b).mpr hd), fun hd => h2 ((hdvd b a).mpr hd)⟩
  · intro h x hx y hy hxy
    rw [Finset.mem_image] at hx hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have hab : a ≠ b := fun heq => hxy (by rw [heq])
    obtain ⟨h1, h2⟩ := h a ha b hb hab
    exact ⟨fun hd => h1 ((hdvd a b).mp hd), fun hd => h2 ((hdvd b a).mp hd)⟩

/-- **Divisibility-freeness of the subset sums is dilation-invariant.**  Since the
    subset-sum spectrum rescales uniformly (`subsetSums_dilate`) and divisibility
    is scale-free (`divisibilityFree_image_mul_iff`), the divisibility-free
    condition on the subset sums transfers exactly across dilation. -/
theorem divisibilityFree_subsetSums_dilate_iff {k : ℕ} (hk : 1 ≤ k) (A : Finset ℕ) :
    DivisibilityFree (subsetSums (dilate k A)) ↔ DivisibilityFree (subsetSums A) := by
  rw [subsetSums_dilate hk]
  exact divisibilityFree_image_mul_iff hk _

/-- **Having distinct subset sums is dilation-invariant.**  Dilation preserves both
    `|subsetSums A|` (it rescales the spectrum injectively) and `|A|`, so the
    extremal equation `|subsetSums A| = 2^{|A|} − 1` is preserved and reflected. -/
theorem distinctSubsetSums_dilate_iff {k : ℕ} (hk : 1 ≤ k) (A : Finset ℕ) :
    DistinctSubsetSums (dilate k A) ↔ DistinctSubsetSums A := by
  unfold DistinctSubsetSums
  rw [subsetSums_dilate hk, Finset.card_image_of_injective _ (mul_injective hk),
    dilate_card hk]

/-- **The Erdős #882 scaling law.**  Dilation by `k ≥ 1` gives a bijection between
    valid subsets of `{1,…,n}` and valid subsets of `{1,…,k·n}` supported on the
    dilated lattice: `ValidSubset (k·n) (k·A) ↔ ValidSubset n A`.  Both the
    membership bounds (`1 ≤ a ≤ n ↔ 1 ≤ k·a ≤ k·n`) and the divisibility-free
    condition on the subset sums (`divisibilityFree_subsetSums_dilate_iff`) transfer
    exactly.  Consequently an optimal divisibility-free-subset-sum set for `{1,…,n}`
    dilates to one of the *same cardinality* (`dilate_card`) inside `{1,…,k·n}` — the
    extremal function is monotone along every dilation orbit. -/
theorem validSubset_dilate_iff {n k : ℕ} (hk : 1 ≤ k) {A : Finset ℕ} :
    ValidSubset (k * n) (dilate k A) ↔ ValidSubset n A := by
  unfold ValidSubset
  rw [divisibilityFree_subsetSums_dilate_iff hk]
  refine and_congr_left (fun _ => ?_)
  constructor
  · intro hbound a ha
    obtain ⟨h1, h2⟩ := hbound (k * a) (Finset.mem_image_of_mem _ ha)
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos a with rfl | hpos
      · simp only [Nat.mul_zero] at h1; omega
      · exact hpos
    · exact Nat.le_of_mul_le_mul_left h2 hk
  · intro hbound x hx
    simp only [dilate, Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨h1, h2⟩ := hbound a ha
    refine ⟨?_, Nat.mul_le_mul (le_refl k) h2⟩
    have := Nat.mul_le_mul hk h1
    simpa using this

/-- **Dilation produces same-size valid witnesses.**  Given a valid set `A` for
    `{1,…,n}`, its `k`-dilation is a valid set for `{1,…,k·n}` with the identical
    cardinality — the concrete transfer of extremal witnesses along the dilation
    orbit implied by `validSubset_dilate_iff` and `dilate_card`. -/
theorem exists_validSubset_dilate {n k : ℕ} (hk : 1 ≤ k) {A : Finset ℕ}
    (hA : ValidSubset n A) :
    ValidSubset (k * n) (dilate k A) ∧ (dilate k A).card = A.card :=
  ⟨(validSubset_dilate_iff hk).mpr hA, dilate_card hk A⟩

end Erdos882OQ03Dilation
