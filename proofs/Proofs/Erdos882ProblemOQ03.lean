/-
# Erdős Problem #882 — OQ-03: Structural theory of valid subset-sum sets

Erdős Problem #882 asks for the largest `A ⊆ {1,…,n}` whose non-empty subset
sums are pairwise non-dividing (answer: `(1+o(1)) log₂ n`).  The parent file
`Erdos882Problem` introduces the concrete predicates `subsetSums`,
`DivisibilityFree`, `ValidSubset` and states the two deep analytic bounds as
axioms, but proves *no* structural properties of the predicates.

This file supplies that missing structural layer — all fully machine-checked
(0 axioms, 0 sorries):

  * `subsetSums_mono`         — subset sums grow with the set;
  * `DivisibilityFree.mono`   — divisibility-freeness is hereditary;
  * `validSubset_subset`      — **`ValidSubset` is downward closed**;
  * `subsetSums_nonempty`     — a non-empty set has a non-empty sum set;
  * `subsetSums_pos`          — subset sums of positive sets are positive;
  * `nonemptySubsets_card`    — there are exactly `2^|A| − 1` non-empty subsets;
  * `subsetSums_card_le`      — **`|subsetSums A| ≤ 2^|A| − 1`** (counting anchor);
  * `subset_subsetSums`       — `A ⊆ subsetSums A` (elements are subset sums);
  * `subsetSums_card_ge`      — **`|A| ≤ |subsetSums A|`** (counting lower bound);
  * `subsetSums_card_bounds`  — the sandwich `|A| ≤ |subsetSums A| ≤ 2^|A| − 1`;
  * `subsetSums_le`           — every subset sum is `≤ n·|A|`;
  * `subsetSums_subset_Icc`   — **`subsetSums A ⊆ {1,…,n·|A|}`** (membership range);
  * `subsetSums_singleton`    — `subsetSums {a} = {a}`;
  * `subsetSums_insert`       — **insertion recursion** `subsetSums (insert a A) =
                                 insert a (subsetSums A ∪ (subsetSums A).image (a+·))`;
  * `subsetSums_card_insert_superincreasing` — the exact **doubling law**
                                 `|subsetSums (insert a A)| = 2·|subsetSums A| + 1`
                                 when `a > ∑ A` (the superincreasing / distinct-sum regime).

The headline is downward closure: any subset of a valid set is valid — the
standard "WLOG pass to a sub-configuration" tool for extremal arguments, and
the exact monotonicity the upper-bound proof leans on.  The new cardinality
bound `subsetSums_card_le` supplies the information-theoretic counting anchor
behind the `(1+o(1)) log₂ n` upper bound: the sum map cannot manufacture more
than `2^|A| − 1` distinct subset sums.

Self-contained: the four predicates are re-declared here (the parent file
predates the current Mathlib toolchain and no longer builds), using the modern
Finset API, so this contribution stands on its own.

Reference: Erdős Problem #882, https://erdosproblems.com/882
-/

import Mathlib

namespace Erdos882OQ03

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

/-- Subset sums are monotone: enlarging `A` only adds subset sums.
    Every non-empty `S ⊆ A` is also a non-empty subset of `B ⊇ A`. -/
theorem subsetSums_mono {A B : Finset ℕ} (h : A ⊆ B) :
    subsetSums A ⊆ subsetSums B := by
  intro s hs
  unfold subsetSums nonemptySubsets at hs ⊢
  rw [Finset.mem_image] at hs ⊢
  obtain ⟨S, hS, rfl⟩ := hs
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  refine ⟨S, ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hS.1.trans h, hS.2⟩

/-- Divisibility-freeness is hereditary: a subset of a divisibility-free set is
    divisibility-free. -/
theorem DivisibilityFree.mono {S T : Finset ℕ} (h : S ⊆ T)
    (hT : DivisibilityFree T) : DivisibilityFree S :=
  fun a ha b hb hab => hT a (h ha) b (h hb) hab

/-- **`ValidSubset` is downward closed.**  Any subset `B` of a valid set `A`
    is itself valid: the membership bounds restrict, and the divisibility-free
    condition on `subsetSums B ⊆ subsetSums A` is inherited. -/
theorem validSubset_subset {n : ℕ} {A B : Finset ℕ}
    (hA : ValidSubset n A) (h : B ⊆ A) : ValidSubset n B := by
  obtain ⟨hbound, hdf⟩ := hA
  exact ⟨fun a ha => hbound a (h ha), hdf.mono (subsetSums_mono h)⟩

/-- A non-empty set has at least one non-empty subset sum (e.g. a singleton). -/
theorem subsetSums_nonempty {A : Finset ℕ} (hA : A.Nonempty) :
    (subsetSums A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  refine ⟨a, ?_⟩
  unfold subsetSums nonemptySubsets
  rw [Finset.mem_image]
  refine ⟨{a}, ?_, by simp⟩
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.singleton_subset_iff.mpr ha, Finset.singleton_ne_empty a⟩

/-- Every subset sum of a set of positive integers is itself positive: a
    non-empty subset of positive numbers sums to at least its smallest member. -/
theorem subsetSums_pos {A : Finset ℕ} (hA : ∀ a ∈ A, 1 ≤ a) :
    ∀ s ∈ subsetSums A, 1 ≤ s := by
  intro s hs
  unfold subsetSums nonemptySubsets at hs
  rw [Finset.mem_image] at hs
  obtain ⟨S, hS, rfl⟩ := hs
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  obtain ⟨hSsub, hSne⟩ := hS
  obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hSne
  calc 1 ≤ b := hA b (hSsub hb)
    _ ≤ S.sum id := Finset.single_le_sum (fun i _ => Nat.zero_le (id i)) hb

/-- The family of non-empty subsets has exactly `2^|A| − 1` members: the full
    powerset has `2^|A|` elements and we discard only the empty set. -/
theorem nonemptySubsets_card (A : Finset ℕ) :
    (nonemptySubsets A).card = 2 ^ A.card - 1 := by
  unfold nonemptySubsets
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.empty_mem_powerset A),
    Finset.card_powerset]

/-- **Information-theoretic cardinality bound.**  A set with `|A|` elements has at
    most `2^|A| − 1` distinct non-empty subset sums — the sum map can only collapse
    the `2^|A| − 1` non-empty subsets, never create new values.  This is the
    counting anchor behind the `(1+o(1))log₂ n` upper bound: a divisibility-free
    family of subset sums inside `{1,…,n·|A|}` cannot be too large, while the sums
    themselves number at most `2^|A| − 1`. -/
theorem subsetSums_card_le (A : Finset ℕ) :
    (subsetSums A).card ≤ 2 ^ A.card - 1 := by
  unfold subsetSums
  exact le_trans Finset.card_image_le (le_of_eq (nonemptySubsets_card A))

/-- **Membership upper bound.**  If every element of `A` is at most `n`, then
    every non-empty subset sum is at most `n · |A|`: each of the (at most `|A|`)
    summands of a subset `S ⊆ A` contributes at most `n`. -/
theorem subsetSums_le {A : Finset ℕ} {n : ℕ} (hA : ∀ a ∈ A, a ≤ n) :
    ∀ s ∈ subsetSums A, s ≤ n * A.card := by
  intro s hs
  unfold subsetSums nonemptySubsets at hs
  rw [Finset.mem_image] at hs
  obtain ⟨S, hS, rfl⟩ := hs
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  obtain ⟨hSsub, _⟩ := hS
  have hcard : S.card ≤ A.card := Finset.card_le_card hSsub
  calc S.sum id ≤ ∑ _a ∈ S, n := Finset.sum_le_sum (fun i hi => hA i (hSsub hi))
    _ = n * S.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ n * A.card := Nat.mul_le_mul (le_refl n) hcard

/-- **Membership range.**  For a set of positive integers each `≤ n`, every
    non-empty subset sum lies in the explicit interval `{1,…,n·|A|}`.  Together
    with `subsetSums_card_le` this pins down the counting side of the
    `(1+o(1))log₂ n` upper bound: the `≤ 2^|A| − 1` distinct subset sums are all
    confined to an interval of length `n·|A|`. -/
theorem subsetSums_subset_Icc {A : Finset ℕ} {n : ℕ}
    (hlo : ∀ a ∈ A, 1 ≤ a) (hhi : ∀ a ∈ A, a ≤ n) :
    subsetSums A ⊆ Finset.Icc 1 (n * A.card) := by
  intro s hs
  rw [Finset.mem_Icc]
  exact ⟨subsetSums_pos hlo s hs, subsetSums_le hhi s hs⟩

/-- The subset-sum set of a singleton is the singleton itself: the only non-empty
    subset of `{a}` is `{a}`, whose sum is `a`. -/
theorem subsetSums_singleton (a : ℕ) : subsetSums {a} = {a} := by
  apply Finset.Subset.antisymm
  · intro s hs
    unfold subsetSums nonemptySubsets at hs
    rw [Finset.mem_image] at hs
    obtain ⟨S, hS, rfl⟩ := hs
    rw [Finset.mem_filter, Finset.mem_powerset, Finset.subset_singleton_iff] at hS
    rcases hS.1 with h | h
    · exact absurd h hS.2
    · simp [h]
  · intro s hs
    rw [Finset.mem_singleton] at hs
    subst hs
    unfold subsetSums nonemptySubsets
    rw [Finset.mem_image]
    refine ⟨{s}, ?_, by simp⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl _, Finset.singleton_ne_empty s⟩

/-- Every element of `A` is one of its own subset sums (the singleton subset
    `{a}` sums to `a`), so `A ⊆ subsetSums A`. -/
theorem subset_subsetSums (A : Finset ℕ) : A ⊆ subsetSums A := by
  intro a ha
  unfold subsetSums nonemptySubsets
  rw [Finset.mem_image]
  refine ⟨{a}, ?_, by simp⟩
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.singleton_subset_iff.mpr ha, Finset.singleton_ne_empty a⟩

/-- **Cardinality lower bound.**  A set has at least `|A|` distinct non-empty
    subset sums, since its own elements are singleton subset sums.  Together with
    `subsetSums_card_le` this sandwiches the count:
    `|A| ≤ |subsetSums A| ≤ 2^|A| − 1`. -/
theorem subsetSums_card_ge (A : Finset ℕ) : A.card ≤ (subsetSums A).card :=
  Finset.card_le_card (subset_subsetSums A)

/-- The full sandwich for the number of distinct non-empty subset sums:
    it is at least the number of generators `|A|` and at most `2^|A| − 1`. -/
theorem subsetSums_card_bounds (A : Finset ℕ) :
    A.card ≤ (subsetSums A).card ∧ (subsetSums A).card ≤ 2 ^ A.card - 1 :=
  ⟨subsetSums_card_ge A, subsetSums_card_le A⟩

/-- **The total sum is a subset sum.**  The whole set `A` is one of its own
    non-empty subsets (when `A` is non-empty), so its total `∑ A` occurs as a
    subset sum. -/
theorem sum_mem_subsetSums {A : Finset ℕ} (hA : A.Nonempty) :
    A.sum id ∈ subsetSums A := by
  unfold subsetSums nonemptySubsets
  rw [Finset.mem_image]
  refine ⟨A, ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.Subset.refl A, Finset.nonempty_iff_ne_empty.mp hA⟩

/-- **The total sum dominates every subset sum.**  Every non-empty subset sum is
    at most the total `∑ A`, since a subset's sum never exceeds the whole set's
    sum (all summands are non-negative). -/
theorem subsetSums_le_sum {A : Finset ℕ} :
    ∀ s ∈ subsetSums A, s ≤ A.sum id := by
  intro s hs
  unfold subsetSums nonemptySubsets at hs
  rw [Finset.mem_image] at hs
  obtain ⟨S, hS, rfl⟩ := hs
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  exact Finset.sum_le_sum_of_subset hS.1

/-- **Sharp membership range.**  For a set of positive integers every non-empty
    subset sum lies in `{1,…,∑ A}`.  This refines `subsetSums_subset_Icc`
    (`{1,…,n·|A|}`): since each element is `≤ n`, `∑ A ≤ n·|A|`, so this interval
    is contained in the coarser one, and by `sum_mem_subsetSums` its right endpoint
    is attained. -/
theorem subsetSums_subset_Icc_sum {A : Finset ℕ}
    (hlo : ∀ a ∈ A, 1 ≤ a) :
    subsetSums A ⊆ Finset.Icc 1 (A.sum id) := by
  intro s hs
  rw [Finset.mem_Icc]
  exact ⟨subsetSums_pos hlo s hs, subsetSums_le_sum s hs⟩

/-- **The maximum subset sum is the total.**  For a non-empty set the largest of
    its non-empty subset sums is exactly `∑ A`: it is attained (by the full subset,
    `sum_mem_subsetSums`) and dominates all others (`subsetSums_le_sum`). -/
theorem max'_subsetSums_eq_sum {A : Finset ℕ} (hA : A.Nonempty) :
    (subsetSums A).max' (subsetSums_nonempty hA) = A.sum id :=
  le_antisymm
    (Finset.max'_le _ _ _ (fun s hs => subsetSums_le_sum s hs))
    (Finset.le_max' _ _ (sum_mem_subsetSums hA))

/-- **Every subset sum dominates the minimum element.**  For a non-empty subset
    `S ⊆ A` the sum bounds any one of its (non-negative) summands, and each summand
    lies in `A`, so the sum is at least `A.min'` — the smallest element of `A`. -/
theorem min'_le_subsetSums {A : Finset ℕ} (hA : A.Nonempty) :
    ∀ s ∈ subsetSums A, A.min' hA ≤ s := by
  intro s hs
  unfold subsetSums nonemptySubsets at hs
  rw [Finset.mem_image] at hs
  obtain ⟨S, hS, rfl⟩ := hs
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  obtain ⟨hSsub, hSne⟩ := hS
  obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hSne
  calc A.min' hA ≤ b := Finset.min'_le _ _ (hSsub hb)
    _ ≤ S.sum id := Finset.single_le_sum (fun i _ => Nat.zero_le (id i)) hb

/-- **The minimum subset sum is the minimum element.**  Dual to
    `max'_subsetSums_eq_sum`: the smallest of the non-empty subset sums of a
    non-empty set is exactly `A.min'` — attained by the singleton `{A.min'}`
    (`subset_subsetSums`) and a lower bound for every subset sum
    (`min'_le_subsetSums`).  Together with `max'_subsetSums_eq_sum` this pins down
    *both* endpoints of the subset-sum range: `[A.min', ∑ A]`. -/
theorem min'_subsetSums_eq_min' {A : Finset ℕ} (hA : A.Nonempty) :
    (subsetSums A).min' (subsetSums_nonempty hA) = A.min' hA :=
  le_antisymm
    (Finset.min'_le _ _ (subset_subsetSums A (A.min'_mem hA)))
    (Finset.le_min' _ _ _ (min'_le_subsetSums hA))

/-- **Insertion recursion for subset sums.**  For a fresh element `a ∉ A`, the
    non-empty subsets of `insert a A` split into three disjoint families: those
    avoiding `a` (contributing `subsetSums A`), the singleton `{a}` (contributing
    `a`), and those of the form `insert a S'` with `S' ⊆ A` non-empty (contributing
    `a + s` for `s ∈ subsetSums A`).  Hence

    `subsetSums (insert a A) = insert a (subsetSums A ∪ (subsetSums A).image (a + ·))`.

    This computes the subset-sum set of an explicit construction one generator at a
    time — the recursive tool for analysing candidate lower-bound configurations. -/
theorem subsetSums_insert {a : ℕ} {A : Finset ℕ} (ha : a ∉ A) :
    subsetSums (insert a A)
      = insert a (subsetSums A ∪ (subsetSums A).image (a + ·)) := by
  ext s
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  constructor
  · intro hs
    unfold subsetSums nonemptySubsets at hs
    rw [Finset.mem_image] at hs
    obtain ⟨S, hS, rfl⟩ := hs
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSsub, hSne⟩ := hS
    by_cases haS : a ∈ S
    · -- `S` contains `a`; write `S = insert a S'` with `S' = S.erase a ⊆ A`.
      have hSeq : S = insert a (S.erase a) := (Finset.insert_erase haS).symm
      have haS' : a ∉ S.erase a := Finset.not_mem_erase a S
      have hS'A : S.erase a ⊆ A := by
        intro x hx
        have hxS : x ∈ S := Finset.mem_of_mem_erase hx
        have hxa : x ≠ a := Finset.ne_of_mem_erase hx
        rcases Finset.mem_insert.mp (hSsub hxS) with h | h
        · exact absurd h hxa
        · exact h
      have hsum : S.sum id = a + (S.erase a).sum id := by
        simp [hSeq, Finset.sum_insert haS']
      by_cases hS'e : (S.erase a).Nonempty
      · -- non-empty remainder ⟹ a value of the shifted image `a + subsetSums A`
        right; right
        refine ⟨(S.erase a).sum id, ?_, hsum.symm⟩
        unfold subsetSums nonemptySubsets
        rw [Finset.mem_image]
        refine ⟨S.erase a, ?_, rfl⟩
        rw [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨hS'A, Finset.nonempty_iff_ne_empty.mp hS'e⟩
      · -- empty remainder ⟹ the value is `a` itself
        left
        rw [Finset.not_nonempty_iff_eq_empty] at hS'e
        rw [hsum, hS'e, Finset.sum_empty, Nat.add_zero]
    · -- `S` avoids `a`, hence `S ⊆ A`
      right; left
      have hSA : S ⊆ A := by
        intro x hx
        rcases Finset.mem_insert.mp (hSsub hx) with h | h
        · exact absurd (h ▸ hx) haS
        · exact h
      unfold subsetSums nonemptySubsets
      rw [Finset.mem_image]
      refine ⟨S, ?_, rfl⟩
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hSA, hSne⟩
  · intro hs
    rcases hs with rfl | h | ⟨t, ht, rfl⟩
    · -- `s = a`: the singleton `{a}` is a non-empty subset of `insert a A`
      exact subset_subsetSums (insert a A) (Finset.mem_insert_self a A)
    · -- `s ∈ subsetSums A`: monotonicity along `A ⊆ insert a A`
      exact subsetSums_mono (Finset.subset_insert a A) h
    · -- `s = a + t` with `t ∈ subsetSums A`: adjoin `a` to a witness subset of `t`
      unfold subsetSums nonemptySubsets at ht
      rw [Finset.mem_image] at ht
      obtain ⟨S', hS', rfl⟩ := ht
      rw [Finset.mem_filter, Finset.mem_powerset] at hS'
      obtain ⟨hS'A, hS'ne⟩ := hS'
      have haS' : a ∉ S' := fun h => ha (hS'A h)
      unfold subsetSums nonemptySubsets
      rw [Finset.mem_image]
      refine ⟨insert a S', ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_powerset]
        exact ⟨Finset.insert_subset_insert a hS'A, Finset.insert_ne_empty a S'⟩
      · simp [Finset.sum_insert haS']

/-- **Doubling law in the superincreasing regime.**  If a fresh element `a`
    strictly exceeds the whole total `∑ A` (so `a` is larger than every subset sum),
    then the three families of the insertion recursion are pairwise disjoint: the
    old sums lie in `[1, ∑ A]`, the value `a` exceeds them all, and the shifted sums
    `a + s` (with `s ≥ 1`) exceed even `a`.  Consequently the count exactly doubles
    and gains one:

    `|subsetSums (insert a A)| = 2 · |subsetSums A| + 1`.

    Iterated from `∅`, this is precisely why a superincreasing sequence realises the
    full `2^{|A|} − 1` distinct subset sums of `subsetSums_card_le` — the extremal
    (distinct-subset-sum) side of the counting picture. -/
theorem subsetSums_card_insert_superincreasing
    {a : ℕ} {A : Finset ℕ} (ha : a ∉ A)
    (hlo : ∀ x ∈ A, 1 ≤ x) (hgt : A.sum id < a) :
    (subsetSums (insert a A)).card = 2 * (subsetSums A).card + 1 := by
  -- `a` is above every old subset sum, so `a ∉ subsetSums A`.
  have h_a_notin : a ∉ subsetSums A := fun h =>
    absurd (subsetSums_le_sum a h) (not_le.mpr hgt)
  -- the shift `a + ·` is injective, so the shifted image has the same cardinality.
  have h_img_card : ((subsetSums A).image (a + ·)).card = (subsetSums A).card :=
    Finset.card_image_of_injective _ (add_right_injective a)
  -- old sums (`≤ ∑ A < a`) are disjoint from shifted sums (`= a + s ≥ a + 1`).
  have h_disj : Disjoint (subsetSums A) ((subsetSums A).image (a + ·)) := by
    rw [Finset.disjoint_left]
    intro y hy hyimg
    rw [Finset.mem_image] at hyimg
    obtain ⟨s, _, rfl⟩ := hyimg
    have hle : a + s ≤ A.sum id := subsetSums_le_sum (a + s) hy
    omega
  -- `a` is in neither family.
  have h_a_notin_union :
      a ∉ subsetSums A ∪ (subsetSums A).image (a + ·) := by
    simp only [Finset.mem_union, not_or]
    refine ⟨h_a_notin, ?_⟩
    intro hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨s, hs, hEq⟩ := hmem
    have hs1 : 1 ≤ s := subsetSums_pos hlo s hs
    omega
  rw [subsetSums_insert ha, Finset.card_insert_of_not_mem h_a_notin_union,
    Finset.card_union_of_disjoint h_disj, h_img_card]
  ring

end Erdos882OQ03
