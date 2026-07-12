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
        conv_lhs => rw [hSeq]
        rw [Finset.sum_insert haS']
        simp only [id_eq]
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
    rcases hs with heq | h | ⟨t, ht, rfl⟩
    · -- `s = a`: the singleton `{a}` is a non-empty subset of `insert a A`
      subst s
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

/-- **Superincreasing set.**  A finite set of naturals in which every element
    strictly exceeds the sum of all *strictly smaller* elements.  This is the
    classical "superincreasing sequence" condition, phrased order-agnostically for
    a `Finset`: the standard powers-of-two example `{1,2,4,…,2^{k-1}}` qualifies.
    Superincreasing sets are exactly the ones whose non-empty subset sums are all
    distinct — the extremal regime of `subsetSums_card_le`. -/
def Superincreasing (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, (A.filter (· < a)).sum id < a

/-- Elements of a superincreasing set are positive: each exceeds the sum of the
    smaller elements, which is `≥ 0`. -/
theorem Superincreasing.pos {A : Finset ℕ} (hA : Superincreasing A) :
    ∀ a ∈ A, 1 ≤ a := by
  intro a ha
  have := hA a ha
  omega

/-- **Superincreasing-ness is hereditary.**  Passing to a subset only removes
    smaller elements, so the defining inequality is preserved (the truncated sum
    can only shrink). -/
theorem Superincreasing.mono {A B : Finset ℕ} (h : B ⊆ A)
    (hA : Superincreasing A) : Superincreasing B := by
  intro b hb
  have hsub : B.filter (· < b) ⊆ A.filter (· < b) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨h hx.1, hx.2⟩
  calc (B.filter (· < b)).sum id
      ≤ (A.filter (· < b)).sum id := Finset.sum_le_sum_of_subset hsub
    _ < b := hA b (h hb)

/-- In a superincreasing set the maximum element exceeds the sum of all the
    others: the elements strictly below the max are precisely the rest of the set
    (`A.erase (max)`), and the superincreasing condition at the max bounds their
    total.  This is exactly the hypothesis `∑ (rest) < max` needed to fire the
    doubling law `subsetSums_card_insert_superincreasing`. -/
theorem sum_erase_max_lt {A : Finset ℕ} (hA : Superincreasing A)
    (hne : A.Nonempty) :
    (A.erase (A.max' hne)).sum id < A.max' hne := by
  have hfilter : A.filter (· < A.max' hne) = A.erase (A.max' hne) := by
    ext x
    rw [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hxA, hxlt⟩
      exact ⟨ne_of_lt hxlt, hxA⟩
    · rintro ⟨hxne, hxA⟩
      exact ⟨hxA, lt_of_le_of_ne (Finset.le_max' A x hxA) hxne⟩
  have := hA (A.max' hne) (A.max'_mem hne)
  rwa [hfilter] at this

/-- **Superincreasing ⟹ all subset sums distinct (extremal counting).**  A
    superincreasing set of `k` elements realises the full `2^k − 1` distinct
    non-empty subset sums, meeting the upper bound `subsetSums_card_le` with
    equality.  Proof: strong induction removing the maximum `m`; since
    `∑ (A.erase m) < m` (`sum_erase_max_lt`) the doubling law gives
    `|subsetSums A| = 2·|subsetSums (A.erase m)| + 1`, and `A.erase m` is again
    superincreasing (`Superincreasing.mono`).  This is the exact converse of the
    collapse regime: it certifies that the powers-of-two construction attains the
    maximum possible number of distinct subset sums. -/
theorem subsetSums_card_superincreasing :
    ∀ {A : Finset ℕ}, Superincreasing A →
      (subsetSums A).card = 2 ^ A.card - 1 := by
  intro A
  induction A using Finset.strongInduction with
  | _ A ih =>
    intro hA
    rcases A.eq_empty_or_nonempty with rfl | hne
    · simp [subsetSums, nonemptySubsets, Finset.powerset_empty]
    · set m := A.max' hne with hm
      have hmem : m ∈ A := A.max'_mem hne
      have hEq : A = insert m (A.erase m) := (Finset.insert_erase hmem).symm
      have hnotmem : m ∉ A.erase m := Finset.not_mem_erase m A
      have hsub : A.erase m ⊂ A := Finset.erase_ssubset hmem
      have hAe : Superincreasing (A.erase m) := hA.mono (Finset.erase_subset m A)
      have hgt : (A.erase m).sum id < m := sum_erase_max_lt hA hne
      have hdouble : (subsetSums A).card
          = 2 * (subsetSums (A.erase m)).card + 1 := by
        conv_lhs => rw [hEq]
        exact subsetSums_card_insert_superincreasing hnotmem hAe.pos hgt
      have hcard : (A.erase m).card = A.card - 1 := Finset.card_erase_of_mem hmem
      have hpos : 1 ≤ A.card := Finset.card_pos.mpr hne
      have hple : (1 : ℕ) ≤ 2 ^ (A.card - 1) := Nat.one_le_two_pow
      have h2 : 2 * 2 ^ (A.card - 1) = 2 ^ A.card := by
        rw [← pow_succ']
        congr 1
        omega
      rw [hdouble, ih (A.erase m) hsub hAe, hcard]
      omega

/-- **The counting bound `subsetSums_card_le` is tight for every size.** For each `k`
    there is a `k`-element superincreasing set of naturals whose non-empty subset sums
    are all distinct, realising the full `2^k − 1` possible values. Built by induction:
    insert a fresh element `m = (∑ A) + 1` strictly above the running sum, so `m` is a
    new maximum, `insert m A` stays superincreasing, and the doubling law
    `subsetSums_card_insert_superincreasing` fires. This certifies that the `2^k − 1`
    in `subsetSums_card_le` cannot be lowered — the powers-of-two regime is optimal. -/
theorem exists_superincreasing_extremal (k : ℕ) :
    ∃ A : Finset ℕ, A.card = k ∧ Superincreasing A ∧
      (subsetSums A).card = 2 ^ k - 1 := by
  induction k with
  | zero =>
    refine ⟨∅, by simp, ?_, ?_⟩
    · intro a ha; simp at ha
    · simp [subsetSums, nonemptySubsets, Finset.powerset_empty]
  | succ k ih =>
    obtain ⟨A, hcard, hSI, hsum⟩ := ih
    set m := A.sum id + 1 with hm
    have hmnot : m ∉ A := by
      intro hmA
      have hle : m ≤ A.sum id := Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le _) hmA
      omega
    have hgt : A.sum id < m := by omega
    have hSI' : Superincreasing (insert m A) := by
      intro a ha
      rw [Finset.mem_insert] at ha
      rcases ha with rfl | haA
      · -- a = m : the smaller elements are exactly all of A, summing to ∑A < m
        have hfil : (insert m A).filter (· < m) = A := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hx | hx, hlt⟩
            · exact absurd hlt (by rw [hx]; exact lt_irrefl m)
            · exact hx
          · intro hxA
            refine ⟨Or.inr hxA, ?_⟩
            have hxle : x ≤ A.sum id :=
              Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le _) hxA
            omega
        rw [hfil]; omega
      · -- a ∈ A : m exceeds a, so the smaller-element set is unchanged
        have ham : a ≤ A.sum id :=
          Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le _) haA
        have hfil : (insert m A).filter (· < a) = A.filter (· < a) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hx | hx, hlt⟩
            · rw [hx] at hlt; exact absurd hlt (by omega)
            · exact ⟨hx, hlt⟩
          · rintro ⟨hxA, hlt⟩; exact ⟨Or.inr hxA, hlt⟩
        rw [hfil]; exact hSI a haA
    refine ⟨insert m A, ?_, hSI', ?_⟩
    · rw [Finset.card_insert_of_not_mem hmnot, hcard]
    · have hdouble := subsetSums_card_insert_superincreasing hmnot hSI.pos hgt
      have hk1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      rw [hdouble, hsum]; omega

/-! ## The canonical powers-of-two witness

`exists_superincreasing_extremal` builds *some* `k`-element superincreasing set
abstractly (inserting a fresh element one above the running sum).  Here we exhibit
the canonical named family `{2^0, 2^1, …, 2^{k-1}} = {1, 2, 4, …}` explicitly and
verify it is superincreasing, has exactly `k` elements, and hence — via
`subsetSums_card_superincreasing` — realises all `2^k − 1` distinct non-empty
subset sums.  This is the concrete instantiation the existence theorem abstracts:
every value in `[1, 2^k − 1]` is uniquely a subset sum (binary representation). -/

/-- The powers-of-two set `{2^0, …, 2^{k-1}} = {1, 2, 4, …, 2^{k-1}}`. -/
def powersOfTwo (k : ℕ) : Finset ℕ := (Finset.range k).image (2 ^ ·)

@[simp] theorem mem_powersOfTwo {k x : ℕ} :
    x ∈ powersOfTwo k ↔ ∃ i < k, 2 ^ i = x := by
  simp [powersOfTwo]

/-- `{2^0,…,2^{k-1}}` has exactly `k` elements — the exponent map `2^·` is
    injective (`Nat.pow_right_injective`). -/
theorem powersOfTwo_card (k : ℕ) : (powersOfTwo k).card = k := by
  rw [powersOfTwo,
      Finset.card_image_of_injective _ (Nat.pow_right_injective (le_refl 2)),
      Finset.card_range]

/-- **The powers-of-two family is superincreasing.**  For each element `2^i` the
    strictly smaller elements are exactly `{2^0, …, 2^{i-1}}`, whose total is the
    geometric sum `2^i − 1 < 2^i`. -/
theorem superincreasing_powersOfTwo (k : ℕ) : Superincreasing (powersOfTwo k) := by
  intro a ha
  rw [mem_powersOfTwo] at ha
  obtain ⟨i, hik, rfl⟩ := ha
  -- the elements strictly below `2^i` are precisely `{2^j : j < i}`
  have hfil : (powersOfTwo k).filter (· < 2 ^ i) = (Finset.range i).image (2 ^ ·) := by
    ext x
    simp only [Finset.mem_filter, mem_powersOfTwo, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨j, _, rfl⟩, hlt⟩
      exact ⟨j, (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt, rfl⟩
    · rintro ⟨j, hji, rfl⟩
      exact ⟨⟨j, lt_trans hji hik, rfl⟩, (Nat.pow_lt_pow_iff_right (by norm_num)).mpr hji⟩
  rw [hfil]
  -- ∑_{j<i} 2^j = 2^i − 1
  have hsum : ((Finset.range i).image (2 ^ ·)).sum id = 2 ^ i - 1 := by
    rw [Finset.sum_image (fun x _ y _ h => Nat.pow_right_injective (le_refl 2) h)]
    simp only [id_eq]
    rw [Nat.geomSum_eq (le_refl 2) i]
    norm_num
  rw [hsum]
  have : 1 ≤ 2 ^ i := Nat.one_le_two_pow
  omega

/-- **The powers-of-two family attains the extremal subset-sum count.**  For every
    `k`, the canonical set `{2^0,…,2^{k-1}}` has exactly `2^k − 1` distinct non-empty
    subset sums — the concrete named witness realising the tight bound of
    `subsetSums_card_le` (cf. the abstract `exists_superincreasing_extremal`). -/
theorem subsetSums_card_powersOfTwo (k : ℕ) :
    (subsetSums (powersOfTwo k)).card = 2 ^ k - 1 := by
  have h := subsetSums_card_superincreasing (superincreasing_powersOfTwo k)
  rwa [powersOfTwo_card] at h

/-- The total of the powers-of-two family is the geometric sum
    `∑_{i<k} 2^i = 2^k − 1`. -/
theorem sum_powersOfTwo (k : ℕ) : (powersOfTwo k).sum id = 2 ^ k - 1 := by
  rw [powersOfTwo,
      Finset.sum_image (fun x _ y _ h => Nat.pow_right_injective (le_refl 2) h)]
  simp only [id_eq]
  rw [Nat.geomSum_eq (le_refl 2) k]
  norm_num

/-- **Binary representation: the powers-of-two family realises the full interval.**
    `subsetSums {2^0,…,2^{k-1}} = {1,…,2^k − 1}`.  The counting theorem
    `subsetSums_card_powersOfTwo` gives only the *number* `2^k − 1` of distinct
    subset sums; here we identify them *exactly* as the initial interval, delivering
    on the docstring promise that "every value in `[1, 2^k − 1]` is uniquely a subset
    sum (binary representation)".  Proof: the subset sums are trapped in
    `[1, ∑ = 2^k − 1]` (`subsetSums_pos`, `subsetSums_le_sum`, `sum_powersOfTwo`) and
    number exactly `2^k − 1 = |Icc 1 (2^k − 1)|`, so the containment is an equality by
    cardinality. -/
theorem subsetSums_powersOfTwo (k : ℕ) :
    subsetSums (powersOfTwo k) = Finset.Icc 1 (2 ^ k - 1) := by
  apply Finset.eq_of_subset_of_card_le
  · intro s hs
    rw [Finset.mem_Icc]
    refine ⟨subsetSums_pos (superincreasing_powersOfTwo k).pos s hs, ?_⟩
    have hle := subsetSums_le_sum s hs
    rwa [sum_powersOfTwo] at hle
  · rw [Nat.card_Icc, subsetSums_card_powersOfTwo]
    omega

/-- **Existence half of the binary-representation identity.**  Every value
    `m ∈ [1, 2^k − 1]` occurs as a subset sum of `{2^0,…,2^{k-1}}` — its binary
    expansion selects the subset.  Immediate from the set equality
    `subsetSums_powersOfTwo`. -/
theorem mem_subsetSums_powersOfTwo {k m : ℕ} (h1 : 1 ≤ m) (h2 : m ≤ 2 ^ k - 1) :
    m ∈ subsetSums (powersOfTwo k) := by
  rw [subsetSums_powersOfTwo, Finset.mem_Icc]
  exact ⟨h1, h2⟩

/-!
### The counting-extremal regime is NOT the Erdős #882 validity regime

Everything above characterises the sets that *maximise* the number of distinct
non-empty subset sums: superincreasing sets, and the canonical witness
`{2^0,…,2^{k-1}}`.  Erdős #882, however, asks for sets whose subset sums are
**divisibility-free** (`ValidSubset`), and these two optimality notions are
genuinely different — indeed *incompatible* on the extremal family.  The reason is
elementary: the powers-of-two family contains `1` as a subset sum, and `1` divides
everything, so no set of subset sums containing `1` alongside any other value can be
divisibility-free.  Thus the subset-sum *counting* champion is the *worst possible*
candidate for the divisibility-free problem.  These lemmas make that separation
precise, closing the gap flagged in the file's research notes.
-/

/-- **A subset sum equal to `1` destroys divisibility-freeness.**  If `1 ∈ S` and `S`
has any other element `b ≠ 1`, then `S` is not divisibility-free: `1 ∣ b` violates the
`¬(1 ∣ b)` clause.  (`1` divides every natural, so it can never coexist with a second
value in a divisibility-free set.) -/
theorem not_divisibilityFree_of_one_mem {S : Finset ℕ} (h1 : 1 ∈ S)
    (hb : ∃ b ∈ S, b ≠ 1) : ¬ DivisibilityFree S := by
  obtain ⟨b, hbS, hb1⟩ := hb
  intro hdf
  exact (hdf 1 h1 b hbS (fun h => hb1 h.symm)).1 (one_dvd b)

/-- **The extremal powers-of-two family has non-divisibility-free subset sums.**
For `k ≥ 2` the counting-optimal set `{2^0,…,2^{k-1}}` (which realises all `2^k − 1`
distinct subset sums) fails the Erdős #882 constraint: both `1 = 2^0` and `2 = 2^1`
are subset sums, and `1 ∣ 2`.  So maximising the subset-sum *count* is directly at
odds with divisibility-freeness. -/
theorem not_divisibilityFree_subsetSums_powersOfTwo {k : ℕ} (hk : 2 ≤ k) :
    ¬ DivisibilityFree (subsetSums (powersOfTwo k)) := by
  have h1mem : (1 : ℕ) ∈ powersOfTwo k := by
    rw [mem_powersOfTwo]; exact ⟨0, by omega, by norm_num⟩
  have h2mem : (2 : ℕ) ∈ powersOfTwo k := by
    rw [mem_powersOfTwo]; exact ⟨1, by omega, by norm_num⟩
  have h1 : (1 : ℕ) ∈ subsetSums (powersOfTwo k) := subset_subsetSums _ h1mem
  have h2 : (2 : ℕ) ∈ subsetSums (powersOfTwo k) := subset_subsetSums _ h2mem
  exact not_divisibilityFree_of_one_mem h1 ⟨2, h2, by norm_num⟩

/-- **Subset-sum counting-extremality does not imply Erdős #882 validity.**
For every `k ≥ 2` there is a `k`-element superincreasing set — realising the full
`2^k − 1` distinct non-empty subset sums (`subsetSums_card_superincreasing`) — whose
subset sums are *not* divisibility-free.  Witnessed by `{2^0,…,2^{k-1}}`.  This
cleanly separates the two extremal regimes: the family that maximises the number of
subset sums is exactly the one that maximally violates the divisibility-free
condition, so Erdős #882's optimum lies strictly away from the superincreasing
champion. -/
theorem exists_superincreasing_not_divisibilityFree {k : ℕ} (hk : 2 ≤ k) :
    ∃ A : Finset ℕ, Superincreasing A ∧ A.card = k ∧
      ¬ DivisibilityFree (subsetSums A) :=
  ⟨powersOfTwo k, superincreasing_powersOfTwo k, powersOfTwo_card k,
    not_divisibilityFree_subsetSums_powersOfTwo hk⟩

end Erdos882OQ03
