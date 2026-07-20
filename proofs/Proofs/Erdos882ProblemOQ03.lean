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

set_option autoImplicit false

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

/-- The empty set is divisibility-free (vacuously). -/
theorem divisibilityFree_empty : DivisibilityFree (∅ : Finset ℕ) :=
  fun a ha => absurd ha (Finset.notMem_empty a)

/-- Every singleton is divisibility-free (vacuously — there are no two *distinct*
    elements to divide one another). -/
theorem divisibilityFree_singleton (a : ℕ) : DivisibilityFree ({a} : Finset ℕ) := by
  intro x hx y hy hxy
  rw [Finset.mem_singleton] at hx hy
  exact absurd (hx.trans hy.symm) hxy

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

/-- **Every singleton `{a} ⊆ {1,…,n}` is a valid subset.**  Its only non-empty subset
    sum is `a` itself (`subsetSums {a} = {a}`), and a singleton set of sums is trivially
    divisibility-free (`divisibilityFree_singleton`).  So the extremal sets `A` of Erdős
    #882 always exist for every size `1` — the base case of the `(1+o(1))log₂ n` growth,
    and a concrete witness that `ValidSubset n` is non-vacuous for all `n ≥ 1`. -/
theorem validSubset_singleton {n a : ℕ} (h1 : 1 ≤ a) (h2 : a ≤ n) :
    ValidSubset n {a} := by
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [Finset.mem_singleton] at hx; subst hx; exact ⟨h1, h2⟩
  · rw [subsetSums_singleton]; exact divisibilityFree_singleton a

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
      have haS' : a ∉ S.erase a := Finset.notMem_erase a S
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
  rw [subsetSums_insert ha, Finset.card_insert_of_notMem h_a_notin_union,
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
      have hnotmem : m ∉ A.erase m := Finset.notMem_erase m A
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
    · rw [Finset.card_insert_of_notMem hmnot, hcard]
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

/-!
### The distinct-subset-sum total lower bound (`∑ A ≥ 2^{|A|} − 1`)

The counting bound `subsetSums_card_le` caps the number of distinct non-empty
subset sums at `2^{|A|} − 1`.  When that maximum is *attained* — i.e. all
non-empty subset sums are pairwise distinct, the counting-extremal regime — the
`2^{|A|} − 1` distinct values are forced to fit inside the attained interval
`[1, ∑ A]` (`subsetSums_subset_Icc_sum`).  Cardinality then pins the total from
below: `∑ A ≥ 2^{|A|} − 1`.  This is the classical distinct-subset-sum
phenomenon (the Erdős distinct-subset-sum / Conway–Guy circle): a set with
distinct subset sums must have exponentially large total, so with all elements
`≤ n` its size is `O(log₂ n)` — the quantitative face of the `(1+o(1))log₂ n`
growth.  The bound is *sharp*: the powers-of-two witness has `∑ = 2^k − 1`
exactly.
-/

/-- **Distinct subset sums.**  `A` realises the maximum possible number of
    distinct non-empty subset sums, `2^{|A|} − 1` — i.e. the counting bound
    `subsetSums_card_le` is met with equality.  Superincreasing sets (in
    particular the powers-of-two family) satisfy this; it is the exact opposite
    of the "collapse" regime where many subsets share a sum. -/
def DistinctSubsetSums (A : Finset ℕ) : Prop :=
  (subsetSums A).card = 2 ^ A.card - 1

/-- Superincreasing sets have distinct subset sums — a restatement of
    `subsetSums_card_superincreasing` in the named predicate. -/
theorem Superincreasing.distinctSubsetSums {A : Finset ℕ}
    (hA : Superincreasing A) : DistinctSubsetSums A :=
  subsetSums_card_superincreasing hA

/-- The powers-of-two family `{2^0,…,2^{k-1}}` has distinct subset sums. -/
theorem powersOfTwo_distinctSubsetSums (k : ℕ) :
    DistinctSubsetSums (powersOfTwo k) :=
  (superincreasing_powersOfTwo k).distinctSubsetSums

/-- **Distinct-subset-sum total lower bound.**  If the non-empty subset sums of a
    set of positive integers are all distinct (`DistinctSubsetSums`), then the
    total is at least `2^{|A|} − 1`.  The `2^{|A|} − 1` distinct sums all live in
    `[1, ∑ A]` (`subsetSums_subset_Icc_sum`), an interval of exactly `∑ A`
    integers, so `2^{|A|} − 1 = |subsetSums A| ≤ ∑ A`.  Sharp: the powers-of-two
    witness attains equality (`sum_powersOfTwo_eq_bound`). -/
theorem two_pow_sub_one_le_sum_of_distinct {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 1 ≤ a) (hd : DistinctSubsetSums A) :
    2 ^ A.card - 1 ≤ A.sum id := by
  have hsub : subsetSums A ⊆ Finset.Icc 1 (A.sum id) :=
    subsetSums_subset_Icc_sum hpos
  have hcard : (subsetSums A).card ≤ (Finset.Icc 1 (A.sum id)).card :=
    Finset.card_le_card hsub
  rw [Nat.card_Icc, hd] at hcard
  omega

/-- **The powers-of-two witness attains the total lower bound.**  For the
    canonical distinct-subset-sum set `{2^0,…,2^{k-1}}` the total is *exactly*
    `2^{|A|} − 1`, so `two_pow_sub_one_le_sum_of_distinct` cannot be improved. -/
theorem sum_powersOfTwo_eq_bound (k : ℕ) :
    (powersOfTwo k).sum id = 2 ^ (powersOfTwo k).card - 1 := by
  rw [sum_powersOfTwo, powersOfTwo_card]

/-- **Quantitative `O(log₂ n)` size bound for distinct-subset-sum sets.**  If the
    non-empty subset sums of `A ⊆ {1,…,n}` are all distinct, then
    `2^{|A|} ≤ n·|A| + 1`.  Combining the total lower bound
    `2^{|A|} − 1 ≤ ∑ A` (`two_pow_sub_one_le_sum_of_distinct`) with the trivial
    `∑ A ≤ n·|A|` forces `|A|` to be logarithmic in `n`: this is the quantitative
    heart of the `(1+o(1))log₂ n` growth in the counting-extremal regime. -/
theorem two_pow_le_of_distinct_bounded {A : Finset ℕ} {n : ℕ}
    (hpos : ∀ a ∈ A, 1 ≤ a) (hle : ∀ a ∈ A, a ≤ n) (hd : DistinctSubsetSums A) :
    2 ^ A.card ≤ n * A.card + 1 := by
  have h1 : 2 ^ A.card - 1 ≤ A.sum id := two_pow_sub_one_le_sum_of_distinct hpos hd
  have h2 : A.sum id ≤ n * A.card := by
    calc A.sum id ≤ ∑ _a ∈ A, n := Finset.sum_le_sum (fun i hi => hle i hi)
      _ = n * A.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hp : 1 ≤ 2 ^ A.card := Nat.one_le_two_pow
  omega

/-- **Explicit `log₂` cardinality bound for distinct-subset-sum sets.**  Rewriting the
    quantitative bound `two_pow_le_of_distinct_bounded` (`2^{|A|} ≤ n·|A|+1`) through
    `Nat.pow_le_iff_le_log` turns it into a statement on the cardinality itself:
    `|A| ≤ log₂(n·|A|+1)`.  This is the closed logarithmic form of the `O(log₂ n)` growth —
    the right-hand side still mentions `|A|`, but since `log₂(n·|A|+1) = log₂|A| + log₂ n +
    O(1)` grows only logarithmically in `|A|`, the inequality already pins `|A|` to
    `(1+o(1))·log₂ n`.  Discharging the `Nat.log` step was the standing next task after
    `two_pow_le_of_distinct_bounded`. -/
theorem card_le_log_of_distinct_bounded {A : Finset ℕ} {n : ℕ}
    (hpos : ∀ a ∈ A, 1 ≤ a) (hle : ∀ a ∈ A, a ≤ n) (hd : DistinctSubsetSums A) :
    A.card ≤ Nat.log 2 (n * A.card + 1) := by
  have h := two_pow_le_of_distinct_bounded hpos hle hd
  exact (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mpr h

/-!
## Distinct-subset-sums: the injectivity meaning, and its heredity

`DistinctSubsetSums A` was defined by the *cardinality* equation `|subsetSums A| = 2^|A| − 1`
— the counting bound `subsetSums_card_le` met with equality. Since `subsetSums A` is the image
of the `2^|A| − 1` non-empty subsets under the sum map (`nonemptySubsets_card`), that equation
holds exactly when the sum map is **injective** on the non-empty subsets — i.e. distinct
non-empty subsets have distinct sums. This section records that characterization
(`distinctSubsetSums_iff_injOn`, `distinctSubsetSums_iff_pairwise`) and the structural
consequence it unlocks: **`DistinctSubsetSums` is downward closed** (`DistinctSubsetSums.mono`),
the exact analogue of `Superincreasing.mono` and `DivisibilityFree.mono`, and the WLOG
"pass to a sub-configuration" tool for the distinct-subset-sum regime. All axiom-free. -/

/-- **Non-empty subsets grow with the set.**  `B ⊆ A ⟹ nonemptySubsets B ⊆ nonemptySubsets A`:
    a non-empty subset of `B` is a non-empty subset of `A`.  (The `nonemptySubsets` companion of
    `subsetSums_mono`.) -/
theorem nonemptySubsets_mono {A B : Finset ℕ} (h : B ⊆ A) :
    nonemptySubsets B ⊆ nonemptySubsets A := by
  intro S hS
  unfold nonemptySubsets at hS ⊢
  rw [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
  exact ⟨hS.1.trans h, hS.2⟩

/-- **`DistinctSubsetSums` is injectivity of the sum map.**  `A` has distinct subset sums iff
    the map `S ↦ ∑ S` is injective on the non-empty subsets of `A`.  The cardinality definition
    `|subsetSums A| = 2^|A| − 1` is precisely `|image| = |domain|` (using `nonemptySubsets_card`),
    which is equivalent to injectivity of the map generating the image. -/
theorem distinctSubsetSums_iff_injOn {A : Finset ℕ} :
    DistinctSubsetSums A ↔ Set.InjOn (fun S : Finset ℕ => S.sum id) ↑(nonemptySubsets A) := by
  unfold DistinctSubsetSums subsetSums
  rw [← nonemptySubsets_card A]
  exact ⟨fun h => Finset.injOn_of_card_image_eq h, fun h => Finset.card_image_of_injOn h⟩

/-- **`DistinctSubsetSums`, spelled out.**  `A` has distinct subset sums iff any two non-empty
    subsets with equal sum are equal — the readable pairwise form of
    `distinctSubsetSums_iff_injOn`. -/
theorem distinctSubsetSums_iff_pairwise {A : Finset ℕ} :
    DistinctSubsetSums A ↔
      ∀ S ∈ nonemptySubsets A, ∀ T ∈ nonemptySubsets A, S.sum id = T.sum id → S = T := by
  rw [distinctSubsetSums_iff_injOn]
  exact ⟨fun h S hS T hT hst => h hS hT hst, fun h S hS T hT hst => h S hS T hT hst⟩

/-- **`DistinctSubsetSums` is hereditary (downward closed).**  Any subset of a set with distinct
    subset sums also has distinct subset sums: injectivity of the sum map on the non-empty
    subsets of `A` restricts to injectivity on the (fewer) non-empty subsets of `B ⊆ A`.  This is
    the WLOG "pass to a sub-configuration" tool for the distinct-subset-sum regime, mirroring
    `Superincreasing.mono` and `DivisibilityFree.mono`.  Strictly more general than
    `Superincreasing.mono`, since not every distinct-subset-sum set is superincreasing. -/
theorem DistinctSubsetSums.mono {A B : Finset ℕ} (h : B ⊆ A)
    (hA : DistinctSubsetSums A) : DistinctSubsetSums B := by
  rw [distinctSubsetSums_iff_injOn] at hA ⊢
  exact hA.mono (Finset.coe_subset.mpr (nonemptySubsets_mono h))

/-- **Every subset of the powers-of-two family has distinct subset sums.**  Immediate from
    `powersOfTwo_distinctSubsetSums` and heredity (`DistinctSubsetSums.mono`) — a large concrete
    supply of distinct-subset-sum sets of every size `≤ k`. -/
theorem distinctSubsetSums_of_subset_powersOfTwo {k : ℕ} {B : Finset ℕ}
    (h : B ⊆ powersOfTwo k) : DistinctSubsetSums B :=
  (powersOfTwo_distinctSubsetSums k).mono h

/-! ### Complementation / reflection symmetry of the subset-sum set

The map `s ↦ ∑ A − s` is the *complementation reflection*: a proper non-empty
subset `S ⊊ A` and its complement `A \ S` are both non-empty subsets of `A`
whose sums add up to the total `∑ A`.  Hence, away from its top point `∑ A`,
the value set `subsetSums A` is symmetric about `∑ A / 2`.  This is a
structural symmetry orthogonal to the counting / distinctness layer: it pins
the *shape* of the subset-sum set rather than its size.  Its sharpest
consequence is that the **largest proper subset sum is exactly `∑ A − A.min'`**
— the reflection-dual of `min'_subsetSums_eq_min'`. -/

/-- **Any non-empty subset's sum is a subset sum.**  The direct membership form:
    if `S ⊆ A` is non-empty then `∑ S ∈ subsetSums A`.  (Generalises
    `sum_mem_subsetSums`, which is the `S = A` case.) -/
theorem sum_mem_subsetSums_of_subset {A S : Finset ℕ} (hSA : S ⊆ A)
    (hS : S.Nonempty) : S.sum id ∈ subsetSums A := by
  unfold subsetSums nonemptySubsets
  rw [Finset.mem_image]
  refine ⟨S, ?_, rfl⟩
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hSA, Finset.nonempty_iff_ne_empty.mp hS⟩

/-- **Complementation / reflection symmetry.**  If `s` is a non-empty subset sum
    of `A` other than the total `∑ A`, its reflection `∑ A − s` is *also* a
    non-empty subset sum: any witnessing subset `S` (with `∑ S = s`) is proper
    (`∑ S ≠ ∑ A`), so its complement `A \ S` is a non-empty subset of `A` with
    `∑ (A \ S) = ∑ A − s`.  No positivity hypothesis is needed. -/
theorem subsetSums_reflection {A : Finset ℕ} {s : ℕ}
    (hs : s ∈ subsetSums A) (hne : s ≠ A.sum id) :
    A.sum id - s ∈ subsetSums A := by
  unfold subsetSums nonemptySubsets at hs
  rw [Finset.mem_image] at hs
  obtain ⟨S, hS, rfl⟩ := hs
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  obtain ⟨hSsub, hSne⟩ := hS
  have hSneA : S ≠ A := fun h => hne (by rw [h])
  have hcompl : (A \ S).Nonempty := by
    rw [Finset.sdiff_nonempty]
    exact fun hsub => hSneA (Finset.Subset.antisymm hSsub hsub)
  have hsplit : (A \ S).sum id + S.sum id = A.sum id := Finset.sum_sdiff hSsub
  have hval : (A \ S).sum id = A.sum id - S.sum id := by omega
  rw [← hval]
  exact sum_mem_subsetSums_of_subset Finset.sdiff_subset hcompl

/-- **The reflection is an involution on the proper subset sums.**  For a set of
    positive integers, a value `s` is a *proper* subset sum (a subset sum below
    the total, i.e. `s ∈ (subsetSums A).erase (∑ A)`) **iff** its reflection
    `∑ A − s` is.  Positivity guarantees a proper subset sum is `≥ 1`, so its
    reflection stays strictly below `∑ A` and never coincides with the removed
    top point.  Thus `s ↦ ∑ A − s` is a bijection of the proper subset sums. -/
theorem subsetSums_reflection_mem_erase_iff {A : Finset ℕ}
    (hlo : ∀ a ∈ A, 1 ≤ a) {s : ℕ} :
    s ∈ (subsetSums A).erase (A.sum id) ↔
      A.sum id - s ∈ (subsetSums A).erase (A.sum id) := by
  have fwd : ∀ t, t ∈ (subsetSums A).erase (A.sum id) →
      A.sum id - t ∈ (subsetSums A).erase (A.sum id) := by
    intro t ht
    rw [Finset.mem_erase] at ht ⊢
    obtain ⟨htne, htmem⟩ := ht
    have htpos : 1 ≤ t := subsetSums_pos hlo t htmem
    have htle : t ≤ A.sum id := subsetSums_le_sum t htmem
    exact ⟨by omega, subsetSums_reflection htmem htne⟩
  refine ⟨fwd s, fun h => ?_⟩
  have h2 := fwd _ h
  have hpos : 1 ≤ A.sum id - s := subsetSums_pos hlo _ (Finset.mem_of_mem_erase h)
  rwa [show A.sum id - (A.sum id - s) = s from by omega] at h2

/-- **Dropping one element yields a subset sum.**  For a set with at least two
    elements, removing any single element `a` leaves a non-empty subset, so the
    "co-total" `∑ A − a` is itself a non-empty subset sum. -/
theorem sum_erase_mem_subsetSums {A : Finset ℕ} {a : ℕ} (ha : a ∈ A)
    (hcard : 1 < A.card) : A.sum id - a ∈ subsetSums A := by
  have hne : (A.erase a).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem ha]; omega
  have hval : (A.erase a).sum id = A.sum id - a := by
    have h := Finset.add_sum_erase A id ha
    simp only [id_eq] at h ⊢
    omega
  rw [← hval]
  exact sum_mem_subsetSums_of_subset (Finset.erase_subset a A) hne

/-- **The co-total `∑ A − A.min'` is a subset sum.**  Instance of
    `sum_erase_mem_subsetSums` with `a = A.min'`: drop the smallest element. -/
theorem sum_sub_min'_mem_subsetSums {A : Finset ℕ} (hA : A.Nonempty)
    (hcard : 1 < A.card) : A.sum id - A.min' hA ∈ subsetSums A :=
  sum_erase_mem_subsetSums (A.min'_mem hA) hcard

/-- **Every proper subset sum is at most `∑ A − A.min'`.**  If `s` is a subset
    sum below the total then, by reflection, `∑ A − s` is a subset sum, hence
    `≥ A.min'` (`min'_le_subsetSums`); rearranging gives `s ≤ ∑ A − A.min'`.
    So no proper subset sum can exceed `∑ A − A.min'`. -/
theorem subsetSums_proper_le {A : Finset ℕ} (hA : A.Nonempty) {s : ℕ}
    (hs : s ∈ subsetSums A) (hne : s ≠ A.sum id) :
    s ≤ A.sum id - A.min' hA := by
  have hrefl : A.sum id - s ∈ subsetSums A := subsetSums_reflection hs hne
  have hge : A.min' hA ≤ A.sum id - s := min'_le_subsetSums hA _ hrefl
  have hle : s ≤ A.sum id := subsetSums_le_sum s hs
  omega

/-- The proper subset sums `(subsetSums A).erase (∑ A)` are non-empty once
    `|A| ≥ 2`: the co-total `∑ A − A.min'` is a proper subset sum. -/
theorem proper_subsetSums_nonempty {A : Finset ℕ} (hA : A.Nonempty)
    (hlo : ∀ a ∈ A, 1 ≤ a) (hcard : 1 < A.card) :
    ((subsetSums A).erase (A.sum id)).Nonempty := by
  refine ⟨A.sum id - A.min' hA, ?_⟩
  rw [Finset.mem_erase]
  have hmin : 1 ≤ A.min' hA := hlo _ (A.min'_mem hA)
  have hsum : A.min' hA ≤ A.sum id :=
    subsetSums_le_sum _ (subset_subsetSums A (A.min'_mem hA))
  exact ⟨by omega, sum_sub_min'_mem_subsetSums hA hcard⟩

/-- **The largest proper subset sum is exactly `∑ A − A.min'`.**  Among the
    subset sums strictly below the total, the maximum is the total minus the
    smallest element.  It is attained (`sum_sub_min'_mem_subsetSums`, by dropping
    `A.min'`) and it dominates every proper subset sum (`subsetSums_proper_le`,
    via reflection).  This is the reflection-dual of `min'_subsetSums_eq_min'`
    (the smallest subset sum is `A.min'`) and refines `max'_subsetSums_eq_sum`
    (the overall maximum is `∑ A`) by identifying the second-largest value. -/
theorem max'_proper_subsetSums_eq {A : Finset ℕ} (hA : A.Nonempty)
    (hlo : ∀ a ∈ A, 1 ≤ a) (hcard : 1 < A.card) :
    ((subsetSums A).erase (A.sum id)).max' (proper_subsetSums_nonempty hA hlo hcard)
      = A.sum id - A.min' hA := by
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    rw [Finset.mem_erase] at hy
    exact subsetSums_proper_le hA hy.2 hy.1
  · apply Finset.le_max'
    rw [Finset.mem_erase]
    have hmin : 1 ≤ A.min' hA := hlo _ (A.min'_mem hA)
    have hsum : A.min' hA ≤ A.sum id :=
      subsetSums_le_sum _ (subset_subsetSums A (A.min'_mem hA))
    exact ⟨by omega, sum_sub_min'_mem_subsetSums hA hcard⟩

/-- **`DivisibilityFree` is exactly a divisibility antichain.**
    Bridges the file's ad-hoc predicate to Mathlib's `IsAntichain (· ∣ ·)`,
    unlocking the general antichain API for reuse.  The two definitions coincide
    because `IsAntichain` already quantifies over *both* orders of every pair, so
    a single `¬(a ∣ b)` for all `a ≠ b` is equivalent to the symmetric
    `¬(a ∣ b) ∧ ¬(b ∣ a)`. -/
theorem divisibilityFree_iff_isAntichain (S : Finset ℕ) :
    DivisibilityFree S ↔ IsAntichain (· ∣ ·) (↑S : Set ℕ) := by
  constructor
  · intro h a ha b hb hab
    exact (h a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab).1
  · intro h a ha b hb hab
    exact ⟨h (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab,
           h (Finset.mem_coe.mpr hb) (Finset.mem_coe.mpr ha) (Ne.symm hab)⟩

/-- Forward direction packaged for direct use: a divisibility-free set *is* a
    Mathlib divisibility antichain. -/
theorem DivisibilityFree.isAntichain {S : Finset ℕ} (h : DivisibilityFree S) :
    IsAntichain (· ∣ ·) (↑S : Set ℕ) :=
  (divisibilityFree_iff_isAntichain S).mp h

/-!
### Divisibility necessary conditions for `ValidSubset`

With the `IsAntichain` bridge (`divisibilityFree_iff_isAntichain`) in place, the
Erdős #882 validity hypothesis yields concrete *necessary* conditions: the subset
sums of a valid `A` form a divisibility antichain, no proper partial subset sum
divides the total, and no single element of a size-`≥ 2` valid set divides `∑ A`.
-/

/-- **The subset sums of a valid set form a divisibility antichain.**  This is
    the Erdős #882 hypothesis restated in Mathlib's `IsAntichain` language, ready
    to feed antichain machinery. -/
theorem validSubset_subsetSums_isAntichain {n : ℕ} {A : Finset ℕ}
    (h : ValidSubset n A) : IsAntichain (· ∣ ·) (↑(subsetSums A) : Set ℕ) :=
  h.2.isAntichain

/-- **No proper partial sum divides the total.**  In a valid set `A`, for every
    non-empty proper subset `S ⊊ A` the partial sum `∑ S` does *not* divide the
    total `∑ A`.  Both are subset sums, and `∑ S < ∑ A` (a proper subset of a
    positive set has strictly smaller sum), so they are distinct values and the
    divisibility-free condition forbids `∑ S ∣ ∑ A`.  A concrete necessary
    condition every #882-valid configuration must meet. -/
theorem validSubset_subsetSum_not_dvd_total {n : ℕ} {A S : Finset ℕ}
    (hV : ValidSubset n A) (hSA : S ⊆ A) (hS : S.Nonempty) (hne : S ≠ A) :
    ¬ (S.sum id ∣ A.sum id) := by
  obtain ⟨hbound, hdf⟩ := hV
  have hpos : ∀ a ∈ A, 1 ≤ a := fun a ha => (hbound a ha).1
  have hssub : S ⊂ A := hSA.ssubset_of_ne hne
  obtain ⟨x, hxA, hxS⟩ := Finset.exists_of_ssubset hssub
  have hlt : S.sum id < A.sum id :=
    Finset.sum_lt_sum_of_subset hSA hxA hxS (by simp only [id_eq]; exact hpos x hxA)
      (by intro j _ _; exact Nat.zero_le _)
  have hmemS : S.sum id ∈ subsetSums A := sum_mem_subsetSums_of_subset hSA hS
  have hmemA : A.sum id ∈ subsetSums A := sum_mem_subsetSums ⟨x, hxA⟩
  exact (hdf (S.sum id) hmemS (A.sum id) hmemA (Nat.ne_of_lt hlt)).1

/-- **No element of a size-`≥ 2` valid set divides the total.**  Specialising
    `validSubset_subsetSum_not_dvd_total` to a singleton: in a valid `A` with
    `|A| ≥ 2`, no member `a ∈ A` divides `∑ A`.  (When `|A| = 1` the sole element
    *is* the total, so the size hypothesis is needed.) -/
theorem validSubset_elem_not_dvd_total {n : ℕ} {A : Finset ℕ} {a : ℕ}
    (hV : ValidSubset n A) (ha : a ∈ A) (hcard : 2 ≤ A.card) :
    ¬ (a ∣ A.sum id) := by
  have hne : ({a} : Finset ℕ) ≠ A := by
    intro h
    have : A.card = 1 := by rw [← h]; simp
    omega
  have h := validSubset_subsetSum_not_dvd_total hV
    (Finset.singleton_subset_iff.mpr ha) (Finset.singleton_nonempty a) hne
  simpa using h

/-- **Validity forces divisibility-freeness of the generators themselves.**  Every
    element of `A` is one of its own singleton subset sums (`subset_subsetSums`), so
    the divisibility-free condition on `subsetSums A` restricts to `A`: a valid set is
    in particular a *primitive* (divisibility-free) set.  This is a necessary
    condition that the full subset-sum constraint of Erdős #882 strictly strengthens
    — it is far from sufficient, as `extremal_distinct_not_valid` shows. -/
theorem ValidSubset.divisibilityFree_base {n : ℕ} {A : Finset ℕ}
    (h : ValidSubset n A) : DivisibilityFree A :=
  h.2.mono (subset_subsetSums A)

/-- **Distinct subset sums do NOT imply validity: the counting extremum is strictly
    weaker than Erdős #882 validity.**  The superincreasing set `{1,2}` attains the
    full `2² − 1 = 3` distinct subset sums — it meets the counting ceiling
    `subsetSums_card_le` with equality — yet it is *not* a valid subset for any `n`:
    its subset sums are `{1,2,3}` and `1 ∣ 2`.  So realising the maximum possible
    number of distinct subset sums (the superincreasing / powers-of-two regime) does
    not certify divisibility-freeness of those sums.  This is exactly why the true
    Erdős #882 answer `(1+o(1)) log₂ n` sits far below the naive counting ceiling of
    `2^{|A|} − 1` distinct sums: the validity constraint bites long before the
    counting one does. -/
theorem extremal_distinct_not_valid :
    ∃ A : Finset ℕ, Superincreasing A ∧
      (subsetSums A).card = 2 ^ A.card - 1 ∧ (∀ n, ¬ ValidSubset n A) := by
  have hSI : Superincreasing ({1, 2} : Finset ℕ) := by
    intro a ha; fin_cases ha <;> decide
  refine ⟨{1, 2}, hSI, subsetSums_card_superincreasing hSI, ?_⟩
  intro _ hvalid
  have h1 : (1 : ℕ) ∈ subsetSums ({1, 2} : Finset ℕ) :=
    subset_subsetSums _ (by decide)
  have h2 : (2 : ℕ) ∈ subsetSums ({1, 2} : Finset ℕ) :=
    subset_subsetSums _ (by decide)
  exact (hvalid.2 1 h1 2 h2 (by decide)).1 (by decide)

/-!
### Nested-subset non-divisibility and the per-step growth constraint

The Erdős #882 upper bound `(1+o(1)) log₂ n` is driven by a *growth* phenomenon:
if we enumerate `A = {a₁ < a₂ < ⋯ < a_k}` and form the prefix sums
`σ_i = a₁ + ⋯ + a_i`, then `σ_1 < σ_2 < ⋯ < σ_k = ∑ A` is a strictly increasing
chain of subset sums, and divisibility-freeness forbids `σ_i ∣ σ_j` for `i < j`.
Because `σ_{i+1} = σ_i + a_{i+1}`, the relation `σ_i ∣ σ_{i+1}` is equivalent to
`σ_i ∣ a_{i+1}`; so validity forces `σ_i ∤ a_{i+1}` — a partial sum never divides
the *next* element added.  Below we prove the mechanism at the level of arbitrary
nested subsets, which subsumes the sorted-prefix picture without needing a sort.
-/

/-- **Nested subset sums of a valid set never divide.**  Generalises
    `validSubset_subsetSum_not_dvd_total` (the `T = A` case): for *any* nested pair
    of non-empty subsets `S ⊊ T ⊆ A` of a valid set, the smaller partial sum `∑ S`
    does not divide the larger `∑ T`.  Both are subset sums of `A`, and `∑ S < ∑ T`
    because passing to a strict superset of a positive set strictly increases the
    sum, so they are distinct values and the divisibility-free condition on
    `subsetSums A` forbids `∑ S ∣ ∑ T`.  This is the "antichain along a chain"
    fact: every strictly increasing chain of subset sums is a divisibility
    antichain. -/
theorem validSubset_nested_sum_not_dvd {n : ℕ} {A S T : Finset ℕ}
    (hV : ValidSubset n A) (hST : S ⊂ T) (hTA : T ⊆ A) (hS : S.Nonempty) :
    ¬ (S.sum id ∣ T.sum id) := by
  obtain ⟨hbound, hdf⟩ := hV
  have hpos : ∀ a ∈ A, 1 ≤ a := fun a ha => (hbound a ha).1
  have hSA : S ⊆ A := (subset_of_ssubset hST).trans hTA
  obtain ⟨x, hxT, hxS⟩ := Finset.exists_of_ssubset hST
  have hlt : S.sum id < T.sum id :=
    Finset.sum_lt_sum_of_subset (subset_of_ssubset hST) hxT hxS
      (by simp only [id_eq]; exact hpos x (hTA hxT))
      (by intro j _ _; exact Nat.zero_le _)
  have hT : T.Nonempty := hS.mono (subset_of_ssubset hST)
  have hmemS : S.sum id ∈ subsetSums A := sum_mem_subsetSums_of_subset hSA hS
  have hmemT : T.sum id ∈ subsetSums A := sum_mem_subsetSums_of_subset hTA hT
  exact (hdf (S.sum id) hmemS (T.sum id) hmemT (Nat.ne_of_lt hlt)).1

/-- **A partial sum never divides an excluded element.**  In a valid set `A`, if
    `S ⊆ A` is a non-empty partial support and `a ∈ A` lies outside `S`, then
    `∑ S ∤ a`.  Taking `T = insert a S` in `validSubset_nested_sum_not_dvd` gives
    `∑ S ∤ ∑ (insert a S) = a + ∑ S`, which is equivalent to `∑ S ∤ a`.  This is
    the per-step growth constraint `σ_i ∤ a_{i+1}` behind the `(1+o(1)) log₂ n`
    upper bound, stated for arbitrary supports rather than a sorted prefix. -/
theorem validSubset_partialSum_not_dvd_elem {n : ℕ} {A S : Finset ℕ} {a : ℕ}
    (hV : ValidSubset n A) (hS : S.Nonempty) (hSA : S ⊆ A)
    (ha : a ∈ A) (haS : a ∉ S) :
    ¬ (S.sum id ∣ a) := by
  have hins : insert a S ⊆ A := Finset.insert_subset_iff.mpr ⟨ha, hSA⟩
  have hss : S ⊂ insert a S := Finset.ssubset_insert haS
  have hnd := validSubset_nested_sum_not_dvd hV hss hins hS
  have hsum : (insert a S).sum id = a + S.sum id := by
    rw [Finset.sum_insert haS, id_eq]
  rw [hsum] at hnd
  intro hdvd
  exact hnd (dvd_add hdvd (dvd_refl _))

end Erdos882OQ03
