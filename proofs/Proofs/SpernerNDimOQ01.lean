/-
# Freudenthal Adjacency Theorem

The **Freudenthal triangulation** divides the unit n-cube into n! simplices,
one for each permutation of {0,...,n-1}. Each simplex has n+1 vertices:
for permutation l (represented as a list), the k-th vertex is `(l.take k).toFinset`.

## Main Result

**Freudenthal Adjacency Theorem**: Each interior (n-1)-facet belongs to exactly 2 simplices.

Interior facet at position k (for 0 < k < n): the set of all vertices except the k-th.

## Proof

The key combinatorial fact: the set of k-element subsets S satisfying
  `(l.take (k-1)).toFinset ⊆ S ⊆ (l.take (k+1)).toFinset`
has exactly 2 elements. This follows because B \ A has exactly 2 elements
(l[k-1] and l[k]), and S = A ∪ {one element from B \ A}.

## Sorries

0 sorries (fully proved).

## Tags

Freudenthal, triangulation, simplex, adjacency, Sperner, combinatorics
-/

import Mathlib

namespace FreudenthalAdjacency

open Finset List

variable {n : ℕ}

-- ============================================================
-- SECTION I: Prefix set definitions and basic properties
-- ============================================================

/-- The first k elements of list l as a Finset. -/
def prefixSet (l : List (Fin n)) (k : ℕ) : Finset (Fin n) :=
  (l.take k).toFinset

/-- For a nodup list, the prefix set has cardinality min k l.length. -/
theorem prefixSet_card {l : List (Fin n)} (hl : l.Nodup) (k : ℕ) :
    (prefixSet l k).card = min k l.length := by
  simp only [prefixSet, List.toFinset_card_of_nodup (hl.take k), List.length_take]

theorem prefixSet_card_eq {l : List (Fin n)} (hl : l.Nodup) {k : ℕ} (hk : k ≤ l.length) :
    (prefixSet l k).card = k := by
  rw [prefixSet_card hl, Nat.min_eq_left hk]

/-- Prefix sets form a chain under inclusion. -/
theorem prefixSet_mono {l : List (Fin n)} (k : ℕ) :
    prefixSet l k ⊆ prefixSet l (k + 1) := by
  intro x; simp only [prefixSet, List.mem_toFinset]
  exact fun h => List.take_subset _ (Nat.le_succ k) h

/-- The difference between prefixSet l (k+1) and prefixSet l k is the singleton {l[k]}. -/
theorem prefixSet_succ_sdiff {l : List (Fin n)} (hl : l.Nodup) {k : ℕ} (hk : k < l.length) :
    prefixSet l (k + 1) \ prefixSet l k = {l.get ⟨k, hk⟩} := by
  ext x
  simp only [prefixSet, mem_sdiff, List.mem_toFinset, mem_singleton]
  constructor
  · intro ⟨hmem1, hmem2⟩
    -- x ∈ l.take(k+1) but x ∉ l.take k
    -- By List.take_succ, l.take(k+1) = l.take k ++ [l.get k]
    rw [List.take_succ, List.get?_eq_get hk] at hmem1
    simp only [Option.toList, List.append_cons, List.append_nil, List.mem_append,
      List.mem_singleton] at hmem1
    rcases hmem1 with h | h
    · exact absurd h hmem2
    · exact h
  · intro h
    subst h
    constructor
    · rw [List.take_succ, List.get?_eq_get hk]
      simp [List.mem_append, Option.toList]
    · intro hmem
      -- l.get k ∈ l.take k contradicts nodup
      have := List.Nodup.get_inj_iff hl ⟨k, hk⟩
      rw [List.mem_iff_get] at hmem
      obtain ⟨j, hj⟩ := hmem
      have hjlt : j.val < k := by rwa [List.length_take, Nat.min_eq_left hk.le] at j.isLt
      have := (List.Nodup.get_inj_iff hl).mp (hj.symm)
      exact Nat.not_lt.mpr (Fin.val_le_of_eq this) hjlt

/-- The difference between prefixSet l (k+1) and prefixSet l (k-1) has 2 elements. -/
theorem prefixSet_skip_sdiff_card {l : List (Fin n)} (hl : l.Nodup)
    (k : ℕ) (hk0 : 0 < k) (hk1 : k < l.length) :
    (prefixSet l (k + 1) \ prefixSet l (k - 1)).card = 2 := by
  have hAB : prefixSet l (k - 1) ⊆ prefixSet l (k + 1) :=
    (prefixSet_mono (k - 1)).trans (prefixSet_mono k)
  have hA_card : (prefixSet l (k - 1)).card = k - 1 :=
    prefixSet_card_eq hl (by omega)
  have hB_card : (prefixSet l (k + 1)).card = k + 1 :=
    prefixSet_card_eq hl (by omega)
  rw [Finset.card_sdiff hAB, hA_card, hB_card]
  omega

-- ============================================================
-- SECTION II: The counting lemma for intermediate sets
-- ============================================================

/-- The main combinatorial lemma: if B \ A has 2 elements, there are exactly 2
    sets S with A ⊆ S ⊆ B and |S| = |A| + 1. -/
theorem intermediate_sets_card_eq_two {A B : Finset (Fin n)} (hAB : A ⊆ B)
    (hBA : (B \ A).card = 2) :
    (B.powerset.filter (fun S => A ⊆ S ∧ S.card = A.card + 1)).card = 2 := by
  -- Obtain the two elements of B \ A
  obtain ⟨a, b, hab, hBA_eq⟩ := Finset.card_eq_two.mp hBA
  -- The filter is exactly {A ∪ {a}, A ∪ {b}}
  have ha_notA : a ∉ A := Finset.not_mem_of_mem_sdiff (by rw [← hBA_eq]; simp)
  have hb_notA : b ∉ A := Finset.not_mem_of_mem_sdiff (by rw [← hBA_eq, Finset.insert_comm]; simp)
  have ha_B : a ∈ B := Finset.mem_of_mem_sdiff (by rw [← hBA_eq]; simp)
  have hb_B : b ∈ B := Finset.mem_of_mem_sdiff (by rw [← hBA_eq, Finset.insert_comm]; simp)
  have hpair_ne : A ∪ {a} ≠ A ∪ {b} := by
    intro h
    have : a ∈ A ∪ {b} := h ▸ Finset.mem_union_right A (Finset.mem_singleton_self a)
    simp only [Finset.mem_union, Finset.mem_singleton] at this
    rcases this with h | h
    · exact ha_notA h
    · exact hab h
  convert_to ({A ∪ {a}, A ∪ {b}} : Finset (Finset (Fin n))).card = 2
  · apply Finset.card_pair hpair_ne
  · congr 1
    ext S
    simp only [mem_filter, mem_powerset, mem_insert, mem_singleton]
    constructor
    · intro ⟨hSB, hAS, hScard⟩
      -- S \ A is a 1-element subset of B \ A = {a, b}
      have hSdiff_card : (S \ A).card = 1 := by
        rw [Finset.card_sdiff hAS, hScard]; omega
      obtain ⟨e, he⟩ := Finset.card_eq_one.mp hSdiff_card
      have he_BA : e ∈ B \ A := by
        have he_S : e ∈ S \ A := he ▸ Finset.mem_singleton_self e
        exact Finset.mem_sdiff.mpr ⟨hSB (Finset.mem_of_mem_sdiff he_S),
          Finset.not_mem_of_mem_sdiff he_S⟩
      rw [← hBA_eq] at he_BA
      simp only [mem_insert, mem_singleton] at he_BA
      have hS_eq : S = A ∪ {e} := by
        ext x
        simp only [mem_union, mem_singleton]
        constructor
        · intro hx
          by_cases hxA : x ∈ A
          · exact Or.inl hxA
          · have : x ∈ S \ A := Finset.mem_sdiff.mpr ⟨hx, hxA⟩
            rw [he, mem_singleton] at this
            exact Or.inr this
        · rintro (hx | rfl)
          · exact hAS hx
          · exact Finset.mem_of_mem_sdiff (he ▸ Finset.mem_singleton_self e)
      rcases he_BA with rfl | rfl
      · left; exact hS_eq
      · right; exact hS_eq
    · rintro (rfl | rfl) <;> refine ⟨?_, Finset.subset_union_left, ?_⟩
      · intro x; simp only [mem_union, mem_singleton]; rintro (hx | rfl); exact hAB hx; exact ha_B
      · rw [Finset.card_union_of_disjoint (by simp [ha_notA])]; simp
      · intro x; simp only [mem_union, mem_singleton]; rintro (hx | rfl); exact hAB hx; exact hb_B
      · rw [Finset.card_union_of_disjoint (by simp [hb_notA])]; simp

-- ============================================================
-- SECTION III: Freudenthal Adjacency Theorem
-- ============================================================

/-- **Freudenthal Adjacency Theorem**:
    Each interior (n-1)-facet of the Freudenthal triangulation belongs to exactly 2 simplices.

    We represent a Freudenthal simplex as a nodup list `l` of all elements of `Fin n`.
    The k-th vertex of simplex l is `(l.take k).toFinset`.
    The k-th interior facet (for 0 < k < n) is the sequence of all vertices except the k-th.

    The theorem: the number of k-element subsets S satisfying
      `(l.take (k-1)).toFinset ⊆ S ⊆ (l.take (k+1)).toFinset`
    is exactly 2. These correspond to the 2 simplices sharing the facet.

    The two simplices are l and the permutation obtained by swapping l[k-1] and l[k]. -/
theorem freudenthal_adjacency_theorem
    (l : List (Fin n)) (hl : l.Nodup) (hl_len : l.length = n)
    (k : ℕ) (hk0 : 0 < k) (hk1 : k < n) :
    ((prefixSet l (k + 1)).powerset.filter
      (fun S => prefixSet l (k - 1) ⊆ S ∧ S.card = k)).card = 2 := by
  -- The filter matches our intermediate_sets_card_eq_two lemma
  -- with A = prefixSet l (k-1), B = prefixSet l (k+1), and |A| = k-1
  have hA_card : (prefixSet l (k - 1)).card = k - 1 :=
    prefixSet_card_eq hl (by omega)
  have hAB : prefixSet l (k - 1) ⊆ prefixSet l (k + 1) :=
    (prefixSet_mono (k - 1)).trans (prefixSet_mono k)
  -- Convert S.card = k to S.card = (prefixSet l (k-1)).card + 1
  have hcard_eq : k = (prefixSet l (k - 1)).card + 1 := by omega
  rw [show k = (prefixSet l (k - 1)).card + 1 from hcard_eq]
  apply intermediate_sets_card_eq_two hAB
  -- |B \ A| = 2
  exact prefixSet_skip_sdiff_card hl k hk0 (by omega)

/-- Corollary: For each interior (n-1)-facet, there exist exactly 2 distinct
    k-element Finsets sandwiched between the (k-1) and (k+1) prefix sets.
    These represent the vertex sets (at level k) of the 2 simplices sharing the facet. -/
theorem freudenthal_two_intermediate_sets
    (l : List (Fin n)) (hl : l.Nodup) (hl_len : l.length = n)
    (k : ℕ) (hk0 : 0 < k) (hk1 : k < n) :
    ∃ S₁ S₂ : Finset (Fin n), S₁ ≠ S₂ ∧
    prefixSet l (k - 1) ⊆ S₁ ∧ S₁ ⊆ prefixSet l (k + 1) ∧ S₁.card = k ∧
    prefixSet l (k - 1) ⊆ S₂ ∧ S₂ ⊆ prefixSet l (k + 1) ∧ S₂.card = k := by
  have hcount := freudenthal_adjacency_theorem l hl hl_len k hk0 hk1
  rw [Finset.card_eq_two] at hcount
  obtain ⟨S₁, S₂, hne, heq⟩ := hcount
  have hmem1 : S₁ ∈ (prefixSet l (k + 1)).powerset.filter
      (fun S => prefixSet l (k - 1) ⊆ S ∧ S.card = k) := by
    rw [heq]; exact Finset.mem_insert_self S₁ {S₂}
  have hmem2 : S₂ ∈ (prefixSet l (k + 1)).powerset.filter
      (fun S => prefixSet l (k - 1) ⊆ S ∧ S.card = k) := by
    rw [heq]; simp
  simp only [Finset.mem_filter, Finset.mem_powerset] at hmem1 hmem2
  exact ⟨S₁, S₂, hne, hmem1.2.1, hmem1.1, hmem1.2.2, hmem2.2.1, hmem2.1, hmem2.2.2⟩

end FreudenthalAdjacency
