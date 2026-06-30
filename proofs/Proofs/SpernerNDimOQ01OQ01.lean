/-
# Freudenthal Door-Counting: Every Facet Bounds One or Two Simplices

This file proves the **door-counting parity fact** underlying the combinatorial proof of
Sperner's lemma for the Freudenthal (Kuhn) triangulation, *unifying* the interior and
boundary cases into a single statement.

## Model

A Freudenthal simplex is a nodup list `l` of all elements of `Fin n` — equivalently a
maximal chain (complete flag) in the Boolean lattice `2^(Fin n)`:
  `∅ = V₀ ⊂ V₁ ⊂ ⋯ ⊂ Vₙ = Fin n`,   `Vₖ = (l.take k).toFinset = prefixSet l k`.
A *facet* of the simplex drops one vertex `Vₖ`. The number of simplices sharing that facet
equals the number of `k`-element sets `S` that can replace `Vₖ`, i.e. with
  `prefixSet l (k-1) ⊆ S ⊆ prefixSet l (k+1)`  and  `|S| = k`.

## Main results

* `intermediate_sets_card_eq_two` — abstract counting core: if `|B \ A| = 2`, there are
  exactly `2` sets `S` with `A ⊆ S ⊆ B` and `|S| = |A| + 1`.
* `freudenthal_adjacency_theorem` — **interior** facet (`0 < k < n`): exactly `2` simplices.
* `freudenthal_boundary_bottom` — facet dropping `V₀ = ∅` (`k = 0`): exactly `1` simplex.
* `freudenthal_boundary_top` — facet dropping `Vₙ = Fin n` (`k = n`): exactly `1` simplex.
* `freudenthal_door_count` — **unified door-counting theorem**: for every `k ≤ n` the facet
  count is `if 0 < k ∧ k < n then 2 else 1`. Interior doors are shared by two simplices; the
  two boundary doors bound exactly one. This is the parity input to Sperner's lemma.
* `freudenthal_boundary_unique_bottom` / `freudenthal_boundary_unique_top` — the
  `ExistsUnique` form of the two boundary facts.

A pleasant feature of the `Fin`/`ℕ` encoding: because truncated subtraction gives
`0 - 1 = 0`, the boundary cases are literally the interior filter formula at `k = 0` and
`k = n`, so `freudenthal_door_count` covers interior and boundary uniformly.

The interior infrastructure (`prefixSet` and the intermediate-set counting lemma) reprises
the construction of `Proofs/SpernerNDimOQ01.lean` but is reproved here from current Mathlib
so the file stands on its own.

## Status

0 sorries, 0 axioms (only `propext`, `Classical.choice`, `Quot.sound`).

## Tags

Freudenthal, triangulation, simplex, door-counting, Sperner, boundary, combinatorics
-/

import Mathlib

namespace FreudenthalDoorCount

open Finset

variable {n : ℕ}

-- ============================================================
-- SECTION I: Prefix-set vertices of a Freudenthal simplex
-- ============================================================

/-- The first `k` elements of list `l`, as a Finset — the `k`-th vertex of the simplex. -/
def prefixSet (l : List (Fin n)) (k : ℕ) : Finset (Fin n) :=
  (l.take k).toFinset

/-- For a nodup list, the prefix set has cardinality `min k l.length`. -/
theorem prefixSet_card {l : List (Fin n)} (hl : l.Nodup) (k : ℕ) :
    (prefixSet l k).card = min k l.length := by
  rw [prefixSet, List.toFinset_card_of_nodup ((List.take_sublist k l).nodup hl),
    List.length_take]

/-- For `k ≤ l.length`, the prefix set has cardinality exactly `k`. -/
theorem prefixSet_card_eq {l : List (Fin n)} (hl : l.Nodup) {k : ℕ} (hk : k ≤ l.length) :
    (prefixSet l k).card = k := by
  rw [prefixSet_card hl, Nat.min_eq_left hk]

/-- Prefix sets form a chain under inclusion. -/
theorem prefixSet_mono {l : List (Fin n)} (k : ℕ) :
    prefixSet l k ⊆ prefixSet l (k + 1) := by
  intro x
  simp only [prefixSet, List.mem_toFinset]
  intro hx
  have hxk : x ∈ (l.take (k + 1)).take k := by
    rwa [List.take_take, Nat.min_eq_left (Nat.le_succ k)]
  exact List.mem_of_mem_take hxk

/-- The gap `prefixSet l (k+1) \ prefixSet l (k-1)` has exactly 2 elements (`0 < k < length`).
    This is the geometric fact that removing an interior vertex creates a 2-element gap. -/
theorem prefixSet_skip_sdiff_card {l : List (Fin n)} (hl : l.Nodup)
    (k : ℕ) (hk0 : 0 < k) (hk1 : k < l.length) :
    (prefixSet l (k + 1) \ prefixSet l (k - 1)).card = 2 := by
  have hAB : prefixSet l (k - 1) ⊆ prefixSet l (k + 1) := by
    refine (prefixSet_mono (k - 1)).trans ?_
    rw [Nat.sub_add_cancel hk0]; exact prefixSet_mono k
  have hA_card : (prefixSet l (k - 1)).card = k - 1 := prefixSet_card_eq hl (by omega)
  have hB_card : (prefixSet l (k + 1)).card = k + 1 := prefixSet_card_eq hl (by omega)
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAB, hA_card, hB_card]
  omega

-- ============================================================
-- SECTION II: The counting lemma for intermediate sets
-- ============================================================

/-- The abstract counting core: if `B \ A` has 2 elements, there are exactly 2 sets `S`
    with `A ⊆ S ⊆ B` and `|S| = |A| + 1`. -/
theorem intermediate_sets_card_eq_two {A B : Finset (Fin n)} (hAB : A ⊆ B)
    (hBA : (B \ A).card = 2) :
    (B.powerset.filter (fun S => A ⊆ S ∧ S.card = A.card + 1)).card = 2 := by
  obtain ⟨a, b, hab, hBA_eq⟩ := Finset.card_eq_two.mp hBA
  have ha_BA : a ∈ B \ A := by rw [hBA_eq]; simp
  have hb_BA : b ∈ B \ A := by rw [hBA_eq]; simp
  have ha_notA : a ∉ A := (Finset.mem_sdiff.mp ha_BA).2
  have hb_notA : b ∉ A := (Finset.mem_sdiff.mp hb_BA).2
  have ha_B : a ∈ B := (Finset.mem_sdiff.mp ha_BA).1
  have hb_B : b ∈ B := (Finset.mem_sdiff.mp hb_BA).1
  have hpair_ne : A ∪ {a} ≠ A ∪ {b} := by
    intro h
    have : a ∈ A ∪ {b} := h ▸ Finset.mem_union_right A (Finset.mem_singleton_self a)
    simp only [Finset.mem_union, Finset.mem_singleton] at this
    rcases this with h | h
    · exact ha_notA h
    · exact hab h
  have hfilter : B.powerset.filter (fun S => A ⊆ S ∧ S.card = A.card + 1)
      = ({A ∪ {a}, A ∪ {b}} : Finset (Finset (Fin n))) := by
    ext S
    simp only [mem_filter, mem_powerset, mem_insert, mem_singleton]
    constructor
    · intro ⟨hSB, hAS, hScard⟩
      have hSdiff_card : (S \ A).card = 1 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAS, hScard]; omega
      obtain ⟨e, he⟩ := Finset.card_eq_one.mp hSdiff_card
      have he_BA : e ∈ B \ A := by
        have he_S : e ∈ S \ A := he ▸ Finset.mem_singleton_self e
        exact Finset.mem_sdiff.mpr ⟨hSB (Finset.mem_sdiff.mp he_S).1,
          (Finset.mem_sdiff.mp he_S).2⟩
      rw [hBA_eq] at he_BA
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
        · rintro (hx | hxe)
          · exact hAS hx
          · rw [hxe]; exact (Finset.mem_sdiff.mp (he ▸ Finset.mem_singleton_self e)).1
      rcases he_BA with rfl | rfl
      · left; exact hS_eq
      · right; exact hS_eq
    · rintro (rfl | rfl) <;> refine ⟨?_, Finset.subset_union_left, ?_⟩
      · intro x; simp only [mem_union, mem_singleton]; rintro (hx | rfl); exact hAB hx; exact ha_B
      · rw [Finset.card_union_of_disjoint (by simp [ha_notA])]; simp
      · intro x; simp only [mem_union, mem_singleton]; rintro (hx | rfl); exact hAB hx; exact hb_B
      · rw [Finset.card_union_of_disjoint (by simp [hb_notA])]; simp
  rw [hfilter, Finset.card_pair hpair_ne]

-- ============================================================
-- SECTION III: Interior facets (parent result, reproved)
-- ============================================================

/-- **Freudenthal Adjacency Theorem** (interior facet, `0 < k < n`):
    each interior `(n-1)`-facet of the Freudenthal triangulation belongs to exactly 2
    simplices. -/
theorem freudenthal_adjacency_theorem
    (l : List (Fin n)) (hl : l.Nodup) (hl_len : l.length = n)
    (k : ℕ) (hk0 : 0 < k) (hk1 : k < n) :
    ((prefixSet l (k + 1)).powerset.filter
      (fun S => prefixSet l (k - 1) ⊆ S ∧ S.card = k)).card = 2 := by
  have hA_card : (prefixSet l (k - 1)).card = k - 1 := prefixSet_card_eq hl (by omega)
  have hAB : prefixSet l (k - 1) ⊆ prefixSet l (k + 1) := by
    refine (prefixSet_mono (k - 1)).trans ?_
    rw [Nat.sub_add_cancel hk0]; exact prefixSet_mono k
  have hgap : (prefixSet l (k + 1) \ prefixSet l (k - 1)).card = 2 :=
    prefixSet_skip_sdiff_card hl k hk0 (by rw [hl_len]; exact hk1)
  -- `intermediate_sets_card_eq_two` gives the count with bound `(prefixSet l (k-1)).card + 1`;
  -- rewrite that exponent back to `k` using `|prefixSet l (k-1)| = k - 1` and `k - 1 + 1 = k`.
  have key := intermediate_sets_card_eq_two hAB hgap
  rw [hA_card, Nat.sub_add_cancel hk0] at key
  exact key

-- ============================================================
-- SECTION IV: Boundary facets bound exactly one simplex
-- ============================================================

/-- **Bottom boundary facet** (`k = 0`): the facet of a Freudenthal simplex that drops the
    apex vertex `V₀ = ∅` bounds exactly one simplex. The only `0`-element set `S` with
    `prefixSet l 0 ⊆ S ⊆ prefixSet l 1` is `S = ∅`, so the door-count is `1`. -/
theorem freudenthal_boundary_bottom (l : List (Fin n)) :
    ((prefixSet l (0 + 1)).powerset.filter
      (fun S => prefixSet l (0 - 1) ⊆ S ∧ S.card = 0)).card = 1 := by
  have hset : (prefixSet l (0 + 1)).powerset.filter
      (fun S => prefixSet l (0 - 1) ⊆ S ∧ S.card = 0) = {∅} := by
    ext S
    simp only [mem_filter, mem_powerset, mem_singleton]
    constructor
    · rintro ⟨_, _, hc⟩
      exact Finset.card_eq_zero.mp hc
    · rintro rfl
      exact ⟨Finset.empty_subset _, by simp [prefixSet], Finset.card_empty⟩
  rw [hset, Finset.card_singleton]

/-- **Top boundary facet** (`k = n`): the facet that drops the maximal vertex `Vₙ = Fin n`
    bounds exactly one simplex. The only `n`-element subset of `Fin n` is `Finset.univ`, so
    the door-count is `1`. -/
theorem freudenthal_boundary_top (l : List (Fin n)) (hl : l.Nodup) (hl_len : l.length = n) :
    ((prefixSet l (n + 1)).powerset.filter
      (fun S => prefixSet l (n - 1) ⊆ S ∧ S.card = n)).card = 1 := by
  have huniv : prefixSet l (n + 1) = (Finset.univ : Finset (Fin n)) := by
    apply Finset.eq_univ_of_card
    rw [prefixSet_card hl, hl_len, Fintype.card_fin]
    omega
  have hset : (prefixSet l (n + 1)).powerset.filter
      (fun S => prefixSet l (n - 1) ⊆ S ∧ S.card = n) = {Finset.univ} := by
    ext S
    simp only [mem_filter, mem_powerset, huniv, Finset.subset_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨_, hc⟩
      exact Finset.eq_univ_of_card S (by rw [hc, Fintype.card_fin])
    · rintro rfl
      exact ⟨Finset.subset_univ _, by rw [Finset.card_univ, Fintype.card_fin]⟩
  rw [hset, Finset.card_singleton]

-- ============================================================
-- SECTION V: The unified door-counting theorem
-- ============================================================

/-- **Freudenthal door-counting theorem** (the parity input to Sperner's lemma).

    For every `k ≤ n`, the `k`-th facet of the Freudenthal simplex `l` is shared by
      * `2` simplices when the facet is **interior** (`0 < k < n`), and
      * `1` simplex when the facet is on the **boundary** (`k = 0` or `k = n`).

    Counting facet–simplex incidences this way, every facet is a door between either two
    rooms (interior) or one room and the outside (boundary): exactly the parity bookkeeping
    that drives the combinatorial Sperner argument. -/
theorem freudenthal_door_count
    (l : List (Fin n)) (hl : l.Nodup) (hl_len : l.length = n)
    (k : ℕ) (hk : k ≤ n) :
    ((prefixSet l (k + 1)).powerset.filter
      (fun S => prefixSet l (k - 1) ⊆ S ∧ S.card = k)).card =
      if 0 < k ∧ k < n then 2 else 1 := by
  by_cases hint : 0 < k ∧ k < n
  · rw [if_pos hint]
    exact freudenthal_adjacency_theorem l hl hl_len k hint.1 hint.2
  · rw [if_neg hint]
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      exact freudenthal_boundary_bottom l
    · have hkn : k = n := by
        rcases lt_or_eq_of_le hk with h | h
        · exact absurd ⟨hkpos, h⟩ hint
        · exact h
      subst hkn
      exact freudenthal_boundary_top l hl hl_len

-- ============================================================
-- SECTION VI: ExistsUnique forms of the boundary facts
-- ============================================================

/-- The bottom boundary facet has a **unique** completing vertex set (namely `∅`). -/
theorem freudenthal_boundary_unique_bottom (l : List (Fin n)) :
    ∃! S : Finset (Fin n), S ⊆ prefixSet l 1 ∧ prefixSet l 0 ⊆ S ∧ S.card = 0 := by
  refine ⟨∅, ⟨Finset.empty_subset _, by simp [prefixSet], Finset.card_empty⟩, ?_⟩
  rintro S ⟨_, _, hc⟩
  exact Finset.card_eq_zero.mp hc

/-- The top boundary facet has a **unique** completing vertex set (namely `Finset.univ`). -/
theorem freudenthal_boundary_unique_top
    (l : List (Fin n)) (hl : l.Nodup) (hl_len : l.length = n) :
    ∃! S : Finset (Fin n),
      prefixSet l (n - 1) ⊆ S ∧ S ⊆ prefixSet l (n + 1) ∧ S.card = n := by
  have huniv : prefixSet l (n + 1) = (Finset.univ : Finset (Fin n)) := by
    apply Finset.eq_univ_of_card
    rw [prefixSet_card hl, hl_len, Fintype.card_fin]
    omega
  refine ⟨Finset.univ, ⟨Finset.subset_univ _, ?_, ?_⟩, ?_⟩
  · rw [huniv]
  · rw [Finset.card_univ, Fintype.card_fin]
  · rintro S ⟨_, _, hc⟩
    exact Finset.eq_univ_of_card S (by rw [hc, Fintype.card_fin])

end FreudenthalDoorCount
