/-
# The Sperner door lemma: ≤ 2 doors per simplex (discharging `hsimplex`)

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam from
abstract door-counting").

## Where this sits

The abstract door-counting engine (`SpernerTuckerDoorGraph.lean`) derives the
path-following structure of Tucker's lemma from a finite *door-incidence relation*
`inc : V → D → Prop` satisfying three geometric hypotheses:

* `hdoor`    — each door is shared by `≤ 2` simplices (a pseudomanifold property);
* `hsimplex` — each almost-complementary simplex has `≤ 2` doors;
* `hpair`    — two distinct simplices share `≤ 1` door.

Every prior session carried these as *black-box hypotheses*.  This file **discharges
`hsimplex`** for the canonical Sperner colouring — turning the `≤ 2`-doors-per-simplex
bound from an assumption into a proved combinatorial theorem.

## What this file proves

Model an `n`-dimensional simplex as a colouring `c : Fin (n+1) → Fin (n+1)` of its
`n + 1` vertices by `n + 1` colours.  The distinguished colour is the *top* colour
`Fin.last n`; the remaining `n` are the *low* colours.  A facet — obtained by dropping
one vertex `i` — is a **door** when its `n` vertices realise every low colour
(`IsDoor c i`).

* `door_image`  — a door facet's colour image is **exactly** the low colours: dropping
  `i` gives an honest bijection of the remaining `n` vertices onto the `n` low colours.
  Hence (`door_no_top`, `door_injOn`) no other vertex carries the top colour and the
  colouring is injective off `i`.
* `card_doors_le_two`  — **the door lemma**: every simplex has at most two doors.  The
  doors all carry one common colour (`doors_same_color`), and that colour is realised by
  at most two vertices (`card_color_le_two`).  This is precisely the `hsimplex` bound
  `#{d | inc v d} ≤ 2`, now a theorem.
* `card_doors_eq_one_of_bijective`  — a **panchromatic** simplex (`c` bijective) has
  *exactly one* door: the facet opposite the unique vertex of the top colour.  These are
  the simplices the path-following engine sees as endpoints / interior cells.

The companion bounds `hdoor` (pseudomanifold facet-sharing) and `hpair` (two simplices
share ≤ 1 facet) concern the global complex and remain the open frontier; this file
closes the single-simplex bound, which is the purely local, dimension-free piece.

## Honest status

This is a genuine, dimension-free combinatorial theorem (the classical Sperner "door"
counting fact), proved from scratch — Mathlib has the Sperner/`exists_panchromatic`
machinery but not this per-simplex door count in reusable form.  It converts one of the
three abstract door hypotheses into a proof, narrowing the open obligation.  It is *not*
the full geometric `bridge`, which remains open exactly as prior sessions flagged.

Self-contained.  0 sorries, 0 axioms (propext / Classical.choice / Quot.sound only).
-/
import Mathlib.Tactic

namespace SpernerTuckerDoorLemma

open Finset

variable {n : ℕ}

/-- The facet obtained by dropping vertex `i` is a **door** when its `n` remaining
vertices realise every *low* colour (every colour other than the top colour
`Fin.last n`).  Geometrically: the complementary facet carries a full set of labels. -/
def IsDoor (c : Fin (n + 1) → Fin (n + 1)) (i : Fin (n + 1)) : Prop :=
  ∀ k : Fin (n + 1), k ≠ Fin.last n → ∃ j, j ≠ i ∧ c j = k

instance (c : Fin (n + 1) → Fin (n + 1)) (i : Fin (n + 1)) : Decidable (IsDoor c i) := by
  unfold IsDoor; infer_instance

/-! ## A door facet is a bijection onto the low colours -/

/-- **A door facet's colour image is exactly the low colours.**  Dropping vertex `i`
from a door leaves `n` vertices whose colours are precisely the `n` low colours — an
honest bijection.  (Surjectivity is the door condition; equality of the two `n`-element
finsets upgrades it.) -/
theorem door_image {c : Fin (n + 1) → Fin (n + 1)} {i : Fin (n + 1)} (h : IsDoor c i) :
    (univ.erase i).image c = univ.erase (Fin.last n) := by
  have hcard_low : (univ.erase (Fin.last n) : Finset (Fin (n + 1))).card = n := by
    rw [Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, Fintype.card_fin]; omega
  have hcard_facet : (univ.erase i : Finset (Fin (n + 1))).card = n := by
    rw [Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, Fintype.card_fin]; omega
  have hsub : univ.erase (Fin.last n) ⊆ (univ.erase i).image c := by
    intro k hk
    rw [mem_erase] at hk
    obtain ⟨j, hji, hcj⟩ := h k hk.1
    exact mem_image.mpr ⟨j, mem_erase.mpr ⟨hji, mem_univ _⟩, hcj⟩
  have hle : ((univ.erase i).image c).card ≤ n :=
    le_trans Finset.card_image_le (le_of_eq hcard_facet)
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [hcard_low]; exact hle

/-- A door facet carries no top-coloured vertex other than the dropped one. -/
theorem door_no_top {c : Fin (n + 1) → Fin (n + 1)} {i j : Fin (n + 1)}
    (h : IsDoor c i) (hj : j ≠ i) : c j ≠ Fin.last n := by
  intro hcj
  have hmem : c j ∈ (univ.erase i).image c :=
    mem_image.mpr ⟨j, mem_erase.mpr ⟨hj, mem_univ _⟩, rfl⟩
  rw [door_image h, hcj] at hmem
  exact (mem_erase.mp hmem).1 rfl

/-- A door facet's colouring is injective off the dropped vertex. -/
theorem door_injOn {c : Fin (n + 1) → Fin (n + 1)} {i : Fin (n + 1)} (h : IsDoor c i) :
    Set.InjOn c (univ.erase i) := by
  apply Finset.injOn_of_card_image_eq
  rw [door_image h, Finset.card_erase_of_mem (mem_univ _),
    Finset.card_erase_of_mem (mem_univ _)]

/-! ## The door lemma: ≤ 2 doors per simplex -/

/-- The colour of a door's dropped vertex is realised by at most two vertices: in the
bijection off `i`, that colour appears at most once more. -/
theorem card_color_le_two {c : Fin (n + 1) → Fin (n + 1)} {i : Fin (n + 1)}
    (h : IsDoor c i) : (univ.filter (fun j => c j = c i)).card ≤ 2 := by
  by_cases htop : c i = Fin.last n
  · -- top-coloured dropped vertex: no other vertex shares its colour
    have hsub : univ.filter (fun j => c j = c i) ⊆ {i} := by
      intro j hj
      rw [mem_filter] at hj
      rw [mem_singleton]
      by_contra hji
      exact door_no_top h hji (by rw [hj.2, htop])
    calc (univ.filter (fun j => c j = c i)).card ≤ ({i} : Finset (Fin (n + 1))).card :=
          card_le_card hsub
      _ = 1 := card_singleton i
      _ ≤ 2 := by norm_num
  · -- low-coloured dropped vertex: exactly one other vertex shares its colour
    have hmem : c i ∈ univ.erase (Fin.last n) := mem_erase.mpr ⟨htop, mem_univ _⟩
    rw [← door_image h, mem_image] at hmem
    obtain ⟨j₀, hj₀, hcj₀⟩ := hmem
    have hsub : univ.filter (fun j => c j = c i) ⊆ {i, j₀} := by
      intro j hj
      rw [mem_filter] at hj
      simp only [mem_insert, mem_singleton]
      by_cases hji : j = i
      · exact Or.inl hji
      · refine Or.inr ?_
        have hjerase : j ∈ univ.erase i := mem_erase.mpr ⟨hji, mem_univ _⟩
        exact door_injOn h (Finset.mem_coe.mpr hjerase) (Finset.mem_coe.mpr hj₀)
          (by rw [hj.2, hcj₀])
    have hpair_card : ({i, j₀} : Finset (Fin (n + 1))).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by norm_num [Finset.card_singleton])
    exact (card_le_card hsub).trans hpair_card

/-- **All doors of a simplex carry the same colour.**  If `i ≠ i'` are both doors, then
`c i = c i'`: each door's dropped vertex is low-coloured (by the other door), and the
bijection structure forces the two to coincide. -/
theorem doors_same_color {c : Fin (n + 1) → Fin (n + 1)} {i i' : Fin (n + 1)}
    (hi : IsDoor c i) (hi' : IsDoor c i') (hne : i ≠ i') : c i = c i' := by
  by_contra hcc
  have hilow : c i ≠ Fin.last n := door_no_top hi' hne
  have hi_mem : c i ∈ (univ.erase i).image c := by
    rw [door_image hi]; exact mem_erase.mpr ⟨hilow, mem_univ _⟩
  rw [mem_image] at hi_mem
  obtain ⟨q, hq, hcq⟩ := hi_mem
  have hqi : q ≠ i := (mem_erase.mp hq).1
  have hqi' : q ≠ i' := by
    intro he; rw [he] at hcq; exact hcc hcq.symm
  have hq_e' : q ∈ univ.erase i' := mem_erase.mpr ⟨hqi', mem_univ _⟩
  have hi_e' : i ∈ univ.erase i' := mem_erase.mpr ⟨hne, mem_univ _⟩
  exact hqi (door_injOn hi' (Finset.mem_coe.mpr hq_e') (Finset.mem_coe.mpr hi_e') hcq)

/-- **The Sperner door lemma.**  Every coloured simplex has **at most two** doors.

This is exactly the `hsimplex` hypothesis `#{d | inc v d} ≤ 2` of the abstract
door-counting engine (`SpernerTuckerDoorGraph`), now proved rather than assumed: the
doors all carry one common colour (`doors_same_color`), and any colour is realised by at
most two vertices of a door simplex (`card_color_le_two`). -/
theorem card_doors_le_two (c : Fin (n + 1) → Fin (n + 1)) :
    (univ.filter (IsDoor c)).card ≤ 2 := by
  rcases (univ.filter (IsDoor c)).eq_empty_or_nonempty with hempty | ⟨i₀, hi₀⟩
  · rw [hempty]; simp
  · have hdoor₀ : IsDoor c i₀ := (mem_filter.mp hi₀).2
    have hsub : univ.filter (IsDoor c) ⊆ univ.filter (fun j => c j = c i₀) := by
      intro j hj
      have hdoorj : IsDoor c j := (mem_filter.mp hj).2
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      by_cases hji : j = i₀
      · rw [hji]
      · exact doors_same_color hdoorj hdoor₀ hji
    exact (card_le_card hsub).trans (card_color_le_two hdoor₀)

/-! ## Panchromatic simplices have exactly one door -/

/-- For a **panchromatic** simplex (`c` bijective: every colour occurs exactly once), a
facet is a door iff it drops the unique vertex carrying the top colour. -/
theorem isDoor_iff_eq_top_vertex {c : Fin (n + 1) → Fin (n + 1)}
    (hc : Function.Bijective c) {i : Fin (n + 1)} :
    IsDoor c i ↔ c i = Fin.last n := by
  constructor
  · intro h
    obtain ⟨iL, hiL⟩ := hc.surjective (Fin.last n)
    by_contra hci
    have hiLi : iL ≠ i := fun he => hci (he ▸ hiL)
    exact door_no_top h hiLi hiL
  · intro hci k hk
    obtain ⟨j, hj⟩ := hc.surjective k
    refine ⟨j, ?_, hj⟩
    intro hji
    rw [hji, hci] at hj
    exact hk hj.symm

/-- **A panchromatic simplex has exactly one door** — the facet opposite the unique
top-coloured vertex.  These are the cells the path-following engine treats as endpoints:
of their facets, exactly one is complementary. -/
theorem card_doors_eq_one_of_bijective {c : Fin (n + 1) → Fin (n + 1)}
    (hc : Function.Bijective c) : (univ.filter (IsDoor c)).card = 1 := by
  obtain ⟨iL, hiL⟩ := hc.surjective (Fin.last n)
  have hset : univ.filter (IsDoor c) = {iL} := by
    ext j
    rw [mem_filter, mem_singleton, isDoor_iff_eq_top_vertex hc]
    constructor
    · rintro ⟨_, hj⟩
      exact hc.injective (hj.trans hiL.symm)
    · rintro rfl
      exact ⟨mem_univ _, hiL⟩
  rw [hset, card_singleton]

/-- The door lemma in the exact shape of the abstract engine's `hsimplex` hypothesis:
for any per-vertex door predicate coming from a colouring, the door count is `≤ 2`. -/
example (c : Fin (n + 1) → Fin (n + 1)) :
    (univ.filter (IsDoor c)).card ≤ 2 := card_doors_le_two c

#check @card_doors_le_two
#check @card_doors_eq_one_of_bijective
#check @doors_same_color

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`.
#print axioms card_doors_le_two
#print axioms card_doors_eq_one_of_bijective

end SpernerTuckerDoorLemma
