/-
Copyright (c) 2024-2025 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Proofs.FriendshipTheorem

/-
# Friendship Theorem OQ-04: The Infinite Case

## Open Question (friendship-theorem-oq-04)

The finite Friendship Theorem (Erdős–Rényi–Sós 1966) says: if every two distinct
vertices of a *finite* graph have exactly one common neighbour, then some vertex is
adjacent to all others (a "universal friend" / politician). The graph is a windmill.

For **infinite** graphs the theorem is **false**: the C₅ free-amalgamation
construction (Chvátal–Kotzig–Rosenberg–Davies 1976) gives a countable friendship
graph with no universal vertex; every vertex there has infinite degree.

This file formalizes the *positive* boundary result that pins down exactly which
extra hypothesis restores the conclusion, **without using the spectral argument**
that has no infinite analogue:

* `friendship_diameter_two` — every friendship graph (finite **or** infinite) has
  diameter ≤ 2: any vertex `u ≠ v` is either adjacent to `v` or has a common
  neighbour with `v`. This is purely local — no finiteness is used.

* `locally_finite_is_finite` — if a friendship graph is **locally finite** (every
  neighbourhood is finite) then the vertex type is finite. The diameter-2 covering
  exhibits `V` as a finite union of finite sets. So local finiteness is the *sharp*
  restoring condition: the sole obstruction to finiteness is an infinite-degree
  vertex.

* `locally_finite_friendship_has_universal` — combining the above with the finite
  gallery theorem `FriendshipTheorem.friendship_theorem` recovers a universal
  vertex for any locally finite friendship graph with at least three vertices.

* `universal_noncentral_neighborSet` / `universal_noncentral_ncard_two` — the
  **infinite windmill structure**: in *any* friendship graph with a universal vertex
  (finite or infinite), every non-centre vertex has exactly two neighbours — the
  centre and a unique partner — so `N(u) = {centre, partner}`. This is the
  finiteness-free analogue of the finite gallery's
  `FriendshipTheorem.friendship_noncentral_degree` (which states `G.degree u = 2`, a
  `Fintype` notion); it shows the recovered conclusion is genuinely a windmill even
  on infinite vertex types.

* `unique_infinite_degree_vertex` — the **sharp** count of infinite-degree vertices
  in the conclusion-restored case: in an infinite friendship graph with a universal
  vertex `c`, the centre `c` is the *unique* vertex of infinite degree
  (`(G.neighborSet w).Infinite ↔ w = c`). This refines
  `infinite_friendship_has_infinite_degree` from "at least one infinite-degree
  vertex" to "exactly one" once a universal vertex exists — the infinite windmill is
  as infinite as the finite theorem permits, with a single hub and every other vertex
  of degree two.

* `nonadjacent_neighborSet_equinum` — **regularity (finiteness-free).** Any two
  *non-adjacent* vertices `u`, `v` of a friendship graph have *equinumerous*
  neighbourhoods: the map sending each neighbour `w` of `u` to the unique common
  neighbour of `w` and `v` is a bijection `N(u) → N(v)`. This is the infinite analogue
  of the classical "non-adjacent vertices have equal degree" lemma — the step the
  finite proof uses to deduce the graph is regular before invoking the spectral
  argument. It pins down the structure of the **negative** side of OQ-04: a friendship
  graph *without* a universal vertex necessarily contains non-adjacent pairs, so it is
  regular; the C₅ free-amalgamation counterexample is ℵ₀-regular. Stated as a
  `Set.BijOn` so it carries content on infinite neighbourhoods (where `ncard = 0`),
  with no finiteness used.

Where the finite proof breaks: the spectral step
`FriendshipTheorem.friendship_regular_implies_universal` is entirely finite-matrix
algebra (trace, finite eigenvalue multiplicities, integrality) and has no infinite
analogue. The covering argument below bypasses it entirely.
-/

namespace FriendshipTheoremOQ04

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The (Fintype-free) **friendship property**: every pair of distinct vertices
has exactly one common neighbour. Definitionally identical to
`FriendshipTheorem.IsFriendshipGraph`, but stated without a `[Fintype V]`
assumption so it applies to infinite vertex types. -/
def IsFriendshipGraph (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → (G.commonNeighbors u v).ncard = 1

/-- In a friendship graph, any two distinct vertices have at least one common
neighbour. -/
theorem exists_common_neighbor (hF : IsFriendshipGraph G) {a b : V} (hab : a ≠ b) :
    ∃ x, G.Adj a x ∧ G.Adj b x := by
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp (hF a b hab)
  have hmem : x ∈ G.commonNeighbors a b := by
    rw [hx]; exact Set.mem_singleton_iff.mpr rfl
  rw [SimpleGraph.mem_commonNeighbors] at hmem
  exact ⟨x, hmem.1, hmem.2⟩

/-- **Diameter ≤ 2 (survives infinity).** For any base vertex `v` and any other
vertex `u`, either `u` is a neighbour of `v`, or `u` and `v` share a common
neighbour `x` (so `u` is at distance ≤ 2 from `v`). No finiteness is used. -/
theorem friendship_diameter_two (hF : IsFriendshipGraph G) (v u : V) (huv : u ≠ v) :
    G.Adj v u ∨ ∃ x, G.Adj v x ∧ G.Adj x u := by
  by_cases hadj : G.Adj v u
  · exact Or.inl hadj
  · obtain ⟨x, hvx, hux⟩ := exists_common_neighbor hF (Ne.symm huv)
    exact Or.inr ⟨x, hvx, hux.symm⟩

/-- The diameter-2 covering of the vertex set by a base vertex's 2-ball. -/
theorem univ_subset_two_ball (hF : IsFriendshipGraph G) (v : V) :
    (Set.univ : Set V) ⊆
      {v} ∪ G.neighborSet v ∪ (⋃ x ∈ G.neighborSet v, G.neighborSet x) := by
  intro u _
  by_cases huv : u = v
  · exact Or.inl (Or.inl (Set.mem_singleton_iff.mpr huv))
  · by_cases hadj : G.Adj v u
    · exact Or.inl (Or.inr ((G.mem_neighborSet v u).mpr hadj))
    · obtain ⟨x, hvx, hux⟩ := exists_common_neighbor hF (Ne.symm huv)
      refine Or.inr (Set.mem_biUnion (x := x) ?_ ?_)
      · exact (G.mem_neighborSet v x).mpr hvx
      · exact (G.mem_neighborSet x u).mpr hux.symm

/-- **Local finiteness restores finiteness.** If every neighbourhood of a friendship
graph is finite, the whole vertex set is finite: the 2-ball covering exhibits it as
a finite union of finite sets. This is the sharp restoring condition — the only
obstruction to the infinite theorem is an infinite-degree vertex. -/
theorem univ_finite_of_locallyFinite (hF : IsFriendshipGraph G)
    (hfin : ∀ w : V, (G.neighborSet w).Finite) :
    (Set.univ : Set V).Finite := by
  rcases isEmpty_or_nonempty V with he | hne
  · rw [Set.univ_eq_empty_iff.mpr he]; exact Set.finite_empty
  · obtain ⟨v⟩ := hne
    have hcover : ({v} ∪ G.neighborSet v ∪
        (⋃ x ∈ G.neighborSet v, G.neighborSet x)).Finite := by
      refine Set.Finite.union (Set.Finite.union (Set.finite_singleton v) (hfin v)) ?_
      exact Set.Finite.biUnion (hfin v) (fun x _ => hfin x)
    exact hcover.subset (univ_subset_two_ball hF v)

/-- A locally finite friendship graph has a finite vertex type. -/
theorem locally_finite_is_finite (hF : IsFriendshipGraph G)
    (hfin : ∀ w : V, (G.neighborSet w).Finite) :
    Finite V :=
  Set.finite_univ_iff.mp (univ_finite_of_locallyFinite hF hfin)

/-- **The sharp obstruction (contrapositive).** Every *infinite* friendship graph
has a vertex of infinite degree. Equivalently, the sole reason the finite theorem
fails on infinite graphs is the presence of an infinite-degree vertex — exactly the
feature of the C₅ free-amalgamation counterexample, where every vertex is locally
infinite. This is the direct OQ-04 "where does the proof break" statement, derived
from `locally_finite_is_finite` with no spectral input. -/
theorem infinite_friendship_has_infinite_degree (hF : IsFriendshipGraph G) [Infinite V] :
    ∃ w : V, (G.neighborSet w).Infinite := by
  by_contra h
  push_neg at h
  have hfin : ∀ w : V, (G.neighborSet w).Finite := fun w => h w
  haveI : Finite V := locally_finite_is_finite hF hfin
  exact not_finite V

/-- **Conclusion restored.** A locally finite friendship graph with at least three
vertices has a universal vertex — recovered from the finite gallery theorem via the
finiteness above, with no spectral input on the infinite side. -/
theorem locally_finite_friendship_has_universal (hF : IsFriendshipGraph G)
    (hfin : ∀ w : V, (G.neighborSet w).Finite)
    (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ z : V, FriendshipTheorem.IsUniversalVertex G z := by
  haveI : Finite V := locally_finite_is_finite hF hfin
  classical
  letI : Fintype V := Fintype.ofFinite V
  have h3 : 3 ≤ Fintype.card V := by
    have hcard : ({a, b, c} : Finset V).card = 3 := by
      rw [Finset.card_eq_three]; exact ⟨a, b, c, hab, hac, hbc, rfl⟩
    calc 3 = ({a, b, c} : Finset V).card := hcard.symm
      _ ≤ Fintype.card V := Finset.card_le_univ _
  exact FriendshipTheorem.friendship_theorem G (fun u v h => hF u v h) h3

/-- **Infinite windmill structure.** In a friendship graph with a universal vertex
`c` (finite **or** infinite), every non-centre vertex `u` is adjacent to *exactly*
two vertices — the centre `c` and a unique "partner" `w` — so `N(u) = {c, w}`. The
graph is therefore a windmill (triangles `{c, u, w}` sharing the centre) even when
infinite. No `[Fintype V]` assumption is used: the finite gallery proof
`FriendshipTheorem.friendship_noncentral_degree` derives `G.degree u = 2` (a
`Fintype` notion); this states the underlying *set* equality directly, which holds
verbatim on infinite vertex types. -/
theorem universal_noncentral_neighborSet (hF : IsFriendshipGraph G)
    (c : V) (hc : FriendshipTheorem.IsUniversalVertex G c) (u : V) (hu : u ≠ c) :
    ∃ w, w ≠ c ∧ w ≠ u ∧ G.Adj u w ∧ G.neighborSet u = {c, w} := by
  obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp (hF u c hu)
  have hw_mem : w ∈ G.commonNeighbors u c := by
    rw [hw]; exact Set.mem_singleton_iff.mpr rfl
  rw [SimpleGraph.mem_commonNeighbors] at hw_mem
  have hwu : w ≠ u := fun heq => G.loopless u (heq ▸ hw_mem.1)
  have hwc : w ≠ c := fun heq => G.loopless c (heq ▸ hw_mem.2)
  refine ⟨w, hwc, hwu, hw_mem.1, ?_⟩
  ext x
  simp only [SimpleGraph.mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hadj
    by_cases hxc : x = c
    · exact Or.inl hxc
    · refine Or.inr ?_
      have hcx : G.Adj c x := hc x hxc
      have hxmem : x ∈ G.commonNeighbors u c :=
        (SimpleGraph.mem_commonNeighbors G).mpr ⟨hadj, hcx⟩
      exact Set.mem_singleton_iff.mp (hw ▸ hxmem)
  · rintro (rfl | rfl)
    · exact G.symm (hc u hu)
    · exact hw_mem.1

/-- Every non-centre vertex of a friendship graph with a universal vertex has
exactly two neighbours (`ncard = 2`), with no `[Fintype V]` assumption — the
finiteness-free analogue of `FriendshipTheorem.friendship_noncentral_degree`. -/
theorem universal_noncentral_ncard_two (hF : IsFriendshipGraph G)
    (c : V) (hc : FriendshipTheorem.IsUniversalVertex G c) (u : V) (hu : u ≠ c) :
    (G.neighborSet u).ncard = 2 := by
  obtain ⟨w, hwc, _, _, hset⟩ := universal_noncentral_neighborSet hF c hc u hu
  rw [hset, Set.ncard_pair (Ne.symm hwc)]

/-- **Only the centre can have infinite degree.** In any friendship graph with a
universal vertex `c`, every vertex of infinite degree equals `c`: a non-centre
vertex sits in a single triangle and has exactly two neighbours (`ncard = 2`),
so an infinite neighbourhood (`ncard = 0`) is impossible. No `[Infinite V]`
assumption is needed — this is a pure structural fact about the windmill. -/
theorem infinite_degree_vertex_eq_universal (hF : IsFriendshipGraph G)
    (c : V) (hc : FriendshipTheorem.IsUniversalVertex G c)
    (w : V) (hw : (G.neighborSet w).Infinite) : w = c := by
  by_contra hwc
  have htwo : (G.neighborSet w).ncard = 2 := universal_noncentral_ncard_two hF c hc w hwc
  rw [hw.ncard] at htwo
  omega

/-- **The hub has infinite degree.** If an *infinite* friendship graph has a
universal vertex `c`, then `c` itself has infinite degree. Combined with
`infinite_friendship_has_infinite_degree` (which guarantees *some* infinite-degree
vertex) and `infinite_degree_vertex_eq_universal` (which forces it to be `c`), the
hub is exactly that vertex. -/
theorem universal_vertex_infinite_degree (hF : IsFriendshipGraph G) [Infinite V]
    (c : V) (hc : FriendshipTheorem.IsUniversalVertex G c) :
    (G.neighborSet c).Infinite := by
  obtain ⟨w, hw⟩ := infinite_friendship_has_infinite_degree hF
  rwa [infinite_degree_vertex_eq_universal hF c hc w hw] at hw

/-- **Unique hub of the infinite windmill.** In an infinite friendship graph with a
universal vertex `c`, the centre `c` is the *unique* vertex of infinite degree:
`(G.neighborSet w).Infinite ↔ w = c`. This sharpens the obstruction
`infinite_friendship_has_infinite_degree` (which only gives *at least one*
infinite-degree vertex) to *exactly one* in the conclusion-restored case — the
infinite windmill is "as infinite as the finite theorem permits", with a single
infinite-degree hub and every other vertex of degree two. -/
theorem unique_infinite_degree_vertex (hF : IsFriendshipGraph G) [Infinite V]
    (c : V) (hc : FriendshipTheorem.IsUniversalVertex G c) (w : V) :
    (G.neighborSet w).Infinite ↔ w = c := by
  constructor
  · exact infinite_degree_vertex_eq_universal hF c hc w
  · rintro rfl
    exact universal_vertex_infinite_degree hF w hc

/-- **Regularity (finiteness-free).** In any friendship graph, two *non-adjacent*
vertices `u`, `v` have equinumerous neighbourhoods: the map sending each neighbour `w`
of `u` to the unique common neighbour of `w` and `v` is a bijection `N(u) → N(v)`.
This is the infinite analogue of the classical "non-adjacent vertices have equal
degree" lemma — the step the finite proof uses to conclude the graph is regular before
the spectral argument. It characterizes the *negative* side of OQ-04: a friendship
graph with no universal vertex contains non-adjacent pairs, hence is regular (the C₅
free-amalgamation counterexample is ℵ₀-regular). The conclusion is a `Set.BijOn`, so it
retains content on infinite neighbourhoods (where `ncard` collapses to `0`); no
finiteness is used. -/
theorem nonadjacent_neighborSet_equinum (hF : IsFriendshipGraph G)
    {u v : V} (hadj : ¬ G.Adj u v) :
    ∃ f : V → V, Set.BijOn f (G.neighborSet u) (G.neighborSet v) := by
  classical
  -- Choose, for each `w ≠ v`, the unique common neighbour of `w` and `v`.
  have hex : ∀ w : V, ∃ x : V, w ≠ v → (G.Adj w x ∧ G.Adj v x) := by
    intro w
    by_cases h : w = v
    · exact ⟨v, fun hc => absurd h hc⟩
    · obtain ⟨x, hx⟩ := exists_common_neighbor hF h
      exact ⟨x, fun _ => hx⟩
  choose f hf using hex
  refine ⟨f, ?_, ?_, ?_⟩
  · -- MapsTo: `f` sends a neighbour of `u` to a neighbour of `v`.
    intro w hw
    rw [SimpleGraph.mem_neighborSet] at hw
    have hwv : w ≠ v := fun h => hadj (h ▸ hw)
    rw [SimpleGraph.mem_neighborSet]
    exact (hf w hwv).2
  · -- InjOn: distinct neighbours of `u` map to distinct common neighbours.
    intro w₁ hw₁ w₂ hw₂ heq
    rw [SimpleGraph.mem_neighborSet] at hw₁ hw₂
    have hw₁v : w₁ ≠ v := fun h => hadj (h ▸ hw₁)
    have hw₂v : w₂ ≠ v := fun h => hadj (h ▸ hw₂)
    obtain ⟨h1w, h1v⟩ := hf w₁ hw₁v
    obtain ⟨h2w, h2v⟩ := hf w₂ hw₂v
    have hxu : f w₁ ≠ u := fun h => hadj ((h ▸ h1v).symm)
    have hmem₁ : w₁ ∈ G.commonNeighbors (f w₁) u :=
      (SimpleGraph.mem_commonNeighbors G).mpr ⟨h1w.symm, hw₁⟩
    have hmem₂ : w₂ ∈ G.commonNeighbors (f w₁) u := by
      have hb : w₂ ∈ G.commonNeighbors (f w₂) u :=
        (SimpleGraph.mem_commonNeighbors G).mpr ⟨h2w.symm, hw₂⟩
      rwa [← heq] at hb
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp (hF (f w₁) u hxu)
    rw [ha, Set.mem_singleton_iff] at hmem₁ hmem₂
    rw [hmem₁, hmem₂]
  · -- SurjOn: every neighbour of `v` is hit, via the common neighbour with `u`.
    intro y hy
    rw [SimpleGraph.mem_neighborSet] at hy
    have hyu : y ≠ u := fun h => hadj ((h ▸ hy).symm)
    obtain ⟨w, hyw, huw⟩ := exists_common_neighbor hF hyu
    have hwv : w ≠ v := fun h => hadj (h ▸ huw)
    refine ⟨w, (SimpleGraph.mem_neighborSet G u w).mpr huw, ?_⟩
    obtain ⟨hwf, hvf⟩ := hf w hwv
    have hy_mem : y ∈ G.commonNeighbors w v :=
      (SimpleGraph.mem_commonNeighbors G).mpr ⟨hyw.symm, hy⟩
    have hfw_mem : f w ∈ G.commonNeighbors w v :=
      (SimpleGraph.mem_commonNeighbors G).mpr ⟨hwf, hvf⟩
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp (hF w v hwv)
    rw [ha, Set.mem_singleton_iff] at hy_mem hfw_mem
    rw [hfw_mem, hy_mem]

/-- **Partnership is symmetric (the windmill is a perfect matching off the centre).**
In a friendship graph with universal vertex `c`, if a non-centre vertex `u` has
`N(u) = {c, w}` then its partner `w` satisfies `N(w) = {c, u}` in turn. So the
"partner" relation on non-centre vertices is an involution: the graph with the
centre deleted is a disjoint union of edges (the windmill spokes), each triangle
`{c, u, w}` meeting the others only at the hub `c`. This sharpens
`universal_noncentral_neighborSet`, which gives each vertex a partner but does not
say the pairing is mutual. No `[Fintype V]` assumption is used. -/
theorem universal_partner_symm (hF : IsFriendshipGraph G)
    (c : V) (hc : FriendshipTheorem.IsUniversalVertex G c) (u : V) (hu : u ≠ c) :
    ∃ w, w ≠ c ∧ G.neighborSet u = {c, w} ∧ G.neighborSet w = {c, u} := by
  obtain ⟨w, hwc, _, hadj_uw, hset_u⟩ := universal_noncentral_neighborSet hF c hc u hu
  obtain ⟨u', _, _, _, hset_w⟩ := universal_noncentral_neighborSet hF c hc w hwc
  -- `u` is a neighbour of `w` and is not the centre, so it is `w`'s unique partner `u'`.
  have hu_mem : u ∈ G.neighborSet w := (G.mem_neighborSet w u).mpr hadj_uw.symm
  rw [hset_w] at hu_mem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu_mem
  rcases hu_mem with h | h
  · exact absurd h hu
  · rw [← h] at hset_w
    exact ⟨w, hwc, hset_u, hset_w⟩

/-- **Each non-centre vertex has a unique partner.** In a friendship graph with a
universal vertex `c`, every vertex `u ≠ c` is adjacent to *exactly one* non-centre
vertex. Combined with `universal_partner_symm` this is the perfect-matching
description of the windmill spokes. -/
theorem universal_noncentral_unique_partner (hF : IsFriendshipGraph G)
    (c : V) (hc : FriendshipTheorem.IsUniversalVertex G c) (u : V) (hu : u ≠ c) :
    ∃! w, w ≠ c ∧ G.Adj u w := by
  obtain ⟨w, hwc, _, hadj_uw, hset_u⟩ := universal_noncentral_neighborSet hF c hc u hu
  refine ⟨w, ⟨hwc, hadj_uw⟩, ?_⟩
  rintro w' ⟨hw'c, hadj_uw'⟩
  have hmem : w' ∈ G.neighborSet u := (G.mem_neighborSet u w').mpr hadj_uw'
  rw [hset_u] at hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h
  · exact absurd h hw'c
  · exact h

/-- **Off-centre adjacency is partnership.** For two non-centre vertices `u`, `u'`
of a friendship graph with universal vertex `c`, they are adjacent iff they are each
other's partners (`N(u) = {c, u'}`). This pins down the entire edge set: the hub `c`
is joined to everything, and the only other edges pair partners — exactly the
windmill. No `[Fintype V]` assumption is used. -/
theorem universal_noncentral_adj_iff (hF : IsFriendshipGraph G)
    (c : V) (hc : FriendshipTheorem.IsUniversalVertex G c)
    {u u' : V} (hu : u ≠ c) (hu' : u' ≠ c) :
    G.Adj u u' ↔ G.neighborSet u = {c, u'} := by
  obtain ⟨w, _, _, _, hset_u⟩ := universal_noncentral_neighborSet hF c hc u hu
  constructor
  · intro hadj
    have hmem : u' ∈ G.neighborSet u := (G.mem_neighborSet u u').mpr hadj
    rw [hset_u] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h
    · exact absurd h hu'
    · rw [h]; exact hset_u
  · intro hset
    have hmem : u' ∈ G.neighborSet u := by rw [hset]; simp
    exact (G.mem_neighborSet u u').mp hmem

end FriendshipTheoremOQ04
