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

* `infinite_friendship_has_infinite_degree` — the contrapositive: every *infinite*
  friendship graph is forced to contain a vertex of infinite degree. Infinite degree
  is not incidental to the known counterexamples — it is unavoidable.

* `locally_finite_friendship_has_universal` — combining the above with the finite
  gallery theorem `FriendshipTheorem.friendship_theorem` recovers a universal
  vertex for any locally finite friendship graph with at least three vertices.

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
      refine Or.inr (Set.mem_biUnion ?_ ?_)
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

/-- **The sharp obstruction, stated positively.** Every *infinite* friendship graph
has a vertex of infinite degree. This is the exact contrapositive of
`locally_finite_is_finite`: an infinite friendship graph cannot be locally finite, so
infinite degree is *forced*, not incidental. It pinpoints where the finite proof
breaks — the dichotomy/spectral machinery silently assumes finite degrees. -/
theorem infinite_friendship_has_infinite_degree (hF : IsFriendshipGraph G) [Infinite V] :
    ∃ w : V, (G.neighborSet w).Infinite := by
  by_contra h
  have hfin : ∀ w : V, (G.neighborSet w).Finite := by
    intro w
    by_contra hw
    exact h ⟨w, hw⟩
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

end FriendshipTheoremOQ04
