/-
Copyright (c) 2024-2025 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite
import Proofs.FriendshipTheorem

/-!
# Friendship Theorem OQ-04: The Infinite Case

## Open Question (friendship-theorem-oq-04)

The finite Friendship Theorem (Erdős–Rényi–Sós, 1966; gallery proof
`FriendshipTheorem`) says: a *finite* graph in which every two distinct
vertices have exactly one common neighbour has a universal vertex (a
"politician"), and is therefore a windmill.

**Does this force a universal vertex when the vertex set is infinite?**

## Answer: NO in general — and the obstruction is precisely *infinite degree*.

This file isolates, with a fully elementary argument, *exactly* which
hypothesis of the finite theorem is doing the work. The classical proof
runs through double counting and a spectral (eigenvalue) step, both of
which are finite-dimensional. We show that the entire spectral machinery
is irrelevant to *why* the theorem can fail infinitely: the single
load-bearing fact is **finiteness of the vertex set**, and finiteness is
recovered for free from **local finiteness**.

### The key structural lemma (diameter ≤ 2)

A friendship graph has diameter ≤ 2: any two distinct vertices either are
adjacent or share a (unique) common neighbour. Consequently, for *any*
fixed vertex `v`,
```
            V  =  {v} ∪ N(v) ∪ ⋃_{w ∈ N(v)} N(w).
```
Every vertex `u` is `v` itself, a neighbour of `v`, or — being non-adjacent
to `v` — joined to `v` through a common neighbour `w ∈ N(v)`, whence
`u ∈ N(w)`.

### The positive result

If `G` is **locally finite** (every vertex has finite degree) the right-hand
side above is a *finite* union of *finite* sets, so `V` is finite. Combined
with the finite gallery theorem:

> **A locally finite friendship graph on ≥ 3 vertices has a universal vertex.**

So local finiteness is the exact extra hypothesis that rescues the windmill
conclusion — but it rescues it by forcing the graph to be finite, *not* by an
independent infinite argument. This is the precise sense in which "the
theorem does not generalize."

### Why the conclusion genuinely fails without it

Contrapositively, any infinite friendship graph must contain a vertex of
**infinite degree**. Two facts pin this down:

* The *infinite windmill* — one centre `c` adjacent to everything, plus
  infinitely many disjoint blade-edges `{aᵢ, bᵢ}` — is a bona fide infinite
  friendship graph (verified computationally for truncations, see
  `literature/`). It *does* have a universal vertex, but that vertex has
  infinite degree; the graph is not locally finite.
* Erdős–Rényi–Sós exhibited infinite friendship graphs with **no** universal
  vertex at all (every vertex of infinite degree, built as a free/Fraïssé
  limit). These are the true counterexamples to the OQ; their construction
  is not elementary and is left as future formalization work.

## What This File Proves

1. `IsFriendshipGraph.exists_common_neighbor` — distinct vertices have a
   common neighbour (the diameter ≤ 2 ingredient).
2. `IsFriendshipGraph.univ_subset_ball` — the cover identity
   `V ⊆ {v} ∪ N(v) ∪ ⋃_{w∈N(v)} N(w)`.
3. `finite_of_locallyFinite` — **a locally finite friendship graph is
   finite.** (Elementary; no spectral theory.)
4. `exists_universalVertex_of_locallyFinite` — the positive answer to the OQ
   via the finite gallery theorem.

## Status
- [x] Diameter ≤ 2 / common-neighbour existence
- [x] Cover identity
- [x] Local finiteness ⇒ finite (elementary)
- [x] Universal-vertex corollary (via gallery `friendship_theorem`)
- [ ] Formalized ERS no-universal-vertex infinite counterexample (future work)
-/

namespace FriendshipTheoremOQ04

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- The **friendship property**, stated for an arbitrary (possibly infinite)
vertex type via `Set.ncard`: every two distinct vertices have exactly one
common neighbour. Definitionally the same as the gallery's
`FriendshipTheorem.IsFriendshipGraph`. -/
def IsFriendshipGraph : Prop :=
  ∀ u v : V, u ≠ v → (G.commonNeighbors u v).ncard = 1

/-- A vertex `c` is **universal** if it is adjacent to every other vertex. -/
def IsUniversalVertex (c : V) : Prop :=
  ∀ v : V, v ≠ c → G.Adj c v

variable {G}

/-- **Diameter ≤ 2 ingredient.** In a friendship graph any two distinct
vertices have a common neighbour. -/
lemma IsFriendshipGraph.exists_common_neighbor
    (hF : G.IsFriendshipGraph) {u v : V} (huv : u ≠ v) :
    ∃ w, w ∈ G.commonNeighbors u v := by
  have h := hF u v huv
  rw [Set.ncard_eq_one] at h
  obtain ⟨w, hw⟩ := h
  exact ⟨w, by rw [hw]⟩

/-- **Cover identity.** Fixing any vertex `v`, every vertex lies in the ball of
radius two around `v`:
`V ⊆ {v} ∪ N(v) ∪ ⋃_{w ∈ N(v)} N(w)`. This is the structural heart of the
infinite friendship theorem. -/
lemma IsFriendshipGraph.univ_subset_ball
    (hF : G.IsFriendshipGraph) (v : V) :
    (Set.univ : Set V) ⊆
      ({v} ∪ G.neighborSet v) ∪ (⋃ w ∈ G.neighborSet v, G.neighborSet w) := by
  intro u _
  by_cases huv : u = v
  · exact Set.mem_union_left _ (Set.mem_union_left _ (by rw [Set.mem_singleton_iff]; exact huv))
  · by_cases hadj : G.Adj v u
    · exact Set.mem_union_left _ (Set.mem_union_right _ ((G.mem_neighborSet v u).mpr hadj))
    · have hne : v ≠ u := fun h => huv h.symm
      obtain ⟨w, hw⟩ := hF.exists_common_neighbor hne
      rw [SimpleGraph.mem_commonNeighbors] at hw
      obtain ⟨hvw, huw⟩ := hw
      refine Set.mem_union_right _ (Set.mem_iUnion₂.mpr ⟨w, ?_, ?_⟩)
      · exact (G.mem_neighborSet v w).mpr hvw
      · exact (G.mem_neighborSet w u).mpr huw.symm

/-- **A locally finite friendship graph is finite.**

The single load-bearing fact behind the finite friendship theorem: by the
cover identity the vertex set is contained in a finite union of finite
neighbour sets, hence is finite. No spectral theory is involved. -/
theorem finite_of_locallyFinite [LocallyFinite G]
    (hF : G.IsFriendshipGraph) : Finite V := by
  rcases isEmpty_or_nonempty V with h | ⟨v⟩
  · have huniv : (Set.univ : Set V).Finite := by
      rw [Set.univ_eq_empty_iff.mpr h]; exact Set.finite_empty
    exact Set.finite_univ_iff.mp huniv
  · have hfin :
        (({v} ∪ G.neighborSet v) ∪
          (⋃ w ∈ G.neighborSet v, G.neighborSet w)).Finite := by
      refine Set.Finite.union (Set.Finite.union ?_ ?_) ?_
      · exact Set.finite_singleton v
      · exact (G.neighborSet v).toFinite
      · exact (G.neighborSet v).toFinite.biUnion (fun w _ => (G.neighborSet w).toFinite)
    exact Set.finite_univ_iff.mp (hfin.subset (hF.univ_subset_ball v))

/-- **The positive answer to OQ-04.** A locally finite friendship graph on
`≥ 3` vertices has a universal vertex.

Local finiteness forces the vertex set to be finite, after which the finite
gallery theorem (`FriendshipTheorem.friendship_theorem`) supplies the
politician. Note `IsUniversalVertex` here is definitionally the gallery's. -/
theorem exists_universalVertex_of_locallyFinite [LocallyFinite G]
    (hF : G.IsFriendshipGraph) (h3 : 3 ≤ Nat.card V) :
    ∃ c, G.IsUniversalVertex c := by
  haveI : Finite V := finite_of_locallyFinite hF
  haveI : Fintype V := Fintype.ofFinite V
  classical
  have hcard : 3 ≤ Fintype.card V := by
    rwa [Nat.card_eq_fintype_card] at h3
  -- `IsFriendshipGraph` (this file) and `FriendshipTheorem.IsFriendshipGraph`
  -- are definitionally identical, as are the two `IsUniversalVertex`.
  obtain ⟨c, hc⟩ := FriendshipTheorem.friendship_theorem G hF hcard
  exact ⟨c, hc⟩

end FriendshipTheoremOQ04
