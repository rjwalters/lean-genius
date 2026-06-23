/-
Copyright (c) 2024-2026 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Proofs.FriendshipTheorem
import Proofs.FriendshipTheoremOQ04

/-!
# Friendship Theorem OQ-04: uniqueness of the hub (finiteness-free)

`Proofs/FriendshipTheoremOQ04.lean` develops the finiteness-free structure theory of the
infinite Friendship Theorem: diameter ≤ 2, local-finiteness as the sharp restoring condition,
the infinite windmill structure (`universal_noncentral_neighborSet`), and the unique
infinite-degree hub (`unique_infinite_degree_vertex`).

This file adds the complementary **uniqueness-of-hub** fact, again with no `[Fintype V]` /
`[Finite V]` assumption:

* `two_universal_cover` — in any friendship graph, two *distinct* universal vertices `c`, `c'`
  force the whole vertex set to be the triangle `{c, c', x}`, where `x` is their unique common
  neighbour. So a friendship graph can have two centres only if it is `K₃`.

* `nat_card_eq_three_of_two_universal` — the immediate corollary: a friendship graph with two
  distinct universal vertices has exactly three vertices (`Nat.card V = 3`).

* `finite_of_two_universal` — hence such a graph is finite.

* `universal_unique_of_card_ne_three` — contrapositive packaging: away from the three-vertex
  triangle, the universal vertex (the windmill centre) is **unique**. This complements the
  windmill description: the recovered finite-theorem conclusion has a single, well-defined hub.

The argument is elementary: the two centres have a unique common neighbour `x` (friendship
applied to `c ≠ c'`); any vertex other than `c`, `c'` is adjacent to both centres (universality),
hence is a common neighbour of `c` and `c'`, hence equals `x`.

* `universal_unique_of_infinite` — the OQ-04 specialization: an *infinite* friendship graph has at
  most one universal vertex (since `Nat.card V = 0 ≠ 3`). Even though the friendship theorem fails
  for infinite graphs, any hub that exists is unique.

## Status

Registered in `Proofs.lean` and Docker build-verified (2026-06-18, 7746 jobs green).
0 sorries, 0 axioms by construction; `#print axioms` reports only Mathlib's standard
`propext` / `Classical.choice` / `Quot.sound`.
-/

namespace FriendshipTheoremOQ04

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- **Two centres force a triangle.** In a friendship graph, if `c` and `c'` are distinct
universal vertices then `V = {c, c', x}`, where `x` is the unique common neighbour of `c` and
`c'`. Finiteness-free: no `[Fintype V]` assumption is used. -/
theorem two_universal_cover (hF : IsFriendshipGraph G)
    {c c' : V} (hc : FriendshipTheorem.IsUniversalVertex G c)
    (hc' : FriendshipTheorem.IsUniversalVertex G c') (hne : c ≠ c') :
    ∃ x, x ≠ c ∧ x ≠ c' ∧ (Set.univ : Set V) = {c, c', x} := by
  -- The two centres have a unique common neighbour `x`.
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp (hF c c' hne)
  have hxmem : x ∈ G.commonNeighbors c c' := by
    rw [hx]; exact Set.mem_singleton_iff.mpr rfl
  rw [SimpleGraph.mem_commonNeighbors] at hxmem
  -- `x` is distinct from both centres (no loops).
  have hxc : x ≠ c := fun h => G.loopless c (h ▸ hxmem.1)
  have hxc' : x ≠ c' := fun h => G.loopless c' (h ▸ hxmem.2)
  refine ⟨x, hxc, hxc', ?_⟩
  ext y
  simp only [Set.mem_univ, true_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
  by_cases hyc : y = c
  · exact Or.inl hyc
  · by_cases hyc' : y = c'
    · exact Or.inr (Or.inl hyc')
    · -- A vertex other than the two centres is adjacent to both, hence is `x`.
      refine Or.inr (Or.inr ?_)
      have hcy : G.Adj c y := hc y hyc
      have hc'y : G.Adj c' y := hc' y hyc'
      have hymem : y ∈ G.commonNeighbors c c' :=
        (SimpleGraph.mem_commonNeighbors G).mpr ⟨hcy, hc'y⟩
      exact Set.mem_singleton_iff.mp (hx ▸ hymem)

/-- A friendship graph with two distinct universal vertices has exactly three vertices. -/
theorem nat_card_eq_three_of_two_universal (hF : IsFriendshipGraph G)
    {c c' : V} (hc : FriendshipTheorem.IsUniversalVertex G c)
    (hc' : FriendshipTheorem.IsUniversalVertex G c') (hne : c ≠ c') :
    Nat.card V = 3 := by
  obtain ⟨x, hxc, hxc', huniv⟩ := two_universal_cover hF hc hc' hne
  have : (Set.univ : Set V).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨c, c', x, hne, hxc.symm, hxc'.symm, huniv⟩
  rwa [Set.ncard_univ] at this

/-- A friendship graph with two distinct universal vertices is finite. -/
theorem finite_of_two_universal (hF : IsFriendshipGraph G)
    {c c' : V} (hc : FriendshipTheorem.IsUniversalVertex G c)
    (hc' : FriendshipTheorem.IsUniversalVertex G c') (hne : c ≠ c') :
    Finite V := by
  obtain ⟨x, _, _, huniv⟩ := two_universal_cover hF hc hc' hne
  have hfin : (Set.univ : Set V).Finite := by
    rw [huniv]; exact (Set.finite_singleton x).insert c' |>.insert c
  exact Set.finite_univ_iff.mp hfin

/-- **Uniqueness of the hub away from the triangle.** If a friendship graph does not have exactly
three vertices, then it has at most one universal vertex: any two universal vertices coincide.
This is the contrapositive of `nat_card_eq_three_of_two_universal`; it shows the windmill centre is
unique except in the degenerate `K₃` case. -/
theorem universal_unique_of_card_ne_three (hF : IsFriendshipGraph G)
    (hcard : Nat.card V ≠ 3)
    {c c' : V} (hc : FriendshipTheorem.IsUniversalVertex G c)
    (hc' : FriendshipTheorem.IsUniversalVertex G c') :
    c = c' := by
  by_contra hne
  exact hcard (nat_card_eq_three_of_two_universal hF hc hc' hne)

/-- **An infinite friendship graph has at most one universal vertex.** Specializing
`universal_unique_of_card_ne_three` to the infinite case: when `V` is infinite, `Nat.card V = 0 ≠ 3`,
so the windmill hub — if it exists — is unique. This is the on-topic OQ-04 takeaway: even though the
friendship theorem itself *fails* for infinite graphs (no hub is forced), whenever a hub does exist
in an infinite friendship graph it is the only one. -/
theorem universal_unique_of_infinite [Infinite V] (hF : IsFriendshipGraph G)
    {c c' : V} (hc : FriendshipTheorem.IsUniversalVertex G c)
    (hc' : FriendshipTheorem.IsUniversalVertex G c') :
    c = c' :=
  universal_unique_of_card_ne_three hF
    (by rw [Nat.card_eq_zero_of_infinite]; decide) hc hc'

end FriendshipTheoremOQ04
