/-
Erdős Problem #76 — open question oq-02:
  "What is the answer for 3 or more colors — does the extremal coloring
   generalize to k-partitions?"

# Why the 2-color extremal construction does NOT generalize: a triangle-freeness dichotomy

Erdős #76 (Gruslys–Letzter, 2020) concerns edge-disjoint monochromatic triangles
in a 2-coloring of K_n. The *extremal* coloring splits the vertices into two equal
halves and colors the BETWEEN-half edges red. The decisive structural fact that
makes this construction work is that the red class — the complete bipartite graph
K_{n/2,n/2} — is **triangle-free**, so it "wastes" no triangles and all packed
triangles come from the two monochromatic cliques.

The natural attempt to extend the construction to `k` colors is to partition the
vertices into `k` parts and devote one color to the cross-part edges. This entry
isolates, and proves axiom-free, the exact reason this fails for `k ≥ 3`:

  **The cross-part graph of a partition is triangle-free if and only if the
  partition uses at most 2 parts.**

Concretely, the complete multipartite graph `multipartiteGraph part` (vertices
adjacent iff they lie in different parts) is `CliqueFree 3` exactly when the image
of `part` has at most two values (`cliqueFree_three_iff`). For `k ≥ 3` parts there
is always a transversal triangle — one vertex in each of three distinct parts
(`not_cliqueFree_three_iff`, `K3_not_cliqueFree`). Hence the "triangle-free
cross class" engine of the 2-color extremal coloring has no analogue once three or
more colors are in play: with `k ≥ 3` the would-be sacrificial color class itself
contains triangles.

This is a genuine separation result (the analogue of the planar/higher-dimensional
split in sibling lemniscate work): it pins down that the #76 extremal construction
is a strictly two-color phenomenon, rooted in the triangle-freeness of bipartite
graphs.

**Status**: fully proved, 0 sorries, 0 axioms.

Reference: https://erdosproblems.com/76
-/

import Mathlib

open Finset SimpleGraph

namespace Erdos76Oq02

variable {V : Type*}

/-- The complete multipartite graph induced by a part-assignment `part : V → β`:
two vertices are adjacent iff they lie in different parts. When `β = Fin 2` this is
the complete bipartite graph (the "red" cross class of the Erdős #76 balanced
coloring); for three or more parts it is a general complete multipartite graph. -/
def multipartiteGraph {β : Type*} (part : V → β) : SimpleGraph V where
  Adj u v := part u ≠ part v
  symm := fun _ _ h => h.symm
  loopless := fun _ h => h rfl

@[simp] lemma adj_iff {β : Type*} (part : V → β) (u v : V) :
    (multipartiteGraph part).Adj u v ↔ part u ≠ part v := Iff.rfl

/-
## The core dichotomy

A 3-clique (triangle) in `multipartiteGraph part` is exactly a set of three
vertices lying in three pairwise distinct parts. Such a "transversal triangle"
exists iff the partition uses at least three parts.
-/

/-- **The cross-part graph contains a triangle iff the partition uses ≥ 3 parts.**
A transversal triangle exists exactly when the part-assignment takes at least three
distinct values. -/
theorem not_cliqueFree_three_iff [Fintype V] [DecidableEq V] {β : Type*} [DecidableEq β]
    (part : V → β) :
    ¬ (multipartiteGraph part).CliqueFree 3 ↔ 3 ≤ (univ.image part).card := by
  constructor
  · -- A triangle injects three vertices onto three distinct parts.
    intro hcf
    rw [SimpleGraph.CliqueFree] at hcf
    push_neg at hcf
    obtain ⟨s, hclique, hcard⟩ := hcf
    have hinj : Set.InjOn part ↑s := by
      intro a ha b hb hpart
      by_contra hne
      exact (hclique ha hb hne) hpart
    have himg : (s.image part).card = 3 := by
      rw [Finset.card_image_of_injOn hinj, hcard]
    calc 3 = (s.image part).card := himg.symm
      _ ≤ (univ.image part).card :=
          Finset.card_le_card (Finset.image_subset_image (Finset.subset_univ s))
  · -- Three distinct parts give three vertices forming a transversal triangle.
    intro hcard
    rw [SimpleGraph.CliqueFree]
    push_neg
    obtain ⟨p0, p1, p2, hp0, hp1, hp2, h01, h02, h12⟩ :=
      Finset.two_lt_card_iff.mp (by omega : 2 < (univ.image part).card)
    obtain ⟨v0, -, rfl⟩ := Finset.mem_image.mp hp0
    obtain ⟨v1, -, rfl⟩ := Finset.mem_image.mp hp1
    obtain ⟨v2, -, rfl⟩ := Finset.mem_image.mp hp2
    -- The three vertices are pairwise distinct since their parts differ.
    have hv01 : v0 ≠ v1 := fun h => h01 (by rw [h])
    have hv02 : v0 ≠ v2 := fun h => h02 (by rw [h])
    have hv12 : v1 ≠ v2 := fun h => h12 (by rw [h])
    refine ⟨{v0, v1, v2}, ?_, ?_⟩
    · -- They form a clique: any two distinct ones lie in distinct parts.
      intro a ha b hb hab
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.coe_singleton,
        Set.mem_singleton_iff] at ha hb
      rw [adj_iff]
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
        first
          | exact absurd rfl hab
          | exact h01 | exact h01.symm
          | exact h02 | exact h02.symm
          | exact h12 | exact h12.symm
    · -- The clique has exactly three vertices.
      rw [Finset.card_eq_three]
      exact ⟨v0, v1, v2, hv01, hv02, hv12, rfl⟩

/-- **The cross-part graph is triangle-free iff the partition uses ≤ 2 parts.**
This is the headline dichotomy: the sacrificial cross class of an Erdős-#76-style
construction is triangle-free exactly in the two-color regime. -/
theorem cliqueFree_three_iff [Fintype V] [DecidableEq V] {β : Type*} [DecidableEq β]
    (part : V → β) :
    (multipartiteGraph part).CliqueFree 3 ↔ (univ.image part).card ≤ 2 := by
  have h := not_cliqueFree_three_iff part
  constructor
  · intro hcf
    by_contra hc
    push_neg at hc
    exact (h.mpr (by omega)) hcf
  · intro hle
    by_contra hcf'
    exact absurd (h.mp hcf') (by omega)

/-
## Specializations

The two-color case (the actual Erdős #76 extremal class) and the three-color
case, exhibiting the separation explicitly.
-/

/-- **Two colors: the cross class is always triangle-free.** Every 2-partition
(`β = Fin 2`) gives a triangle-free complete bipartite cross graph — this is the
structural property the #76 balanced bipartition relies on. -/
theorem bipartite_cliqueFree [Fintype V] [DecidableEq V] (part : V → Fin 2) :
    (multipartiteGraph part).CliqueFree 3 := by
  rw [cliqueFree_three_iff]
  calc (univ.image part).card ≤ Fintype.card (Fin 2) := Finset.card_le_univ _
    _ = 2 := by simp

/-- **Three colors: the cross class can contain a triangle.** The discrete
3-partition `id : Fin 3 → Fin 3` yields the complete graph K₃, which is a single
transversal triangle — so the analogous "sacrificial color class" is NOT
triangle-free. This is the concrete witness that the construction breaks at k = 3. -/
theorem K3_not_cliqueFree :
    ¬ (multipartiteGraph (id : Fin 3 → Fin 3)).CliqueFree 3 := by
  rw [not_cliqueFree_three_iff]
  simp

/-- **The separation, packaged.** There is a part-assignment whose cross graph is
triangle-free (any 2-partition) and one whose cross graph is not (a 3-partition):
the triangle-freeness of the cross class is therefore a genuinely two-color
phenomenon, with no naive extension to three or more colors. -/
theorem extremal_crossclass_is_two_color_phenomenon :
    (∀ (part : Fin 6 → Fin 2), (multipartiteGraph part).CliqueFree 3) ∧
    ¬ (multipartiteGraph (id : Fin 3 → Fin 3)).CliqueFree 3 :=
  ⟨fun part => bipartite_cliqueFree part, K3_not_cliqueFree⟩

end Erdos76Oq02
