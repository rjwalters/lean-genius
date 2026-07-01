import Proofs.RandomizedMaxCut
import Mathlib.Combinatorics.SimpleGraph.Basic

/-
# Max-Cut of a Complete Bipartite Graph Equals the Full Edge Count

## What This Proves

For the complete bipartite graph `K_{V,W}` (Mathlib's `completeBipartiteGraph V W`
on the vertex type `V ⊕ W`), the maximum cut value equals the total number of
edges:

  `maxCutValue (completeBipartiteGraph V W) = |E|`,

and this common value is the product of the two side sizes:

  `|E| = card V * card W`.

## Why This Is Interesting

The parent entry (`randomized-maxcut`) proves the *general* upper bound
`maxCutValue G ≤ |E|` and the `1/2`-approximation guarantee of the randomized
algorithm.  A complete bipartite graph is the extremal case where that upper
bound is *attained*: the natural left/right partition is itself a cut, and it
crosses **every** edge.  So the greedy/optimal cut recovers all of `|E|`, and
the randomized `1/2`-approximation is, in the worst case, off by exactly a
factor of two here.

## Proof Strategy

1. `bipartiteAssignment_size_eq_edges`: the assignment `fun x => x.isLeft`
   (left vertices → side `A`, right vertices → side `B`) has cut size `|E|`,
   because in `K_{V,W}` every edge joins a left vertex to a right vertex, so
   `Cut.edgeInCut` is `true` on all of `edgeFinset` (`Finset.filter_true_of_mem`).
2. `maxCut_completeBipartite_eq_edges`: combine `Finset.le_sup` (the supremum
   dominates any single assignment) with the parent's `maxCut_le_edges`.
3. `completeBipartite_edgeFinset_card`: the edges biject with `V × W` via
   `(a, b) ↦ s(inl a, inr b)`, so `|E| = card V * card W` (`Fintype.card_prod`).
-/

open Finset SimpleGraph

namespace RandomizedMaxCutOQ05

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- Adjacency in the complete bipartite graph is decidable. -/
instance : DecidableRel (completeBipartiteGraph V W).Adj := fun v w => by
  rw [completeBipartiteGraph_adj]; infer_instance

/-- **Step 1.** The "left/right" assignment cuts *every* edge of `K_{V,W}`.
Sending each left vertex to side `A` and each right vertex to side `B` produces
a cut whose size is the full edge count, since every edge of a complete
bipartite graph joins the two sides. -/
theorem bipartiteAssignment_size_eq_edges :
    (Cut.ofAssignment (G := completeBipartiteGraph V W) (fun x => x.isLeft)).size
      = (completeBipartiteGraph V W).edgeFinset.card := by
  unfold Cut.size
  refine congrArg Finset.card (Finset.filter_true_of_mem ?_)
  intro e he
  rw [mem_edgeFinset] at he
  induction e using Sym2.ind with
  | _ u v =>
    rw [mem_edgeSet, completeBipartiteGraph_adj] at he
    unfold Cut.edgeInCut Cut.ofAssignment
    simp only [Sym2.lift_mk, Finset.mem_filter, Finset.mem_univ, true_and,
      decide_eq_true_eq]
    cases u <;> cases v <;> simp_all

/-- **Step 2 (main result).** The max-cut value of a complete bipartite graph is
exactly its number of edges. -/
theorem maxCut_completeBipartite_eq_edges :
    maxCutValue (completeBipartiteGraph V W) = (completeBipartiteGraph V W).edgeFinset.card := by
  refine le_antisymm (maxCut_le_edges _) ?_
  calc (completeBipartiteGraph V W).edgeFinset.card
      = (Cut.ofAssignment (G := completeBipartiteGraph V W) (fun x => x.isLeft)).size :=
        (bipartiteAssignment_size_eq_edges).symm
    _ ≤ maxCutValue (completeBipartiteGraph V W) := by
        unfold maxCutValue
        exact Finset.le_sup
          (f := fun f => (Cut.ofAssignment (G := completeBipartiteGraph V W) f).size)
          (Finset.mem_univ (fun x : V ⊕ W => x.isLeft))

/-- **Step 3.** The edges of `K_{V,W}` biject with `V × W`, so the edge count is
the product of the side sizes. -/
theorem completeBipartite_edgeFinset_card :
    (completeBipartiteGraph V W).edgeFinset.card = Fintype.card V * Fintype.card W := by
  have himg : (completeBipartiteGraph V W).edgeFinset
      = (Finset.univ : Finset (V × W)).image (fun p => s(Sum.inl p.1, Sum.inr p.2)) := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [mem_edgeFinset, mem_edgeSet, completeBipartiteGraph_adj, Finset.mem_image,
        Finset.mem_univ, true_and]
      constructor
      · rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
        · cases x with
          | inr _ => simp at hx
          | inl a =>
            cases y with
            | inl _ => simp at hy
            | inr b => exact ⟨(a, b), rfl⟩
        · cases x with
          | inl _ => simp at hx
          | inr b =>
            cases y with
            | inr _ => simp at hy
            | inl a => exact ⟨(a, b), Sym2.eq_swap⟩
      · rintro ⟨⟨a, b⟩, heq⟩
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · subst hx; subst hy; simp
        · subst hx; subst hy; simp
  rw [himg, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_prod]
  intro p q hpq
  simp only [Sym2.eq_iff] at hpq
  rcases hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext (Sum.inl.inj h1) (Sum.inr.inj h2)
  · exact absurd h1 (by simp)

/-- **Corollary.** The max-cut value of `K_{V,W}` equals `card V * card W`. -/
theorem maxCut_completeBipartite_eq_mul :
    maxCutValue (completeBipartiteGraph V W) = Fintype.card V * Fintype.card W := by
  rw [maxCut_completeBipartite_eq_edges, completeBipartite_edgeFinset_card]

end RandomizedMaxCutOQ05
