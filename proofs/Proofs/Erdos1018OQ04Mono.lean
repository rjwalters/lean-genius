/-
# Erdős #1018 (OQ-04) — sub-hypergraph monotonicity of geometric embeddability

`Erdos1018OQ04.lean` defines the linear embeddability predicate `isEmbeddable H d`
(`∃` an injective placement `φ : V → ℝ^d` under which the convex hulls of distinct edges
meet only in the hull of their shared vertices), the higher-dimensional generalisation of
graph planarity used in the van Kampen–Flores obstruction.  It records that a hypergraph
`H` has a *small non-embeddable* induced piece (`hasSmallNonEmbeddable`), the shape of the
Kostochka–Pyber conclusion — but it does not prove that non-embeddability of a piece actually
obstructs the whole graph.

This file supplies that missing structural fact: embeddability is closed under passing to
**sub-hypergraphs**.  Any `H₁` whose edge set is contained in that of an embeddable `H₂` is
itself embeddable — the *same* placement `φ` works, since the convex-hull separation is then
required of fewer edge pairs.  Its contrapositive,

    a non-embeddable sub-hypergraph obstructs the whole graph,

is exactly the logical mechanism behind Erdős #1018 / Kostochka–Pyber: to certify that a
dense (hyper)graph contains a non-embeddable (for `r = 2`, non-planar) subgraph it suffices to
exhibit one small non-embeddable piece.  As a capstone we discharge exactly that reduction:
`hasSmallNonEmbeddable H k → isNonEmbeddable H (criticalDim r)`.  The vertex-induced case is
recovered as the special case where the sub-edge-set is `H.edges.filter (· ⊆ S)`.

All results are `0`-sorry / `0`-axiom on top of Mathlib and `Erdos1018OQ04`; they do not invoke
any of the deep axioms (`vanKampen_Flores`, `triangle_planar`, `K4_planar`, …) declared there.
-/
import Mathlib
import Proofs.Erdos1018OQ04

namespace Erdos1018OQ04

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Embeddability is sub-hypergraph closed.**  If every edge of `H₁` is an edge of `H₂`
    and `H₂` embeds in `ℝ^d`, then `H₁` embeds in `ℝ^d`: the same injective placement `φ`
    works, because the convex-hull separation condition for `H₁` ranges over a subset of the
    edge pairs it holds for in `H₂`. -/
theorem isEmbeddable_of_edges_subset {r d : ℕ}
    {H₁ H₂ : Hypergraph V r} (hsub : H₁.edges ⊆ H₂.edges)
    (hE : isEmbeddable H₂ d) : isEmbeddable H₁ d := by
  obtain ⟨φ, hinj, hsep⟩ := hE
  exact ⟨φ, hinj, fun e₁ he₁ e₂ he₂ hne => hsep e₁ (hsub he₁) e₂ (hsub he₂) hne⟩

/-- **A non-embeddable sub-hypergraph obstructs the whole graph.**  Contrapositive of
    `isEmbeddable_of_edges_subset`: if `H₁ ⊆ H₂` (edge-wise) and `H₁` is non-embeddable in
    `ℝ^d`, then so is `H₂`.  This is the precise logical shape of "a dense (hyper)graph
    containing a non-embeddable subgraph is itself non-embeddable". -/
theorem isNonEmbeddable_of_edges_subset {r d : ℕ}
    {H₁ H₂ : Hypergraph V r} (hsub : H₁.edges ⊆ H₂.edges)
    (hne : isNonEmbeddable H₁ d) : isNonEmbeddable H₂ d :=
  fun hE => hne (isEmbeddable_of_edges_subset hsub hE)

/-- The vertex-induced sub-hypergraph is an edge-subset: `(H.induced S).edges ⊆ H.edges`. -/
theorem induced_edges_subset {r : ℕ} (H : Hypergraph V r) (S : Finset V) :
    (H.induced S).edges ⊆ H.edges := by
  unfold Hypergraph.induced
  exact Finset.filter_subset _ _

/-- **Embeddability is inherited by vertex-induced subgraphs.**  Special case of
    `isEmbeddable_of_edges_subset` for `H.induced S`. -/
theorem isEmbeddable_induced {r d : ℕ} {H : Hypergraph V r} (S : Finset V)
    (hE : isEmbeddable H d) : isEmbeddable (H.induced S) d :=
  isEmbeddable_of_edges_subset (induced_edges_subset H S) hE

/-- **A small non-embeddable induced piece is exactly a whole-graph obstruction.**  Unfolds
    `hasSmallNonEmbeddable H k` (an induced `S`, `|S| ≤ k`, with `H.induced S` non-embeddable
    at the critical dimension) into the conclusion that `H` itself is non-embeddable there —
    closing the gap between "has a small non-embeddable piece" and "is non-embeddable". -/
theorem isNonEmbeddable_of_hasSmallNonEmbeddable {r k : ℕ} {H : Hypergraph V r}
    (h : hasSmallNonEmbeddable H k) : isNonEmbeddable H (criticalDim r) := by
  obtain ⟨S, _, hS⟩ := h
  exact isNonEmbeddable_of_edges_subset (induced_edges_subset H S) hS

end Erdos1018OQ04
