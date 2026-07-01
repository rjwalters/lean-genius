import Proofs.RandomizedMaxCut
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Max-Cut Saturates the Edge Bound Exactly on Bipartite Graphs

The base entry `randomized-maxcut` proves the universal upper bound
`maxCutValue G ≤ |E(G)|` (`maxCut_le_edges`): no cut can cross more edges than
the graph has.  This entry pins down **exactly when that bound is attained**.

## Main results

* `maxCut_eq_edges_of_coloring` — if `G` admits a `Bool`-coloring (i.e. `G` is
  bipartite), then `maxCutValue G = |E(G)|`: the bipartition crosses *every*
  edge, so the trivial upper bound is met.
* `coloring_of_maxCut_eq_edges` — conversely, if the max cut crosses every edge
  then the optimal partition is a proper `2`-coloring, so `G` is bipartite.
* `maxCut_eq_edges_iff_colorable` — the **rigidity characterization**:
  `maxCutValue G = |E(G)| ↔ Nonempty (G.Coloring Bool)`.  Max-Cut saturates the
  edge bound *iff* the graph is bipartite.
* `maxCut_completeBipartiteGraph` — the headline corollary:
  `maxCutValue (completeBipartiteGraph V W) = card V * card W`.  For `K_{m,n}`
  the maximum cut is the entire edge set, of size `m * n`.

The forward direction is the easy "witness" half; the reverse direction is the
extremal content — a rigidity statement in the spirit of "the averaging bound is
tight only in the degenerate (here: bipartite) case".
-/

open Finset SimpleGraph

namespace RandomizedMaxCutOQ05

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Under the cut coming from an assignment `c : V → Bool`, an edge `s(u, v)` is
crossed **iff** its endpoints receive different colours. -/
lemma edgeInCut_ofAssignment {G : SimpleGraph V} (c : V → Bool) (u v : V) :
    (Cut.ofAssignment (G := G) c).edgeInCut s(u, v) = (c u != c v) := by
  simp only [Cut.edgeInCut, Cut.ofAssignment, Sym2.lift_mk, mem_filter, mem_univ, true_and]
  cases c u <;> cases c v <;> decide

/-- If every edge of `G` is crossed by the cut of an assignment `c`, then that
cut has size `|E(G)|`. -/
lemma size_ofAssignment_eq_card_edges {G : SimpleGraph V} [DecidableRel G.Adj]
    (c : V → Bool) (h : ∀ e ∈ G.edgeFinset, (Cut.ofAssignment (G := G) c).edgeInCut e) :
    (Cut.ofAssignment (G := G) c).size = G.edgeFinset.card := by
  unfold Cut.size
  rw [Finset.filter_true_of_mem h]

/-- **Bipartite ⟹ Max-Cut is the whole edge set.**  A `Bool`-coloring of `G`
crosses every edge, so its partition is an optimal cut of size `|E(G)|`. -/
theorem maxCut_eq_edges_of_coloring {G : SimpleGraph V} [DecidableRel G.Adj]
    (C : G.Coloring Bool) : maxCutValue G = G.edgeFinset.card := by
  refine le_antisymm (maxCut_le_edges G) ?_
  set c : V → Bool := fun v => C v with hc
  have hcross : ∀ e ∈ G.edgeFinset, (Cut.ofAssignment (G := G) c).edgeInCut e := by
    intro e
    induction e using Sym2.ind with
    | _ u v =>
      intro he
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      rw [edgeInCut_ofAssignment]
      have hne : C u ≠ C v := C.valid he
      simpa [hc, bne_iff_ne] using hne
  have hsize : (Cut.ofAssignment (G := G) c).size = G.edgeFinset.card :=
    size_ofAssignment_eq_card_edges c hcross
  calc G.edgeFinset.card = (Cut.ofAssignment (G := G) c).size := hsize.symm
    _ ≤ maxCutValue G := by
        rw [maxCutValue]
        exact Finset.le_sup (f := fun f : V → Bool => (Cut.ofAssignment (G := G) f).size)
          (Finset.mem_univ c)

/-- **Max-Cut is the whole edge set ⟹ bipartite.**  If the optimal cut crosses
every edge, the assignment attaining it is a proper `2`-coloring. -/
theorem coloring_of_maxCut_eq_edges {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : maxCutValue G = G.edgeFinset.card) : Nonempty (G.Coloring Bool) := by
  have hne : (Finset.univ : Finset (V → Bool)).Nonempty := Finset.univ_nonempty
  obtain ⟨f, _, hf⟩ :=
    Finset.exists_mem_eq_sup' hne (fun f : V → Bool => (Cut.ofAssignment (G := G) f).size)
  have hsup : maxCutValue G = (Cut.ofAssignment (G := G) f).size := by
    rw [maxCutValue, ← Finset.sup'_eq_sup hne, hf]
  have hsize : (Cut.ofAssignment (G := G) f).size = G.edgeFinset.card := by
    rw [← hsup, h]
  have hfilter :
      G.edgeFinset.filter (fun e => (Cut.ofAssignment (G := G) f).edgeInCut e)
        = G.edgeFinset := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    exact le_of_eq hsize.symm
  have hcross : ∀ e ∈ G.edgeFinset, (Cut.ofAssignment (G := G) f).edgeInCut e :=
    (Finset.filter_eq_self).1 hfilter
  refine ⟨Coloring.mk f ?_⟩
  intro u v huv
  have hmem : s(u, v) ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]; exact huv
  have hc := hcross _ hmem
  rw [edgeInCut_ofAssignment] at hc
  simpa [bne_iff_ne] using hc

/-- **Rigidity characterization.**  The maximum cut saturates the universal edge
bound `maxCutValue G ≤ |E(G)|` **iff** `G` is bipartite (`Bool`-colorable). -/
theorem maxCut_eq_edges_iff_colorable {G : SimpleGraph V} [DecidableRel G.Adj] :
    maxCutValue G = G.edgeFinset.card ↔ Nonempty (G.Coloring Bool) :=
  ⟨coloring_of_maxCut_eq_edges, fun ⟨C⟩ => maxCut_eq_edges_of_coloring C⟩

/-! ## The complete bipartite graph `K_{m,n}` -/

section CompleteBipartite

variable (V W : Type*) [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W]

instance : DecidableRel (completeBipartiteGraph V W).Adj := by
  intro u v
  unfold completeBipartiteGraph
  infer_instance

/-- Degree of a left vertex in `K_{m,n}` is `|W| = n`. -/
lemma degree_inl (a : V) :
    (completeBipartiteGraph V W).degree (Sum.inl a) = Fintype.card W := by
  have hset : (completeBipartiteGraph V W).neighborFinset (Sum.inl a)
      = Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩ := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_map, Finset.mem_univ,
      Function.Embedding.coeFn_mk, true_and]
    cases x with
    | inl b => simp [completeBipartiteGraph]
    | inr w => simp [completeBipartiteGraph]
  rw [SimpleGraph.degree, hset, Finset.card_map, Finset.card_univ]

/-- Degree of a right vertex in `K_{m,n}` is `|V| = m`. -/
lemma degree_inr (b : W) :
    (completeBipartiteGraph V W).degree (Sum.inr b) = Fintype.card V := by
  have hset : (completeBipartiteGraph V W).neighborFinset (Sum.inr b)
      = Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩ := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_map, Finset.mem_univ,
      Function.Embedding.coeFn_mk, true_and]
    cases x with
    | inl a => simp [completeBipartiteGraph]
    | inr w => simp [completeBipartiteGraph]
  rw [SimpleGraph.degree, hset, Finset.card_map, Finset.card_univ]

/-- The number of edges of `K_{m,n}` is `m * n`. -/
lemma card_edgeFinset_completeBipartiteGraph :
    (completeBipartiteGraph V W).edgeFinset.card = Fintype.card V * Fintype.card W := by
  have h := (completeBipartiteGraph V W).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_sum_type] at h
  simp only [degree_inl, degree_inr, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  rw [Nat.mul_comm (Fintype.card W) (Fintype.card V)] at h
  omega

/-- **Headline corollary.**  The maximum cut of the complete bipartite graph
`K_{m,n}` crosses *every* edge, so it equals `|E| = m * n`. -/
theorem maxCut_completeBipartiteGraph :
    maxCutValue (completeBipartiteGraph V W) = Fintype.card V * Fintype.card W := by
  rw [maxCut_eq_edges_of_coloring (CompleteBipartiteGraph.bicoloring V W),
    card_edgeFinset_completeBipartiteGraph]

end CompleteBipartite

end RandomizedMaxCutOQ05
