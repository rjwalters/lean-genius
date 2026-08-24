import Proofs.Erdos85BinaryCutGraphTwoPoleRoute

/-!
# Flipping and same-side edge parity

Every edge population splits exactly into edges crossing a Boolean shore and
edges staying on one side.  Over `ZMod 2`, this gives the source identity
`same = total + flip` used in `(73rnz_cjibkz)`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The spanning subgraph consisting of edges whose endpoints lie on the
same side of `B`. -/
def binaryVertexSameSideGraph
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (B : Finset V) :
    SimpleGraph V where
  Adj u v := G.Adj u v ∧ ((u ∈ B) = (v ∈ B))
  symm := ⟨by
    rintro u v ⟨huv, hsame⟩
    exact ⟨huv.symm, hsame.symm⟩⟩
  loopless := ⟨by
    intro u h
    exact G.loopless.irrefl u h.1⟩

instance binaryVertexSameSideGraph_instDecidableRelAdj
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (B : Finset V) :
    DecidableRel (binaryVertexSameSideGraph G B).Adj := fun u v => by
  change Decidable (G.Adj u v ∧ ((u ∈ B) = (v ∈ B)))
  infer_instance

/-- Flipping and same-side subgraphs reconstruct the ambient graph. -/
theorem binaryVertexCutGraph_sup_sameSideGraph
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (B : Finset V) :
    binaryVertexCutGraph G B ⊔ binaryVertexSameSideGraph G B = G := by
  ext u v
  change (G.Adj u v ∧ (u ∈ B) ≠ (v ∈ B)) ∨
      (G.Adj u v ∧ ((u ∈ B) = (v ∈ B))) ↔ G.Adj u v
  constructor
  · rintro (h | h) <;> exact h.1
  · intro huv
    by_cases hB : (u ∈ B) = (v ∈ B)
    · exact Or.inr ⟨huv, hB⟩
    · exact Or.inl ⟨huv, hB⟩

/-- The flipping and same-side subgraphs are edge-disjoint. -/
theorem binaryVertexCutGraph_inf_sameSideGraph
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (B : Finset V) :
    binaryVertexCutGraph G B ⊓ binaryVertexSameSideGraph G B = ⊥ := by
  ext u v
  simp only [SimpleGraph.inf_adj, binaryVertexCutGraph,
    binaryVertexSameSideGraph, SimpleGraph.bot_adj, iff_false]
  tauto

/-- Exact natural-number partition of the ambient edge population. -/
theorem card_cutEdge_add_card_sameSideEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) :
    (binaryVertexCutGraph G B).edgeFinset.card +
        (binaryVertexSameSideGraph G B).edgeFinset.card =
      G.edgeFinset.card := by
  have hdisj : Disjoint
      (binaryVertexCutGraph G B).edgeFinset
      (binaryVertexSameSideGraph G B).edgeFinset := by
    apply Finset.disjoint_left.mpr
    intro e hecut hesame
    induction e using Sym2.inductionOn with
    | _ u v =>
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          binaryVertexCutGraph, binaryVertexSameSideGraph] at hecut hesame
        exact hecut.2 hesame.2
  have hunion :
      (binaryVertexCutGraph G B).edgeFinset ∪
          (binaryVertexSameSideGraph G B).edgeFinset = G.edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
        simp only [Finset.mem_union, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet, binaryVertexCutGraph,
          binaryVertexSameSideGraph]
        constructor
        · rintro (h | h) <;> exact h.1
        · intro huv
          by_cases hB : (u ∈ B) = (v ∈ B)
          · exact Or.inr ⟨huv, hB⟩
          · exact Or.inl ⟨huv, hB⟩
  calc
    (binaryVertexCutGraph G B).edgeFinset.card +
        (binaryVertexSameSideGraph G B).edgeFinset.card =
        ((binaryVertexCutGraph G B).edgeFinset ∪
          (binaryVertexSameSideGraph G B).edgeFinset).card :=
      (Finset.card_union_of_disjoint hdisj).symm
    _ = G.edgeFinset.card := congrArg Finset.card hunion

/-- **Same-side parity identity (73rnz_cjibkz).**  In characteristic two,
the same-side count equals the total count plus the flipping count. -/
theorem card_sameSideEdge_cast_eq_card_add_card_cutEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset V) :
    ((binaryVertexSameSideGraph G B).edgeFinset.card : ZMod 2) =
      (G.edgeFinset.card : ZMod 2) +
        ((binaryVertexCutGraph G B).edgeFinset.card : ZMod 2) := by
  have h := congrArg (fun n : ℕ => (n : ZMod 2))
    (card_cutEdge_add_card_sameSideEdge G B)
  push_cast at h
  have hdouble (z : ZMod 2) : z + z = 0 := by
    rw [← two_mul]
    have htwo : (2 : ZMod 2) = 0 := by decide
    rw [htwo, zero_mul]
  calc
    ((binaryVertexSameSideGraph G B).edgeFinset.card : ZMod 2) =
        ((binaryVertexSameSideGraph G B).edgeFinset.card : ZMod 2) +
          (((binaryVertexCutGraph G B).edgeFinset.card : ZMod 2) +
            ((binaryVertexCutGraph G B).edgeFinset.card : ZMod 2)) := by
      rw [hdouble, add_zero]
    _ = (((binaryVertexCutGraph G B).edgeFinset.card : ZMod 2) +
          ((binaryVertexSameSideGraph G B).edgeFinset.card : ZMod 2)) +
        ((binaryVertexCutGraph G B).edgeFinset.card : ZMod 2) := by ring
    _ = (G.edgeFinset.card : ZMod 2) +
        ((binaryVertexCutGraph G B).edgeFinset.card : ZMod 2) := by rw [h]

end

end Erdos85

#print axioms Erdos85.binaryVertexCutGraph_sup_sameSideGraph
#print axioms Erdos85.binaryVertexCutGraph_inf_sameSideGraph
#print axioms Erdos85.card_cutEdge_add_card_sameSideEdge
#print axioms Erdos85.card_sameSideEdge_cast_eq_card_add_card_cutEdge
