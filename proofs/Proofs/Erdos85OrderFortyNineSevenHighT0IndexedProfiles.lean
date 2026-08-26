import Proofs.Erdos85OrderFortyNineSevenHighT0LowVertexIndexing
import Proofs.Erdos85OrderFortyNineSevenHighT0LocalProfile

/-!
# Graph profiles on the complete low-vertex index

This begins transporting the graph-facing local quotient laws to the exact
`7E + 14S + 21P` index used by the finite completion model.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

def sevenHighT0LowIndexSupportCard : SevenHighT0LowIndex → Nat
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

theorem sevenHighT0LowVertex_support_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (i : SevenHighT0LowIndex) :
    (orderFortyNineHighSupport G
      (sevenHighT0LowVertex G hfree hmin hHigh hzero e i)).card =
        sevenHighT0LowIndexSupportCard i := by
  rw [← sevenHighLabeledSupport_card G e]
  rcases i with i | i
  · simp only [sevenHighT0LowVertex]
    rw [sevenHighT0EmptyVertex_support]
    rfl
  · rcases i with i | i
    · simp only [sevenHighT0LowVertex]
      rw [sevenHighT0SingletonVertex_support]
      simp [sevenHighT0LowIndexSupportCard]
    · simp only [sevenHighT0LowVertex]
      rw [sevenHighT0PairVertex_support]
      simp [sevenHighT0LowIndexSupportCard, ne_of_lt i.2]

theorem sevenHighT0LowVertex_degree_eq_seven
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (i : SevenHighT0LowIndex) :
    G.degree (sevenHighT0LowVertex
      G hfree hmin hHigh hzero e i) = 7 := by
  let y := sevenHighT0LowVertex G hfree hmin hHigh hzero e i
  have hyLow : y.1 ∈ orderFortyNineLowVertices G := y.2
  have hyNotHigh : y.1 ∉ orderFortyNineHighVertices G :=
    (Finset.mem_sdiff.mp hyLow).2
  rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin (Fintype.card_fin 49) y.1 with hy7 | hy8
  · exact hy7
  · exfalso
    apply hyNotHigh
    simp [orderFortyNineHighVertices, hy8]

/-- The actual graph induced on low vertices, transported to the complete
`7E + 14S + 21P` index. -/
def sevenHighT0LowGraph
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7) :
    SimpleGraph SevenHighT0LowIndex :=
  G.comap fun i =>
    (sevenHighT0LowVertex G hfree hmin hHigh hzero e i).1

instance sevenHighT0LowGraph_adj_decidable
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7) :
    DecidableRel (sevenHighT0LowGraph
      G hfree hmin hHigh hzero e).Adj := by
  intro i j
  change Decidable (G.Adj _ _)
  infer_instance

theorem sevenHighT0LowGraph_adj_iff
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (i j : SevenHighT0LowIndex) :
    (sevenHighT0LowGraph G hfree hmin hHigh hzero e).Adj i j ↔
      G.Adj
        (sevenHighT0LowVertex G hfree hmin hHigh hzero e i)
        (sevenHighT0LowVertex G hfree hmin hHigh hzero e j) := Iff.rfl

private theorem sevenHighT0LowGraph_degree_eq_lowNeighborCount
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (i : SevenHighT0LowIndex) :
    (sevenHighT0LowGraph G hfree hmin hHigh hzero e).degree i =
      ((G.neighborFinset
        (sevenHighT0LowVertex G hfree hmin hHigh hzero e i)).filter
          fun x => x ∉ orderFortyNineHighVertices G).card := by
  rw [SimpleGraph.degree]
  apply Finset.card_bij
      (fun j _ => (sevenHighT0LowVertex
        G hfree hmin hHigh hzero e j).1)
  · intro j hj
    apply Finset.mem_filter.mpr
    refine ⟨?_, (Finset.mem_sdiff.mp
      (sevenHighT0LowVertex G hfree hmin hHigh hzero e j).2).2⟩
    simpa [SimpleGraph.mem_neighborFinset, sevenHighT0LowGraph] using hj
  · intro a ha b hb hab
    exact sevenHighT0LowVertex_injective
      G hfree hmin hHigh hzero e (Subtype.ext hab)
  · intro x hx
    have hx' := Finset.mem_filter.mp hx
    let xLow : {z : Fin 49 // z ∈ orderFortyNineLowVertices G} :=
      ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx'.2⟩⟩
    let j := (sevenHighT0LowVertexEquiv
      G hfree hmin hHigh hzero e).symm xLow
    have hjx : (sevenHighT0LowVertex
        G hfree hmin hHigh hzero e j).1 = x := by
      change (sevenHighT0LowVertexEquiv
        G hfree hmin hHigh hzero e j).1 = x
      simp [j, xLow, sevenHighT0LowVertexEquiv]
    refine ⟨j, ?_, ?_⟩
    · simpa [SimpleGraph.mem_neighborFinset, sevenHighT0LowGraph, hjx]
        using hx'.1
    · exact hjx

/-- The indexed low degree is the ambient degree seven minus the number of
high neighbors carried by the root's support. -/
theorem sevenHighT0LowGraph_degree_add_supportCard_eq_seven
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 7)
    (i : SevenHighT0LowIndex) :
    (sevenHighT0LowGraph G hfree hmin hHigh hzero e).degree i +
      sevenHighT0LowIndexSupportCard i = 7 := by
  let y := (sevenHighT0LowVertex G hfree hmin hHigh hzero e i).1
  have hdegree := sevenHighT0LowVertex_degree_eq_seven
    G hfree hmin hHigh hzero e i
  change G.degree y = 7 at hdegree
  have hlow := sevenHighT0LowGraph_degree_eq_lowNeighborCount
    G hfree hmin hHigh hzero e i
  change (sevenHighT0LowGraph G hfree hmin hHigh hzero e).degree i =
    ((G.neighborFinset y).filter fun x =>
      x ∉ orderFortyNineHighVertices G).card at hlow
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := G.neighborFinset y)
    (p := fun x => x ∈ orderFortyNineHighVertices G)
  have hhigh :
      ((G.neighborFinset y).filter fun x =>
        x ∈ orderFortyNineHighVertices G).card =
        sevenHighT0LowIndexSupportCard i := by
    rw [← sevenHighT0LowVertex_support_card
      G hfree hmin hHigh hzero e i]
    congr 1
  rw [hhigh] at hsplit
  rw [SimpleGraph.card_neighborFinset_eq_degree, hdegree] at hsplit
  omega

end


end Erdos85

#print axioms Erdos85.sevenHighT0LowVertex_support_card
#print axioms Erdos85.sevenHighT0LowVertex_degree_eq_seven
#print axioms Erdos85.sevenHighT0LowGraph_adj_iff
#print axioms Erdos85.sevenHighT0LowGraph_degree_add_supportCard_eq_seven
