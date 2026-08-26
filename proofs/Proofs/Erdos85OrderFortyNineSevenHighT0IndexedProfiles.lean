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

end


end Erdos85

#print axioms Erdos85.sevenHighT0LowVertex_support_card
#print axioms Erdos85.sevenHighT0LowVertex_degree_eq_seven
#print axioms Erdos85.sevenHighT0LowGraph_adj_iff
