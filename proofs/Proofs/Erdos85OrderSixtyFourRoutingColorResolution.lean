import Proofs.Erdos85OrderSixtyFourRoutingColorFactors

/-! # Algebraic resolution by routing-color factors -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Complete bipartite graph between two endpoint component supports. -/
def endpointCompleteBipartiteGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c e : (secondOrderDefectGraph G).ConnectedComponent) :
    SimpleGraph (c.supp ⊕ e.supp) where
  Adj u v := match u, v with
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | _, _ => False
  symm := by
    constructor
    intro u v
    cases u <;> cases v <;> simp_all
  loopless := by
    constructor
    intro u
    cases u <;> simp

noncomputable instance endpointCompleteBipartiteGraph.instDecidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c e : (secondOrderDefectGraph G).ConnectedComponent) :
    DecidableRel (endpointCompleteBipartiteGraph G c e).Adj :=
  Classical.decRel _

/-- Pointwise, the routing-color adjacency matrices resolve the complete
endpoint bipartite adjacency matrix. -/
theorem sum_routingColorBipartiteGraph_adjMatrix_apply_eq_complete
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    (u v : c.supp ⊕ e.supp) :
    (∑ d : (secondOrderDefectGraph G).ConnectedComponent,
      (routingColorBipartiteGraph G hfree c e hce d).adjMatrix ℤ u v) =
        (endpointCompleteBipartiteGraph G c e).adjMatrix ℤ u v := by
  cases u with
  | inl x =>
      cases v with
      | inl y =>
          simp [routingColorBipartiteGraph, endpointCompleteBipartiteGraph,
            SimpleGraph.adjMatrix_apply]
      | inr z =>
          simp only [SimpleGraph.adjMatrix_apply]
          rw [if_pos (by simp [endpointCompleteBipartiteGraph])]
          rw [Finset.sum_boole]
          have heq : (Finset.univ.filter fun d :
              (secondOrderDefectGraph G).ConnectedComponent =>
                (routingColorBipartiteGraph G hfree c e hce d).Adj
                  (Sum.inl x) (Sum.inr z)) =
              {crossIntermediateComponent G hfree hce x z} := by
            ext d
            simp [routingColorBipartiteGraph]
          rw [heq]
          simp
  | inr z =>
      cases v with
      | inl x =>
          simp only [SimpleGraph.adjMatrix_apply]
          rw [if_pos (by simp [endpointCompleteBipartiteGraph])]
          rw [Finset.sum_boole]
          have heq : (Finset.univ.filter fun d :
              (secondOrderDefectGraph G).ConnectedComponent =>
                (routingColorBipartiteGraph G hfree c e hce d).Adj
                  (Sum.inr z) (Sum.inl x)) =
              {crossIntermediateComponent G hfree hce x z} := by
            ext d
            simp [routingColorBipartiteGraph]
          rw [heq]
          simp
      | inr w =>
          simp [routingColorBipartiteGraph, endpointCompleteBipartiteGraph,
            SimpleGraph.adjMatrix_apply]

/-- Distinct routing-color matrices have disjoint support entrywise. -/
theorem routingColorBipartiteGraph_adjMatrix_mul_apply_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    {d₁ d₂ : (secondOrderDefectGraph G).ConnectedComponent} (hdd : d₁ ≠ d₂)
    (u v : c.supp ⊕ e.supp) :
    (routingColorBipartiteGraph G hfree c e hce d₁).adjMatrix ℤ u v *
      (routingColorBipartiteGraph G hfree c e hce d₂).adjMatrix ℤ u v = 0 := by
  cases u <;> cases v <;>
    simp only [SimpleGraph.adjMatrix_apply, routingColorBipartiteGraph]
  · simp
  · split <;> split <;> simp_all
  · split <;> split <;> simp_all
  · simp

end

end Erdos85
