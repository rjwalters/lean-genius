import Proofs.Erdos85OrderFortyNineSevenHighT0ExteriorPairCapacity
import Proofs.Erdos85OrderFortyNineSevenHighT0ExteriorPairLowerBound
import Proofs.Erdos85VertexSubsetEdgeCapacity

/-! Actual H7 vertex-subset inequality combining the exterior-pair edge
lower bound, degree capacities, and forbidden inside common neighbors.
The finite43-class enumeration is not used or certified here. -/
namespace Erdos85
open SimpleGraph
noncomputable section

/-- Allowed pairs: distinct vertices with no common neighbor inside E. -/
def insideCommonFreeGraph {V : Type*} (G : SimpleGraph V) (E : Finset V) :
    SimpleGraph (↑E : Set V) where
  Adj u v := u ≠ v ∧ ∀ w : (↑E : Set V), ¬ (G.Adj u.val w.val ∧ G.Adj v.val w.val)
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    intro w hw
    exact h.2 w ⟨hw.2,hw.1⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance insideCommonFreeGraph_adjDecidable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (E : Finset V) :
    DecidableRel (insideCommonFreeGraph G E).Adj := by
  classical
  intro u v
  change Decidable (u ≠ v ∧ ∀ w : (↑E : Set V), ¬ (G.Adj u.val w.val ∧ G.Adj v.val w.val))
  infer_instance

/-- Every subset of the actual empty-support fiber satisfies the exact
capacity inequality used by the induced-class obstructions. -/
theorem sevenHigh_t0_vertex_subset_exterior_capacity_inequality
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (U : Finset (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49))) :
    35 ≤ 4 * sevenHighT0InternalEdgeCount G 0 +
      (∑ v ∈ U, (7 - 2 * (G.neighborFinset v.val ∩ sevenHighT0LowSupportFiber G 0).card)) +
      ((insideCommonFreeGraph G (sevenHighT0LowSupportFiber G 0)).edgeFinset.filter
        (fun e => ∀ v ∈ U, v ∉ e)).card := by
  classical
  let E := sevenHighT0LowSupportFiber G 0
  let X := exteriorPairGraph G (↑E : Set (Fin 49))
  let F := insideCommonFreeGraph G E
  have hsub : X ≤ F := by
    intro u v huv
    refine ⟨huv.1, ?_⟩
    intro w hw
    exact exteriorPair_adj_no_inside_common G E hfree huv ⟨w.val,w.property,hw⟩
  have hcap : ∀ v ∈ U, X.degree v ≤ 7 - 2 * (G.neighborFinset v.val ∩ E).card := by
    intro v hv
    have h := sevenHigh_t0_exteriorPair_degree_add_two_empty_neighbors_le_seven
      G hfree hmin hHigh hzero v
    change X.degree v + 2 * (G.neighborFinset v.val ∩ E).card ≤ 7 at h
    omega
  have hupper := vertex_subset_edge_capacity_bound X F U
    (fun v => 7 - 2 * (G.neighborFinset v.val ∩ E).card) hsub hcap
  have hlower := sevenHigh_t0_exteriorPair_edges_add_four_empty_edges_ge_thirtyFive
    G hfree hmin hHigh hzero
  have h := hlower.trans (Nat.add_le_add_left hupper (4 * sevenHighT0InternalEdgeCount G 0))
  simpa only [Nat.add_assoc] using h

end
end Erdos85
#print axioms Erdos85.sevenHigh_t0_vertex_subset_exterior_capacity_inequality
