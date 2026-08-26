import Proofs.Erdos85OrderFortyNineSevenHighT0GlobalQuotientBridge

/-!
# Parity of the directed empty-fiber parameter

Self-incidences count each induced edge twice.  This file connects the
directed graph parameter `D = I₀₀` to the undirected empty-fiber edge count
`F`, recovering the five-value range `6 ≤ F ≤ 10`.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

def sevenHighT0InternalEdgeCount
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] (k : Nat) : Nat :=
  (G.induce (↑(sevenHighT0LowSupportFiber G k) : Set (Fin 49))).edgeFinset.card

private theorem sum_card_neighbor_inter_self_eq_twice_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (∑ y ∈ S, (G.neighborFinset y ∩ S).card) =
      2 * (G.induce (↑S : Set V)).edgeFinset.card := by
  classical
  let H := G.induce (↑S : Set V)
  have hhand := H.sum_degrees_eq_twice_card_edges
  calc
    (∑ y ∈ S, (G.neighborFinset y ∩ S).card) =
        ∑ y : {x : V // x ∈ (↑S : Set V)}, H.degree y := by
      rw [Finset.sum_subtype S (fun _ => Iff.rfl)]
      apply Finset.sum_congr rfl
      intro y _
      rw [← H.card_neighborFinset_eq_degree]
      apply Finset.card_bij (fun x hx =>
        ⟨x, (Finset.mem_inter.mp hx).2⟩)
      · intro x hx
        have hxAdj := (Finset.mem_inter.mp hx).1
        simpa [H, SimpleGraph.mem_neighborFinset] using hxAdj
      · intro x hx z hz hxz
        exact congrArg Subtype.val hxz
      · intro z hz
        refine ⟨z.1, ?_, ?_⟩
        · apply Finset.mem_inter.mpr
          refine ⟨?_, z.2⟩
          simpa [H, SimpleGraph.mem_neighborFinset] using hz
        · exact Subtype.ext rfl
    _ = _ := hhand

/-- Directed self-incidence on a support fiber is twice its induced edge
count. -/
theorem sevenHighT0DirectedIncidence_self_eq_twice_internalEdges
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] (k : Nat) :
    sevenHighT0DirectedIncidence G k k =
      2 * sevenHighT0InternalEdgeCount G k := by
  classical
  rw [sevenHighT0DirectedIncidence, sevenHighT0InternalEdgeCount]
  calc
    (∑ y ∈ sevenHighT0LowSupportFiber G k,
        ((G.neighborFinset y).filter fun x =>
          x ∈ sevenHighT0LowSupportFiber G k).card) =
        ∑ y ∈ sevenHighT0LowSupportFiber G k,
          (G.neighborFinset y ∩ sevenHighT0LowSupportFiber G k).card := by
      apply Finset.sum_congr rfl
      intro y _
      apply congrArg Finset.card
      ext x
      simp
    _ = _ := sum_card_neighbor_inter_self_eq_twice_edges
      G (sevenHighT0LowSupportFiber G k)

/-- The undirected empty-fiber parameter has exactly the classical range
`6 ≤ F ≤ 10`; equivalently `D = 2F` lies between 11 and 21. -/
theorem sevenHigh_t0_internalEmptyEdge_parameter_bounds
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0) :
    6 ≤ sevenHighT0InternalEdgeCount G 0 ∧
      sevenHighT0InternalEdgeCount G 0 ≤ 10 := by
  have hparam := sevenHigh_t0_directed_quotient_one_parameter
    G hfree hmin hHigh hzero
  have htwice := sevenHighT0DirectedIncidence_self_eq_twice_internalEdges G 0
  dsimp only at hparam
  omega

end


end Erdos85

#print axioms Erdos85.sevenHighT0DirectedIncidence_self_eq_twice_internalEdges
#print axioms Erdos85.sevenHigh_t0_internalEmptyEdge_parameter_bounds
