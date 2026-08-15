import Proofs.Erdos85OrderFortyNineSevenHighFiberLabeling

/-!
# Fiber census for the empty seven-high triple system

When `t=0`, every low high-support has size at most two.  Globally there are
seven empty, fourteen singleton, and twenty-one pair supports; locally at
each high point there are exactly two singleton and six pair supports.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

theorem sevenHigh_t0_global_incidence
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0) :
    orderFortyNineHighIncidenceCount G 0 = 7 ∧
    orderFortyNineHighIncidenceCount G 1 = 14 ∧
    orderFortyNineHighIncidenceCount G 2 = 21 := by
  have hp := orderFortyNine_highIncidence_profile_of_seven_high
    G hfree hmin (Fintype.card_fin 49) hHigh
  dsimp only at hp
  omega

theorem sevenHigh_t0_no_triple_neighbor
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    {v : Fin 49} (hv : v ∈ orderFortyNineHighVertices G) :
    ((G.neighborFinset v).filter fun x =>
      (orderFortyNineHighSupport G x).card = 3).card = 0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxN := (Finset.mem_filter.mp hx).1
  have hx3 := (Finset.mem_filter.mp hx).2
  have hxLow : x ∈ orderFortyNineLowVertices G := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ x, ?_⟩
    intro hxHigh
    have hx8 := (Finset.mem_filter.mp hxHigh).2
    have hv8 := (Finset.mem_filter.mp hv).2
    have hadj : G.Adj v x := by
      simpa [SimpleGraph.mem_neighborFinset] using hxN
    have hx7 := orderFortyNine_neighbor_degree_seven_of_degreeEight
      G hfree hmin (Fintype.card_fin 49) hv8 hadj
    omega
  have hxGlobal : x ∈ (orderFortyNineLowVertices G).filter fun y =>
      (G.neighborFinset y ∩ orderFortyNineHighVertices G).card = 3 := by
    apply Finset.mem_filter.mpr
    simpa [orderFortyNineHighSupport] using And.intro hxLow hx3
  have hempty : ((orderFortyNineLowVertices G).filter fun y =>
      (G.neighborFinset y ∩ orderFortyNineHighVertices G).card = 3) = ∅ := by
    apply Finset.card_eq_zero.mp
    exact hzero
  rw [hempty] at hxGlobal
  simp at hxGlobal

theorem sevenHigh_t0_local_incidence
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    {v : Fin 49} (hv : v ∈ orderFortyNineHighVertices G) :
    ((G.neighborFinset v).filter fun x =>
      (orderFortyNineHighSupport G x).card = 1).card = 2 ∧
    ((G.neighborFinset v).filter fun x =>
      (orderFortyNineHighSupport G x).card = 2).card = 6 := by
  have hv8 : G.degree v = 8 := (Finset.mem_filter.mp hv).2
  have hp := orderFortyNine_highNeighborhood_profile_of_seven_high
    G hfree hmin (Fintype.card_fin 49) hHigh hv8
  dsimp only at hp
  have h3 := sevenHigh_t0_no_triple_neighbor G hfree hmin hzero hv
  omega

end

end Erdos85
