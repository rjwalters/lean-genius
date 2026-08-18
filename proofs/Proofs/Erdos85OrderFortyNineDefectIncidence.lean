import Proofs.Erdos85OrderFortyNineIncidence
import Proofs.Erdos85NonregularDefectOperator
import Proofs.Erdos85AlternatingFourthMoment

/-!
# Defect incidence across the order-49 degree split

The exact nonregular adjacency--defect commutator becomes a sharp incidence
identity between the degree-eight and degree-seven sectors.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If `x` is high and `y` is low, precisely one neighbor of `x` is a defect
neighbor of `y` when `x,y` are nonadjacent, and none is when they are
adjacent.  In matrix language this is the entrywise form of
`B (D_low + I) = J`. -/
theorem orderFortyNine_card_highNeighbors_inter_defectNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x y : V}
    (hx : G.degree x = 8) (hy : G.degree y = 7) :
    (G.neighborFinset x ∩
        (secondOrderDefectGraph G).neighborFinset y).card =
      if G.Adj x y then 0 else 1 := by
  let D := secondOrderDefectGraph G
  have hxD : D.degree x = 0 :=
    (orderFortyNine_degreeEight_defectDegree_and_neighborExcess_zero
      G hfree hmin hcard hx).1
  have hxDempty : D.neighborFinset x = ∅ := by
    rw [← Finset.card_eq_zero, D.card_neighborFinset_eq_degree, hxD]
  have hcomm := adjMatrix_secondOrderDefect_commutator_apply G hfree x y
  rw [Matrix.sub_apply,
    adjMatrix_mul_subgraph_apply_eq_card_mixed G D x y,
    adjMatrix_mul_subgraph_apply_eq_card_mixed D G x y,
    hxDempty] at hcomm
  simp only [Finset.empty_inter, Finset.card_empty, Int.ofNat_zero, sub_zero,
    hx, hy, SimpleGraph.adjMatrix_apply] at hcomm
  by_cases hxy : G.Adj x y
  · rw [if_pos hxy]
    simp [hxy] at hcomm
    exact Finset.card_eq_zero.mpr hcomm
  · rw [if_neg hxy]
    simp [hxy] at hcomm
    omega

/-- Between the neighborhoods of two distinct high vertices there are
exactly seven ordered defect incidences.  This is the entrywise statement
`B D Bᵀ = 7 (J - I)`. -/
theorem orderFortyNine_sum_defectIncidence_between_highNeighborhoods
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x z : V}
    (hx : G.degree x = 8) (hz : G.degree z = 8) (hxz : x ≠ z) :
    (∑ y ∈ G.neighborFinset z,
      (G.neighborFinset x ∩
        (secondOrderDefectGraph G).neighborFinset y).card) = 7 := by
  calc
    (∑ y ∈ G.neighborFinset z,
      (G.neighborFinset x ∩
        (secondOrderDefectGraph G).neighborFinset y).card) =
        ∑ y ∈ G.neighborFinset z, if G.Adj x y then 0 else 1 := by
      apply Finset.sum_congr rfl
      intro y hyz
      have hzy : G.Adj z y := by
        simpa [SimpleGraph.mem_neighborFinset] using hyz
      have hy : G.degree y = 7 :=
        orderFortyNine_neighbor_degree_seven_of_degreeEight
          G hfree hmin hcard hz hzy
      exact orderFortyNine_card_highNeighbors_inter_defectNeighbors
        G hfree hmin hcard hx hy
    _ = (G.neighborFinset z \ G.neighborFinset x).card := by
      have hbool : ∀ y : V,
          (if G.Adj x y then 0 else 1) =
            (if ¬ G.Adj x y then 1 else 0) := by
        intro y
        by_cases hxy : G.Adj x y <;> simp [hxy]
      simp_rw [hbool]
      rw [Finset.sum_boole]
      apply congrArg Finset.card
      ext y
      simp [SimpleGraph.mem_neighborFinset]
    _ = 7 := by
      rw [Finset.card_sdiff, G.card_neighborFinset_eq_degree, hz]
      have hinter := orderFortyNine_card_common_degreeEight_eq_one
        G hfree hmin hcard hz hx hxz.symm
      rw [Finset.inter_comm, hinter]

end

end Erdos85
