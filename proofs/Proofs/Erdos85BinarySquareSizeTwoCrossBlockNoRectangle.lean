import Proofs.Erdos85BinarySquareSizeTwoOwnerFactorization

/-! # Cross blocks contain no rectangles -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Two distinct rows of any cross-component adjacency block share at most
one target neighbor.  This is the direct `K₂,₂`/four-cycle exclusion on the
subtype-valued cross block. -/
theorem card_crossNeighborFinset_inter_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {source : (secondOrderDefectGraph G).ConnectedComponent}
    (target : (secondOrderDefectGraph G).ConnectedComponent)
    (x y : source.supp) (hxy : x ≠ y) :
    ((componentCrossNeighborFinset G target x) ∩
      componentCrossNeighborFinset G target y).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have hxyVal : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
  have hcommon := common_le_one_of_not_containsC4 hfree x.1 y.1 hxyVal
  have haData := Finset.mem_inter.mp ha
  have hbData := Finset.mem_inter.mp hb
  have haCommon : a.1 ∈ G.neighborFinset x.1 ∩ G.neighborFinset y.1 := by
    apply Finset.mem_inter.mpr
    constructor
    · exact (G.mem_neighborFinset x.1 a.1).mpr
        (Finset.mem_filter.mp haData.1).2
    · exact (G.mem_neighborFinset y.1 a.1).mpr
        (Finset.mem_filter.mp haData.2).2
  have hbCommon : b.1 ∈ G.neighborFinset x.1 ∩ G.neighborFinset y.1 := by
    apply Finset.mem_inter.mpr
    constructor
    · exact (G.mem_neighborFinset x.1 b.1).mpr
        (Finset.mem_filter.mp hbData.1).2
    · exact (G.mem_neighborFinset y.1 b.1).mpr
        (Finset.mem_filter.mp hbData.2).2
  exact Subtype.ext (Finset.card_le_one.mp hcommon a.1 haCommon b.1 hbCommon)

/-- The restricted target-owner factor is exactly the common-neighbor graph
of the corresponding cross block. -/
theorem restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (x y : source.supp) :
    (restrictedComponentOwnerGraph G source target).Adj x y ↔
      x ≠ y ∧
        ((componentCrossNeighborFinset G target x) ∩
          componentCrossNeighborFinset G target y).Nonempty := by
  constructor
  · intro hxy
    have howner :
        (componentOwnerGraph G (secondOrderDefectGraph G) target).Adj x.1 y.1 :=
      hxy
    have hdata := (componentOwnerGraph_adj
      G (secondOrderDefectGraph G) target x.1 y.1).mp howner
    obtain ⟨z, hz⟩ := hdata.2
    have hzData := Finset.mem_inter.mp hz
    have hzTarget : z ∈ target.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff target z).mpr
        (Finset.mem_filter.mp hzData.1).2
    refine ⟨hxy.ne, ⟨⟨z, hzTarget⟩, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩⟩
    · rw [componentCrossNeighborFinset, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (G.mem_neighborFinset x.1 z).mp
        (Finset.mem_filter.mp hzData.1).1⟩
    · rw [componentCrossNeighborFinset, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (G.mem_neighborFinset y.1 z).mp
        (Finset.mem_filter.mp hzData.2).1⟩
  · rintro ⟨hxy, z, hz⟩
    have hzData := Finset.mem_inter.mp hz
    change (componentOwnerGraph G (secondOrderDefectGraph G) target).Adj x.1 y.1
    rw [componentOwnerGraph_adj]
    refine ⟨fun h => hxy (Subtype.ext h), ⟨z.1, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩⟩
    · rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset x.1 z.1).mpr
          (Finset.mem_filter.mp hzData.1).2,
        (SimpleGraph.ConnectedComponent.mem_supp_iff target z.1).mp z.2⟩
    · rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset y.1 z.1).mpr
          (Finset.mem_filter.mp hzData.2).2,
        (SimpleGraph.ConnectedComponent.mem_supp_iff target z.1).mp z.2⟩

/-- In a size-two target block, adjacent rows of the restricted owner factor
share exactly one target point, and nonadjacent distinct rows share none. -/
theorem binarySquare_regular_sizeTwoTarget_crossRow_inter_card_eq_ite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {source : (secondOrderDefectGraph G).ConnectedComponent}
    (target : (secondOrderDefectGraph G).ConnectedComponent)
    (x y : source.supp) (hxy : x ≠ y) :
    ((componentCrossNeighborFinset G target x) ∩
      componentCrossNeighborFinset G target y).card =
        if (restrictedComponentOwnerGraph G source target).Adj x y then 1 else 0 := by
  have hle := card_crossNeighborFinset_inter_le_one G hfree target x y hxy
  by_cases hadj : (restrictedComponentOwnerGraph G source target).Adj x y
  · rw [if_pos hadj]
    have hnon := (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
      G source target x y).mp hadj |>.2
    have hpos : 0 < ((componentCrossNeighborFinset G target x) ∩
      componentCrossNeighborFinset G target y).card := Finset.card_pos.mpr hnon
    omega
  · rw [if_neg hadj]
    have hempty : ¬((componentCrossNeighborFinset G target x) ∩
      componentCrossNeighborFinset G target y).Nonempty := by
      intro hnon
      exact hadj ((restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
        G source target x y).mpr ⟨hxy, hnon⟩)
    exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hempty)

end

end Erdos85
