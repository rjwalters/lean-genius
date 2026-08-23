import Proofs.Erdos85OddSquareOrderNineOrder34FourEdgePlacement

/-! # Corrected order-34 punctured profile dispatcher

This file dispatches the four honest local alternatives after the
owner-punctured transfer: three or four local edges, and owner-W degree one
or two.  All exceptional degrees use the corrected `1/2` shore formula.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The four corrected local terminals, assembled behind the two profile
dichotomies. -/
theorem false_of_orderNine_order34_local_profile_of_corrected_punctured_data
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    (h₁ h₂ h₃ owner : V)
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (S T Z P W : Finset V)
    (hSsub : S ⊆ (Finset.univ : Finset V) \
      squareOrderHighVertices G 9)
    (hdisj : Disjoint S T)
    (hownerS : (G.neighborFinset owner ∩ S).card = 3)
    (hpartnersSub : G.neighborFinset owner ∩
      squareOrderNineLowIncidenceBin G 1 ⊆ S ∪ T)
    (hfull : orderNineArticulationSmallShoreFullType G
      ((secondOrderDefectGraph G).neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0) h₁ h₂ h₃ S)
    (hScard : S.card = 34)
    (hpartition : Z = insert owner (P ∪ W))
    (hPsub : P ⊆ squareOrderNineLowIncidenceBin G 1)
    (hWsub : W ⊆ squareOrderNineLowIncidenceBin G 0)
    (hWcard : W.card = 2)
    (hlocAlt : (G.induce (G.neighborSet owner)).edgeFinset.card = 3 ∨
      (G.induce (G.neighborSet owner)).edgeFinset.card = 4)
    (hownerWAlt : (G.neighborFinset owner ∩ W).card = 2 ∨
      (G.neighborFinset owner ∩ W).card = 1)
    (hExceptionalDegree : ∀ e ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0 ∩
        (secondOrderDefectGraph G).neighborFinset owner),
      (G.neighborFinset e ∩ Z).card = if e ∈ S then 1 else 2)
    (hRegularDegree : ∀ r ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0) \
        (secondOrderDefectGraph G).neighborFinset owner,
      (G.neighborFinset r ∩ Z).card = 2)
    (hPartnerDegree : ∀ z ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1),
      (G.neighborFinset z ∩ W).card = if z ∈ S then 0 else 1) : False := by
  have hTotalDefectS :
      (((secondOrderDefectGraph G).neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0) ∩ S).card = 2 :=
    hfull.2.2.2 hScard
  have hownerSPartition :=
    orderNine_secondProfile_owner_neighbor_inter_ordinary_shore_bin_partition
      G hp hhigh hc2 hc3 howner S hSsub
  have hcensus :=
    squareOrderNine_threeHigh_secondProfile_binThree_original_neighborhood_census
      G hfree hmin hcard hp hhigh hc2 hc3 hc4 howner
  have hpartnerCard : (G.neighborFinset owner ∩
      squareOrderNineLowIncidenceBin G 1).card = 3 := by
    simpa using hcensus.2.1
  rcases hlocAlt with hthree | hfour
  · rcases hownerWAlt with htwo | hone
    · exact false_of_orderNine_order34_three_edge_owner_W_two_punctured
        G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner hthree
          S Z P W hpartition hPsub hWcard htwo hTotalDefectS
          hExceptionalDegree
    · exact false_of_orderNine_order34_three_edge_owner_W_one_punctured
        G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner hthree
          S T Z P W hSsub hdisj hownerS hpartnersSub
          hpartition hPsub hWsub hWcard hone hTotalDefectS
          hExceptionalDegree
          (fun z hz ↦ by
            have h := hPartnerDegree z (Finset.mem_inter.mp hz).1
            have hzNotS : z ∉ S := by
              intro hzS
              exact (Finset.disjoint_left.mp hdisj) hzS
                (Finset.mem_inter.mp hz).2
            simpa [hzNotS] using h)
  · rcases hownerWAlt with htwo | hone
    · exact false_of_orderNine_order34_four_edge_owner_W_two_punctured
        G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner hfour
          S Z P W hpartition hPsub hWsub hWcard htwo hownerS
          hpartnerCard hPartnerDegree hRegularDegree hExceptionalDegree
    · exact false_of_orderNine_order34_four_edge_owner_W_one_punctured
        G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner hfour
          S T Z P W hdisj hownerS hownerSPartition hpartnersSub
          hpartition hPsub hWsub hWcard hone
          hExceptionalDegree hRegularDegree
          (fun z hz ↦ by
            have h := hPartnerDegree z (Finset.mem_inter.mp hz).1
            have hzNotS : z ∉ S := by
              intro hzS
              exact (Finset.disjoint_left.mp hdisj) hzS
                (Finset.mem_inter.mp hz).2
            simpa [hzNotS] using h)

/-- Graph-facing corrected order-34 capstone.  Actual owner-punctured
articulation data supplies every degree law consumed by the local profile
dispatcher. -/
theorem false_of_orderNine_order34_local_profile_of_punctured_articulation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    (h₁ h₂ h₃ owner : V)
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (U S T : Finset V)
    (hownerNotU : owner ∉ U)
    (hunion : S ∪ T = U) (hdisj : Disjoint S T)
    (hSsub : S ⊆ (Finset.univ : Finset V) \
      squareOrderHighVertices G 9)
    (hownerS : (G.neighborFinset owner ∩ S).card = 3)
    (hpartnersSub : G.neighborFinset owner ∩
      squareOrderNineLowIncidenceBin G 1 ⊆ S ∪ T)
    (hneighborsPunctured : ∀ x ∈ U,
      (secondOrderDefectGraph G).neighborFinset x ⊆ insert owner U)
    (hSclosed : ∀ x ∈ S,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ S)
    (hTclosed : ∀ x ∈ T,
      (secondOrderDefectGraph G).neighborFinset x ∩ U ⊆ T)
    (hlocalU : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0), y ∈ U)
    (hpartnerU : ∀ z ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1), z ∈ U)
    (hScard : S.card = 34)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ S 3 60)
    (hhigh₁ : (G.neighborFinset h₁ ∩ S).card = 4)
    (hhigh₂ : (G.neighborFinset h₂ ∩ S).card = 4)
    (hhigh₃ : (G.neighborFinset h₃ ∩ S).card = 4)
    (hSH : Disjoint S {h₁, h₂, h₃})
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ x ∈ ({h₁, h₂, h₃} : Finset V), G.degree x = 10)
    (hlocalOrd : ∀ y ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0),
      y ∉ ({h₁, h₂, h₃} : Finset V))
    (hpartnerOrd : ∀ z ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1),
      z ∉ ({h₁, h₂, h₃} : Finset V))
    (hfull : orderNineArticulationSmallShoreFullType G
      ((secondOrderDefectGraph G).neighborFinset owner ∩
        squareOrderNineLowIncidenceBin G 0) h₁ h₂ h₃ S)
    (Z P W : Finset V)
    (hZ : Z = orderNineOrdinaryLowSet G h₁ h₂ h₃ S 3)
    (hpartition : Z = insert owner (P ∪ W))
    (hPsub : P ⊆ squareOrderNineLowIncidenceBin G 1)
    (hWsub : W ⊆ squareOrderNineLowIncidenceBin G 0)
    (hWcard : W.card = 2)
    (hlocAlt : (G.induce (G.neighborSet owner)).edgeFinset.card = 3 ∨
      (G.induce (G.neighborSet owner)).edgeFinset.card = 4)
    (hownerWAlt : (G.neighborFinset owner ∩ W).card = 2 ∨
      (G.neighborFinset owner ∩ W).card = 1) : False := by
  have hExceptionalDegree :=
    orderNine_order34_exceptional_owner_neighbors_lowSet_degree_eq_if_of_punctured_shores
      G hfree hmin hcover hcard h₁ h₂ h₃ owner U S T
        hownerNotU hunion hdisj hneighborsPunctured hSclosed hTclosed
        (fun y hy ↦ hlocalU y (Finset.mem_inter.mp hy).1)
        hScard hpart hhigh₁ hhigh₂ hhigh₃ hSH hdegOrd hdegHigh
        (fun y hy ↦ hlocalOrd y (Finset.mem_inter.mp hy).1) Z hZ
  have hRegularDegree :=
    orderNine_order34_regular_owner_neighbors_lowSet_degree_two_of_punctured_shores
      G hfree hmin hcover hcard h₁ h₂ h₃ owner U S T
        hunion hdisj hneighborsPunctured hSclosed hTclosed hlocalU
        hScard hpart hhigh₁ hhigh₂ hhigh₃ hSH hdegOrd hdegHigh
        hlocalOrd Z hZ
  have hpartnerDclosed : ∀ z ∈
      (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 1),
      (secondOrderDefectGraph G).neighborFinset z ⊆ U := by
    intro z hz
    exact orderNine_secondProfile_owner_partner_defectNeighbors_subset_punctured
      G hfree hhigh howner (Finset.mem_inter.mp hz).2 U
        (hneighborsPunctured z (hpartnerU z hz))
  have hPartnerDegree :=
    orderNine_order34_owner_partners_W_degree_eq_if_of_pointwise_closure
      G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4
        h₁ h₂ h₃ owner howner U S T hScard hpart
        hhigh₁ hhigh₂ hhigh₃ hSH hdegOrd hdegHigh
        hunion hdisj hpartnerU hpartnerDclosed hSclosed hTclosed
        hpartnerOrd Z P W hZ hpartition hPsub hWsub
  exact false_of_orderNine_order34_local_profile_of_corrected_punctured_data
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4
      h₁ h₂ h₃ owner howner S T Z P W hSsub hdisj hownerS
      hpartnersSub hfull hScard hpartition hPsub hWsub hWcard
      hlocAlt hownerWAlt hExceptionalDegree hRegularDegree hPartnerDegree

#print axioms false_of_orderNine_order34_local_profile_of_corrected_punctured_data
#print axioms false_of_orderNine_order34_local_profile_of_punctured_articulation

end

end Erdos85
