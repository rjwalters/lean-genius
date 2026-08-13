import Proofs.Erdos85OrderFortyNineDefectEigenvectors

/-!
# Perfect codes in the order-49 low defect graph

Every high neighborhood is an efficient dominating set of the low-sector
second-order defect graph.  This is a combinatorial form of `B (D + I) = J`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The closed defect neighborhood of every low vertex meets every high
neighborhood in exactly one vertex. -/
theorem orderFortyNine_closedDefectNeighborhood_inter_highNeighborhood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v x : V}
    (hv : G.degree v = 8) (hx : G.degree x = 7) :
    (insert x ((secondOrderDefectGraph G).neighborFinset x) ∩
        G.neighborFinset v).card = 1 := by
  have hcount := orderFortyNine_card_highNeighbors_inter_defectNeighbors
    G hfree hmin hcard hv hx
  rw [Finset.inter_comm] at hcount
  by_cases hvx : G.Adj v x
  · rw [if_pos hvx] at hcount
    have hempty : (secondOrderDefectGraph G).neighborFinset x ∩
        G.neighborFinset v = ∅ := Finset.card_eq_zero.mp hcount
    simp [Finset.insert_inter, SimpleGraph.mem_neighborFinset, hvx, hempty]
  · rw [if_neg hvx] at hcount
    simpa [Finset.insert_inter, SimpleGraph.mem_neighborFinset, hvx] using hcount

/-- A defect edge cannot join two low vertices having a common high
neighbor.  Equivalently, incidence blocks at the ends of a defect edge are
disjoint. -/
theorem orderFortyNine_no_common_highNeighbor_of_defectAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v x y : V}
    (hv : G.degree v = 8) (hx : G.degree x = 7)
    (hDxy : (secondOrderDefectGraph G).Adj x y) :
    ¬ (G.Adj v x ∧ G.Adj v y) := by
  rintro ⟨hvx, hvy⟩
  have hcount := orderFortyNine_card_highNeighbors_inter_defectNeighbors
    G hfree hmin hcard hv hx
  rw [if_pos hvx, Finset.card_eq_zero] at hcount
  have hy : y ∈ G.neighborFinset v ∩
      (secondOrderDefectGraph G).neighborFinset x := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hvy, hDxy⟩
  rw [hcount] at hy
  exact Finset.notMem_empty y hy

/-- Global perfect-code form of the preceding pointwise count.  Fixing a
degree-eight vertex `v`, every low vertex belongs to the closed defect
neighborhood of a unique neighbor of `v`.  These unique owners are the
partition map used in the unresolved small-high order-49 strata. -/
theorem orderFortyNine_existsUnique_highNeighbor_closedDefectOwner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v y : V}
    (hv : G.degree v = 8) (hy : G.degree y = 7) :
    ∃! x : V, x ∈ G.neighborFinset v ∧
      y ∈ insert x ((secondOrderDefectGraph G).neighborFinset x) := by
  have hcardOne :=
    orderFortyNine_closedDefectNeighborhood_inter_highNeighborhood
      G hfree hmin hcard hv hy
  rcases Finset.card_eq_one.mp hcardOne with ⟨x, hx⟩
  have hxmem : x ∈ insert y
      ((secondOrderDefectGraph G).neighborFinset y) ∩
        G.neighborFinset v := by
    simp [hx]
  refine ⟨x, ?_, ?_⟩
  · have hxparts := Finset.mem_inter.mp hxmem
    refine ⟨hxparts.2, ?_⟩
    rcases Finset.mem_insert.mp hxparts.1 with hxy | hD
    · exact Finset.mem_insert.mpr (Or.inl hxy.symm)
    · exact Finset.mem_insert.mpr (Or.inr (by
        simpa [SimpleGraph.mem_neighborFinset,
          (secondOrderDefectGraph G).adj_comm] using hD))
  · intro z hz
    have hzmem : z ∈ insert y
        ((secondOrderDefectGraph G).neighborFinset y) ∩
          G.neighborFinset v := by
      apply Finset.mem_inter.mpr
      refine ⟨?_, hz.1⟩
      rcases Finset.mem_insert.mp hz.2 with hyz | hD
      · exact Finset.mem_insert.mpr (Or.inl hyz.symm)
      · exact Finset.mem_insert.mpr (Or.inr (by
          simpa [SimpleGraph.mem_neighborFinset,
            (secondOrderDefectGraph G).adj_comm] using hD))
    simpa [hx] using hzmem

/-- Distinct code vertices have disjoint closed defect neighborhoods. -/
theorem orderFortyNine_closedDefectNeighborhood_pairwiseDisjoint_at_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8) :
    (G.neighborFinset v : Set V).PairwiseDisjoint
      (fun x => (insert x
        ((secondOrderDefectGraph G).neighborFinset x) : Finset V)) := by
  intro x hx z hz hxz
  change Disjoint
    (insert x ((secondOrderDefectGraph G).neighborFinset x))
    (insert z ((secondOrderDefectGraph G).neighborFinset z))
  rw [Finset.disjoint_left]
  intro y hyx hyz
  have hxAdj : G.Adj v x := by
    simpa [SimpleGraph.mem_neighborFinset] using hx
  have hxdeg : G.degree x = 7 :=
    orderFortyNine_neighbor_degree_seven_of_degreeEight
      G hfree hmin hcard hv hxAdj
  have hydeg : G.degree y = 7 := by
    rcases Finset.mem_insert.mp hyx with rfl | hD
    · exact hxdeg
    · rcases orderFortyNine_degree_eq_seven_or_eight
        G hfree hmin hcard y with hy7 | hy8
      · exact hy7
      · have hyDzero :=
          (orderFortyNine_degreeEight_defectDegree_and_neighborExcess_zero
            G hfree hmin hcard hy8).1
        have hDAdj : (secondOrderDefectGraph G).Adj y x := by
          simpa [SimpleGraph.mem_neighborFinset,
            (secondOrderDefectGraph G).adj_comm] using hD
        have hpos : 0 < (secondOrderDefectGraph G).degree y := by
          rw [← (secondOrderDefectGraph G).card_neighborFinset_eq_degree]
          exact Finset.card_pos.mpr
            ⟨x, ((secondOrderDefectGraph G).mem_neighborFinset y x).mpr hDAdj⟩
        omega
  obtain ⟨owner, howner, hunique⟩ :=
    orderFortyNine_existsUnique_highNeighbor_closedDefectOwner
      G hfree hmin hcard hv hydeg
  have hxeq : x = owner := hunique x ⟨hx, hyx⟩
  have hzeq : z = owner := hunique z ⟨hz, hyz⟩
  exact hxz (hxeq.trans hzeq.symm)

/-- The closed defect cells centered at the neighbors of a high vertex cover
the entire low sector.  Together with pairwise disjointness, this is the
global perfect-code partition identity. -/
theorem orderFortyNine_biUnion_closedDefectNeighborhood_eq_lowVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8) :
    (G.neighborFinset v).biUnion (fun x =>
      insert x ((secondOrderDefectGraph G).neighborFinset x)) =
        Finset.univ \ orderFortyNineHighVertices G := by
  ext y
  constructor
  · intro hy
    rw [Finset.mem_biUnion] at hy
    obtain ⟨x, hx, hyx⟩ := hy
    have hvx : G.Adj v x := by
      simpa [SimpleGraph.mem_neighborFinset] using hx
    have hxdeg : G.degree x = 7 :=
      orderFortyNine_neighbor_degree_seven_of_degreeEight
        G hfree hmin hcard hv hvx
    have hydeg : G.degree y = 7 := by
      rcases Finset.mem_insert.mp hyx with rfl | hD
      · exact hxdeg
      · rcases orderFortyNine_degree_eq_seven_or_eight
          G hfree hmin hcard y with hy7 | hy8
        · exact hy7
        · have hyDzero :=
            (orderFortyNine_degreeEight_defectDegree_and_neighborExcess_zero
              G hfree hmin hcard hy8).1
          have hDAdj : (secondOrderDefectGraph G).Adj y x := by
            simpa [SimpleGraph.mem_neighborFinset,
              (secondOrderDefectGraph G).adj_comm] using hD
          have hpos : 0 < (secondOrderDefectGraph G).degree y := by
            rw [← (secondOrderDefectGraph G).card_neighborFinset_eq_degree]
            exact Finset.card_pos.mpr
              ⟨x, ((secondOrderDefectGraph G).mem_neighborFinset y x).mpr hDAdj⟩
          omega
    rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ y, by
      simp [orderFortyNineHighVertices, hydeg]⟩
  · intro hy
    have hynot : y ∉ orderFortyNineHighVertices G :=
      (Finset.mem_sdiff.mp hy).2
    have hydeg : G.degree y = 7 := by
      rcases orderFortyNine_degree_eq_seven_or_eight
          G hfree hmin hcard y with hy7 | hy8
      · exact hy7
      · exact (hynot (by simp [orderFortyNineHighVertices, hy8])).elim
    obtain ⟨x, hx, _⟩ :=
      orderFortyNine_existsUnique_highNeighbor_closedDefectOwner
        G hfree hmin hcard hv hydeg
    rw [Finset.mem_biUnion]
    exact ⟨x, hx.1, hx.2⟩

/-- In the one-high stratum every cell of the defect perfect code has six
vertices: its low center and its five defect neighbors. -/
theorem orderFortyNine_card_closedDefectNeighborhood_eq_six_of_one_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v x : V} (hv : G.degree v = 8) (hx : x ∈ G.neighborFinset v) :
    (insert x ((secondOrderDefectGraph G).neighborFinset x)).card = 6 := by
  have hvx : G.Adj v x := by
    simpa [SimpleGraph.mem_neighborFinset] using hx
  have hxdeg : G.degree x = 7 :=
    orderFortyNine_neighbor_degree_seven_of_degreeEight
      G hfree hmin hcard hv hvx
  have hvHigh : v ∈ orderFortyNineHighVertices G := by
    simp [orderFortyNineHighVertices, hv]
  have hvMem : v ∈ G.neighborFinset x ∩ orderFortyNineHighVertices G := by
    simp [SimpleGraph.mem_neighborFinset, hvx.symm, hvHigh]
  have hkpos : 1 ≤
      (G.neighborFinset x ∩ orderFortyNineHighVertices G).card :=
    Finset.one_le_card.mpr ⟨v, hvMem⟩
  have hkle :
      (G.neighborFinset x ∩ orderFortyNineHighVertices G).card ≤ 1 := by
    rw [← hHigh]
    exact Finset.card_le_card Finset.inter_subset_right
  have hk :
      (G.neighborFinset x ∩ orderFortyNineHighVertices G).card = 1 := by
    omega
  have hexcess : neighborDegreeExcess G 7 x =
      (G.neighborFinset x ∩ orderFortyNineHighVertices G).card := by
    rw [neighborDegreeExcess_eq_sum_neighborFinset]
    calc
      (∑ y ∈ G.neighborFinset x, (G.degree y - 7)) =
          ∑ y ∈ G.neighborFinset x,
            if G.degree y = 8 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro y _hy
        rcases orderFortyNine_degree_eq_seven_or_eight
            G hfree hmin hcard y with hy7 | hy8
        · simp [hy7]
        · simp [hy8]
      _ = ((G.neighborFinset x).filter fun y => G.degree y = 8).card := by
        rw [Finset.card_filter]
      _ = (G.neighborFinset x ∩ orderFortyNineHighVertices G).card := by
        congr 1
        ext y
        simp [orderFortyNineHighVertices, and_comm]
  have hbudget := orderFortyNine_degreeSeven_local_budget
    G hfree hmin hcard hxdeg
  rw [hexcess, hk] at hbudget
  rw [Finset.card_insert_of_notMem]
  · rw [(secondOrderDefectGraph G).card_neighborFinset_eq_degree]
    omega
  · simp

/-- In the one-high stratum, every low vertex outside the high vertex's
neighborhood has no high neighbor and hence defect degree six. -/
theorem orderFortyNine_defectDegree_eq_six_of_one_high_of_not_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v y : V} (hv : G.degree v = 8) (hy : G.degree y = 7)
    (hvy : ¬ G.Adj v y) :
    (secondOrderDefectGraph G).degree y = 6 := by
  have hvHigh : v ∈ orderFortyNineHighVertices G := by
    simp [orderFortyNineHighVertices, hv]
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hHigh
  have hvw : v = w := by
    simpa [hw] using hvHigh
  have hHighEq : orderFortyNineHighVertices G = {v} := by
    simpa [hvw] using hw
  have hk :
      (G.neighborFinset y ∩ orderFortyNineHighVertices G).card = 0 := by
    rw [hHighEq]
    simp [SimpleGraph.mem_neighborFinset, G.adj_comm, hvy]
  have hexcess : neighborDegreeExcess G 7 y =
      (G.neighborFinset y ∩ orderFortyNineHighVertices G).card := by
    rw [neighborDegreeExcess_eq_sum_neighborFinset]
    calc
      (∑ z ∈ G.neighborFinset y, (G.degree z - 7)) =
          ∑ z ∈ G.neighborFinset y,
            if G.degree z = 8 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro z _hz
        rcases orderFortyNine_degree_eq_seven_or_eight
            G hfree hmin hcard z with hz7 | hz8
        · simp [hz7]
        · simp [hz8]
      _ = ((G.neighborFinset y).filter fun z => G.degree z = 8).card := by
        rw [Finset.card_filter]
      _ = (G.neighborFinset y ∩ orderFortyNineHighVertices G).card := by
        congr 1
        ext z
        simp [orderFortyNineHighVertices, and_comm]
  have hbudget := orderFortyNine_degreeSeven_local_budget
    G hfree hmin hcard hy
  rw [hexcess, hk] at hbudget
  omega

/-- Every noncenter low vertex has exactly one defect neighbor among the
eight centers `N_G(v)`.  Removing that owner edge leaves five defect edges
inside the forty-vertex leaf layer. -/
theorem orderFortyNine_existsUnique_defectCenter_of_not_adj_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    {v y : V} (hv : G.degree v = 8) (hy : G.degree y = 7)
    (hvy : ¬ G.Adj v y) :
    ∃! x : V, x ∈ G.neighborFinset v ∧
      (secondOrderDefectGraph G).Adj x y := by
  obtain ⟨x, hx, huniq⟩ :=
    orderFortyNine_existsUnique_highNeighbor_closedDefectOwner
      G hfree hmin hcard hv hy
  have hxy : x ≠ y := by
    intro h
    subst x
    exact hvy (by
      simpa [SimpleGraph.mem_neighborFinset] using hx.1)
  have hDxy : (secondOrderDefectGraph G).Adj x y := by
    rcases Finset.mem_insert.mp hx.2 with h | h
    · exact (hxy h.symm).elim
    · simpa [SimpleGraph.mem_neighborFinset] using h
  refine ⟨x, ⟨hx.1, hDxy⟩, ?_⟩
  intro z hz
  apply huniq z
  exact ⟨hz.1, Finset.mem_insert.mpr (Or.inr (by
    simpa [SimpleGraph.mem_neighborFinset] using hz.2))⟩

/-- In the one-high stratum, deleting the unique center edge from a leaf's
six defect incidences leaves exactly five leaf-layer defect neighbors. -/
theorem orderFortyNine_card_defectNeighbors_sdiff_centers_eq_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v y : V} (hv : G.degree v = 8) (hy : G.degree y = 7)
    (hvy : ¬ G.Adj v y) :
    ((secondOrderDefectGraph G).neighborFinset y \
      G.neighborFinset v).card = 5 := by
  let D := secondOrderDefectGraph G
  obtain ⟨x, hx, huniq⟩ :=
    orderFortyNine_existsUnique_defectCenter_of_not_adj_high
      G hfree hmin hcard hv hy hvy
  have hinter : D.neighborFinset y ∩ G.neighborFinset v = {x} := by
    ext z
    constructor
    · intro hz
      have hzparts := Finset.mem_inter.mp hz
      have hDz : D.Adj z y := by
        simpa [D, SimpleGraph.mem_neighborFinset, D.adj_comm] using hzparts.1
      have : z = x := huniq z ⟨hzparts.2, hDz⟩
      simp [this]
    · intro hz
      have hzx : z = x := by simpa using hz
      subst z
      apply Finset.mem_inter.mpr
      exact ⟨by
        simpa [D, SimpleGraph.mem_neighborFinset, D.adj_comm] using hx.2,
        hx.1⟩
  have hDdegree :=
    orderFortyNine_defectDegree_eq_six_of_one_high_of_not_adj
      G hfree hmin hcard hHigh hv hy hvy
  rw [Finset.card_sdiff, Finset.inter_comm, hinter, Finset.card_singleton,
    D.card_neighborFinset_eq_degree, hDdegree]

end

end Erdos85
