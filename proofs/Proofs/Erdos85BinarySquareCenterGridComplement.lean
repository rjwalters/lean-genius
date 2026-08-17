import Proofs.Erdos85BinarySquareCrossRootCenterPairs
import Proofs.Erdos85ExteriorDefectDecomposition

/-! # Identifying the fourth factor in a cross-root center grid -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Center-grid pairs which are themselves second-order-defect edges. -/
def crossRootDefectCenterPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (x y : V) : Finset (V × V) :=
  (crossRootCenterGrid G x y).filter fun p =>
    (secondOrderDefectGraph G).Adj p.1 p.2

/-- Center-grid pairs having a common neighbor back in the roots' component. -/
def crossRootSourceCommonCenterPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (d : (secondOrderDefectGraph G).ConnectedComponent)
    (x y : V) : Finset (V × V) :=
  (crossRootCenterGrid G x y).filter fun p =>
    ∃ w : d.supp, G.Adj p.1 w.1 ∧ G.Adj p.2 w.1

private theorem centerGrid_coordinates_ne_of_defect_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : (secondOrderDefectGraph G).ConnectedComponent}
    (x y : d.supp)
    (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1)
    {p : V × V} (hp : p ∈ crossRootCenterGrid G x.1 y.1) :
    p.1 ≠ p.2 := by
  rw [crossRootCenterGrid, Finset.mem_product] at hp
  intro huv
  have hxy : x.1 ≠ y.1 := (secondOrderDefectGraph G).ne_of_adj hxyD
  have hxu : G.Adj x.1 p.1 := (G.mem_neighborFinset x.1 p.1).mp hp.1
  have hyv : G.Adj y.1 p.2 := (G.mem_neighborFinset y.1 p.2).mp hp.2
  exact (not_secondOrderDefect_adj_of_commonNeighbor G hfree hxy
    hxu (huv ▸ hyv)) hxyD

/-- Every pair in the center grid of a defect edge either is a defect edge or
has an ambient common neighbor. -/
theorem centerGrid_pair_defect_or_exists_commonNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d : (secondOrderDefectGraph G).ConnectedComponent}
    (x y : d.supp)
    (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1)
    {p : V × V} (hp : p ∈ crossRootCenterGrid G x.1 y.1) :
    (secondOrderDefectGraph G).Adj p.1 p.2 ∨
      ∃ w : V, G.Adj p.1 w ∧ G.Adj p.2 w := by
  have huv := centerGrid_coordinates_ne_of_defect_adj G hfree x y hxyD hp
  by_cases hD : (secondOrderDefectGraph G).Adj p.1 p.2
  · exact Or.inl hD
  · right
    have hcard :
        (G.neighborFinset p.1 ∩ G.neighborFinset p.2).card ≠ 0 := by
      intro hzero
      exact hD ((secondOrderDefectGraph_adj_iff_card_common_eq_zero
        G hfree huv).mpr hzero)
    obtain ⟨w, hw⟩ := Finset.card_ne_zero.mp hcard
    exact ⟨w, (G.mem_neighborFinset p.1 w).mp (Finset.mem_inter.mp hw).1,
      (G.mem_neighborFinset p.2 w).mp (Finset.mem_inter.mp hw).2⟩

/-- A common neighbor realizes its center pair in the transition graph of the
component containing that neighbor. -/
theorem centerPair_mem_targetFinset_of_commonNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d e : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x y : d.supp)
    {p : V × V} {w : V}
    (hwcomp : (secondOrderDefectGraph G).connectedComponentMk w = e)
    (hpw : G.Adj p.1 w ∧ G.Adj p.2 w)
    (hpgrid : p ∈ crossRootCenterGrid G x.1 y.1) :
    p ∈ crossRootCenterPairFinset G hfree hde x y := by
  rw [crossRootCenterGrid, Finset.mem_product] at hpgrid
  let ws : e.supp := ⟨w, (ConnectedComponent.mem_supp_iff e w).mpr hwcomp⟩
  apply Finset.mem_image.mpr
  refine ⟨ws, Finset.mem_univ _, ?_⟩
  apply Prod.ext
  · exact (eq_crossCommonNeighbor_of_adj G hfree hde x ws
      ⟨(G.mem_neighborFinset x.1 p.1).mp hpgrid.1, hpw.1.symm⟩).symm
  · exact (eq_crossCommonNeighbor_of_adj G hfree hde y ws
      ⟨(G.mem_neighborFinset y.1 p.2).mp hpgrid.2, hpw.2.symm⟩).symm

/-- Once four named components exhaust the component type, every edge left
outside the three remote transition factors is either a source-component
common-neighbor pair or a defect pair. -/
theorem crossRootCenterGrid_complement_subset_sourceCommon_union_defect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d e f g : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (hdf : d ≠ f) (hdg : d ≠ g)
    (hexhaust : ∀ k : (secondOrderDefectGraph G).ConnectedComponent,
      k = d ∨ k = e ∨ k = f ∨ k = g)
    (x y : d.supp)
    (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1) :
    crossRootCenterGrid G x.1 y.1 \ ((
        crossRootCenterPairFinset G hfree hde x y ∪
          crossRootCenterPairFinset G hfree hdf x y) ∪
        crossRootCenterPairFinset G hfree hdg x y) ⊆
      crossRootSourceCommonCenterPairs G d x.1 y.1 ∪
        crossRootDefectCenterPairs G x.1 y.1 := by
  intro p hp
  have hpgrid := (Finset.mem_sdiff.mp hp).1
  have hpremote := (Finset.mem_sdiff.mp hp).2
  rcases centerGrid_pair_defect_or_exists_commonNeighbor
      G hfree x y hxyD hpgrid with hD | ⟨w, hpw⟩
  · apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨hpgrid, hD⟩
  · let k := (secondOrderDefectGraph G).connectedComponentMk w
    rcases hexhaust k with hk | hk | hk | hk
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨hpgrid, ⟨⟨w, ?_⟩, hpw⟩⟩
      exact (ConnectedComponent.mem_supp_iff d w).mpr hk
    · exfalso
      apply hpremote
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact centerPair_mem_targetFinset_of_commonNeighbor
        G hfree hde x y hk hpw hpgrid
    · exfalso
      apply hpremote
      apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact centerPair_mem_targetFinset_of_commonNeighbor
        G hfree hdf x y hk hpw hpgrid
    · exfalso
      apply hpremote
      apply Finset.mem_union_right
      exact centerPair_mem_targetFinset_of_commonNeighbor
        G hfree hdg x y hk hpw hpgrid

/-- Source-common pairs cannot occur in a genuinely remote transition
factor. -/
theorem crossRootSourceCommonCenterPairs_disjoint_target
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d e : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x y : d.supp)
    (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1) :
    Disjoint (crossRootSourceCommonCenterPairs G d x.1 y.1)
      (crossRootCenterPairFinset G hfree hde x y) := by
  classical
  rw [Finset.disjoint_left]
  intro p hpSource hpTarget
  obtain ⟨hpgrid, w, hpw⟩ := Finset.mem_filter.mp hpSource
  obtain ⟨z, _hz, hpz⟩ := Finset.mem_image.mp hpTarget
  have huv := centerGrid_coordinates_ne_of_defect_adj G hfree x y hxyD hpgrid
  have hwz : w.1 ≠ z.1 := by
    intro hwz
    apply hde
    have hwd := (ConnectedComponent.mem_supp_iff d w.1).mp w.2
    have hze := (ConnectedComponent.mem_supp_iff e z.1).mp z.2
    exact hwd.symm.trans ((congrArg
      (secondOrderDefectGraph G).connectedComponentMk hwz).trans hze)
  have hz₁ := (crossCommonNeighbor_spec G hfree hde x z).2
  have hz₂ := (crossCommonNeighbor_spec G hfree hde y z).2
  have hcenter₁ := congrArg Prod.fst hpz
  have hcenter₂ := congrArg Prod.snd hpz
  change crossCommonNeighbor G hfree hde x z = p.1 at hcenter₁
  change crossCommonNeighbor G hfree hde y z = p.2 at hcenter₂
  rw [hcenter₁] at hz₁
  rw [hcenter₂] at hz₂
  exact hfree (containsC4_of_two_common huv hwz
    hpw.1.symm hpw.2.symm hz₁ hz₂)

/-- Defect pairs have no common neighbor, so they cannot occur in any remote
transition factor. -/
theorem crossRootDefectCenterPairs_disjoint_target
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d e : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x y : d.supp) :
    Disjoint (crossRootDefectCenterPairs G x.1 y.1)
      (crossRootCenterPairFinset G hfree hde x y) := by
  classical
  rw [Finset.disjoint_left]
  intro p hpDefect hpTarget
  obtain ⟨_hpgrid, hpD⟩ := Finset.mem_filter.mp hpDefect
  obtain ⟨z, _hz, hpz⟩ := Finset.mem_image.mp hpTarget
  have hz₁ := (crossCommonNeighbor_spec G hfree hde x z).2
  have hz₂ := (crossCommonNeighbor_spec G hfree hde y z).2
  have hcenter₁ := congrArg Prod.fst hpz
  have hcenter₂ := congrArg Prod.snd hpz
  change crossCommonNeighbor G hfree hde x z = p.1 at hcenter₁
  change crossCommonNeighbor G hfree hde y z = p.2 at hcenter₂
  rw [hcenter₁] at hz₁
  rw [hcenter₂] at hz₂
  exact (not_secondOrderDefect_adj_of_commonNeighbor G hfree
    ((secondOrderDefectGraph G).ne_of_adj hpD) hz₁.symm hz₂.symm) hpD

/-- Exact identification of the anonymous fourth factor: after removing the
three remote target factors, the center grid consists precisely of the
source-common pairs and the defect pairs. -/
theorem crossRootCenterGrid_complement_eq_sourceCommon_union_defect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d e f g : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (hdf : d ≠ f) (hdg : d ≠ g)
    (hexhaust : ∀ k : (secondOrderDefectGraph G).ConnectedComponent,
      k = d ∨ k = e ∨ k = f ∨ k = g)
    (x y : d.supp)
    (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1) :
    crossRootCenterGrid G x.1 y.1 \ ((
        crossRootCenterPairFinset G hfree hde x y ∪
          crossRootCenterPairFinset G hfree hdf x y) ∪
        crossRootCenterPairFinset G hfree hdg x y) =
      crossRootSourceCommonCenterPairs G d x.1 y.1 ∪
        crossRootDefectCenterPairs G x.1 y.1 := by
  apply Finset.Subset.antisymm
  · exact crossRootCenterGrid_complement_subset_sourceCommon_union_defect
      G hfree hde hdf hdg hexhaust x y hxyD
  · intro p hp
    rcases Finset.mem_union.mp hp with hpSource | hpDefect
    · have hpgrid := (Finset.mem_filter.mp hpSource).1
      apply Finset.mem_sdiff.mpr
      refine ⟨hpgrid, ?_⟩
      intro hpRemote
      rcases Finset.mem_union.mp hpRemote with hpEF | hpG
      · rcases Finset.mem_union.mp hpEF with hpE | hpF
        · exact Finset.disjoint_left.mp
            (crossRootSourceCommonCenterPairs_disjoint_target
              G hfree hde x y hxyD) hpSource hpE
        · exact Finset.disjoint_left.mp
            (crossRootSourceCommonCenterPairs_disjoint_target
              G hfree hdf x y hxyD) hpSource hpF
      · exact Finset.disjoint_left.mp
          (crossRootSourceCommonCenterPairs_disjoint_target
            G hfree hdg x y hxyD) hpSource hpG
    · have hpgrid := (Finset.mem_filter.mp hpDefect).1
      apply Finset.mem_sdiff.mpr
      refine ⟨hpgrid, ?_⟩
      intro hpRemote
      rcases Finset.mem_union.mp hpRemote with hpEF | hpG
      · rcases Finset.mem_union.mp hpEF with hpE | hpF
        · exact Finset.disjoint_left.mp
            (crossRootDefectCenterPairs_disjoint_target
              G hfree hde x y) hpDefect hpE
        · exact Finset.disjoint_left.mp
            (crossRootDefectCenterPairs_disjoint_target
              G hfree hdf x y) hpDefect hpF
      · exact Finset.disjoint_left.mp
          (crossRootDefectCenterPairs_disjoint_target
            G hfree hdg x y) hpDefect hpG

/-- The two graph-native pieces of the fourth factor are disjoint. -/
theorem crossRootSourceCommonCenterPairs_disjoint_defect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (d : (secondOrderDefectGraph G).ConnectedComponent)
    (x y : V) :
    Disjoint (crossRootSourceCommonCenterPairs G d x y)
      (crossRootDefectCenterPairs G x y) := by
  classical
  rw [Finset.disjoint_left]
  intro p hpSource hpDefect
  obtain ⟨_hpgrid, w, hpw⟩ := Finset.mem_filter.mp hpSource
  have hpD := (Finset.mem_filter.mp hpDefect).2
  exact (not_secondOrderDefect_adj_of_commonNeighbor G hfree
    ((secondOrderDefectGraph G).ne_of_adj hpD) hpw.1 hpw.2) hpD

/-- Numerical form of the identified fourth factor at order sixty-four. -/
theorem orderSixtyFour_sourceCommon_add_defect_centerPairs_card_eq_sixteen
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ z, G.degree z = 8)
    {d e f g : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (hdf : d ≠ f) (hdg : d ≠ g)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (he : e.supp.ncard = 16) (hf : f.supp.ncard = 16)
    (hg : g.supp.ncard = 16)
    (hexhaust : ∀ k : (secondOrderDefectGraph G).ConnectedComponent,
      k = d ∨ k = e ∨ k = f ∨ k = g)
    (x y : d.supp)
    (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1) :
    (crossRootSourceCommonCenterPairs G d x.1 y.1).card +
      (crossRootDefectCenterPairs G x.1 y.1).card = 16 := by
  have hcard :=
    orderSixtyFour_three_remoteTargets_centerGrid_complement_card_eq_sixteen
      G hfree hreg hde hdf hdg hef heg hfg he hf hg x y hxyD
  rw [crossRootCenterGrid_complement_eq_sourceCommon_union_defect
      G hfree hde hdf hdg hexhaust x y hxyD,
    Finset.card_union_of_disjoint
      (crossRootSourceCommonCenterPairs_disjoint_defect
        G hfree d x.1 y.1)] at hcard
  exact hcard

/-- The source-common part of the fourth factor is left-unique: it is the
graph of a partial function on the first center neighborhood. -/
theorem binarySquare_sizeTwo_sourceCommonCenterPairs_left_unique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d : (secondOrderDefectGraph G).ConnectedComponent}
    (hdTwo : ∀ u : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) d u).card = 2)
    (x y : d.supp)
    (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1)
    {p q : V × V}
    (hp : p ∈ crossRootSourceCommonCenterPairs G d x.1 y.1)
    (hq : q ∈ crossRootSourceCommonCenterPairs G d x.1 y.1)
    (hfirst : p.1 = q.1) : p = q := by
  classical
  obtain ⟨hpgrid, w, hpw⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqgrid, z, hqz⟩ := Finset.mem_filter.mp hq
  have hpgrid' := hpgrid
  have hqgrid' := hqgrid
  rw [crossRootCenterGrid, Finset.mem_product] at hpgrid' hqgrid'
  have hxy : x.1 ≠ y.1 := (secondOrderDefectGraph G).ne_of_adj hxyD
  have hwx : w.1 ≠ x.1 := by
    intro hwx
    have hyv : G.Adj y.1 p.2 := (G.mem_neighborFinset y.1 p.2).mp hpgrid'.2
    have hxv : G.Adj x.1 p.2 := by simpa [hwx] using hpw.2.symm
    exact (not_secondOrderDefect_adj_of_commonNeighbor G hfree hxy
      hxv hyv) hxyD
  have hzx : z.1 ≠ x.1 := by
    intro hzx
    have hyv : G.Adj y.1 q.2 := (G.mem_neighborFinset y.1 q.2).mp hqgrid'.2
    have hxv : G.Adj x.1 q.2 := by simpa [hzx] using hqz.2.symm
    exact (not_secondOrderDefect_adj_of_commonNeighbor G hfree hxy
      hxv hyv) hxyD
  have hwz : w.1 = z.1 := by
    by_contra hwz
    let S := componentNeighborFinset G (secondOrderDefectGraph G) d p.1
    have hxS : x.1 ∈ S := by
      dsimp [S]
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset p.1 x.1).mpr
        ((G.mem_neighborFinset x.1 p.1).mp hpgrid'.1).symm,
        (ConnectedComponent.mem_supp_iff d x.1).mp x.2⟩
    have hwS : w.1 ∈ S := by
      dsimp [S]
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset p.1 w.1).mpr hpw.1,
        (ConnectedComponent.mem_supp_iff d w.1).mp w.2⟩
    have hzS : z.1 ∈ S := by
      dsimp [S]
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset p.1 z.1).mpr (hfirst ▸ hqz.1),
        (ConnectedComponent.mem_supp_iff d z.1).mp z.2⟩
    have hthree : ({x.1, w.1, z.1} : Finset V).card = 3 := by
      have hxw : x.1 ≠ w.1 := hwx.symm
      have hxz : x.1 ≠ z.1 := hzx.symm
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
      · simpa only [Finset.mem_singleton] using hwz
      · simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using
          And.intro hxw hxz
    have hsub : ({x.1, w.1, z.1} : Finset V) ⊆ S := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hxS, hwS, hzS⟩
    have := Finset.card_le_card hsub
    rw [hthree, hdTwo p.1] at this
    omega
  apply Prod.ext hfirst
  by_contra hsecond
  have hyw : y.1 ≠ w.1 := by
    intro hyw
    have hxu : G.Adj x.1 p.1 := (G.mem_neighborFinset x.1 p.1).mp hpgrid'.1
    have hyu : G.Adj y.1 p.1 := by simpa [hyw] using hpw.1.symm
    exact (not_secondOrderDefect_adj_of_commonNeighbor G hfree hxy
      hxu hyu) hxyD
  apply hfree
  exact containsC4_of_two_common hyw hsecond
    ((G.mem_neighborFinset y.1 p.2).mp hpgrid'.2).symm hpw.2
    ((G.mem_neighborFinset y.1 q.2).mp hqgrid'.2).symm
    (by simpa [hwz] using hqz.2)

/-- The same source-common factor is right-unique, hence is a matching. -/
theorem binarySquare_sizeTwo_sourceCommonCenterPairs_right_unique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d : (secondOrderDefectGraph G).ConnectedComponent}
    (hdTwo : ∀ u : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) d u).card = 2)
    (x y : d.supp)
    (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1)
    {p q : V × V}
    (hp : p ∈ crossRootSourceCommonCenterPairs G d x.1 y.1)
    (hq : q ∈ crossRootSourceCommonCenterPairs G d x.1 y.1)
    (hsecond : p.2 = q.2) : p = q := by
  classical
  have swap_mem {r : V × V}
      (hr : r ∈ crossRootSourceCommonCenterPairs G d x.1 y.1) :
      r.swap ∈ crossRootSourceCommonCenterPairs G d y.1 x.1 := by
    obtain ⟨hrgrid, w, hrw⟩ := Finset.mem_filter.mp hr
    rw [crossRootCenterGrid, Finset.mem_product] at hrgrid
    apply Finset.mem_filter.mpr
    refine ⟨?_, ⟨w, hrw.2, hrw.1⟩⟩
    rw [crossRootCenterGrid, Finset.mem_product]
    exact ⟨hrgrid.2, hrgrid.1⟩
  have hswap := binarySquare_sizeTwo_sourceCommonCenterPairs_left_unique
    G hfree hdTwo y x hxyD.symm (swap_mem hp) (swap_mem hq) hsecond
  exact Prod.swap_injective hswap

/-- Consequently the source-common portion has cardinality at most the
ambient degree of either root. -/
theorem binarySquare_sizeTwo_sourceCommonCenterPairs_card_le_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d : (secondOrderDefectGraph G).ConnectedComponent}
    (hdTwo : ∀ u : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) d u).card = 2)
    (x y : d.supp)
    (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1) :
    (crossRootSourceCommonCenterPairs G d x.1 y.1).card ≤ G.degree x.1 := by
  let S := crossRootSourceCommonCenterPairs G d x.1 y.1
  have hinj : Set.InjOn Prod.fst (↑S : Set (V × V)) := by
    intro p hp q hq hpq
    exact binarySquare_sizeTwo_sourceCommonCenterPairs_left_unique
      G hfree hdTwo x y hxyD hp hq hpq
  have himage : S.image Prod.fst ⊆ G.neighborFinset x.1 := by
    intro u hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  calc
    S.card = (S.image Prod.fst).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (G.neighborFinset x.1).card := Finset.card_le_card himage
    _ = G.degree x.1 := G.card_neighborFinset_eq_degree x.1

end

end Erdos85
