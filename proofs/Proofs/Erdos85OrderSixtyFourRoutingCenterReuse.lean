import Proofs.Erdos85OrderSixtyFourNoRainbowRoutingCyclePressure
import Proofs.Erdos85BinarySquareSeparatedCentersPackingBound
import Proofs.Erdos85OrderSixtyFourDefectComponentEquitable

/-! # Rooted routing pressure forces reuse of a closing center -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 10000

/-- The canonical common-neighbor center of the closing route of a rooted
routing cycle.  Packaging the cycle with its membership proof makes the
cross-component inequality available definitionally. -/
def rootedRoutingClosingCenter
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (x : Fin 64)
    (p : {p // p ∈ rootedAllDistinctRoutingCyclePairs G hfree a b c x}) :
    Fin 64 := by
  let D := secondOrderDefectGraph G
  exact if hzx : D.connectedComponentMk p.1.1 ≠ D.connectedComponentMk x then
    crossCommonNeighbor G hfree hzx
      ⟨p.1.1, ConnectedComponent.connectedComponentMk_mem⟩
      ⟨x, ConnectedComponent.connectedComponentMk_mem⟩
  else x

/-- The finite set of canonical closing centers used by the rooted routing
cycles of prescribed colors. -/
def rootedRoutingClosingCenters
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (x : Fin 64) : Finset (Fin 64) :=
  (rootedAllDistinctRoutingCyclePairs G hfree a b c x).attach.image
    (rootedRoutingClosingCenter G hfree a b c x)

/-- Every canonical closing center is adjacent to the root. -/
theorem rootedRoutingClosingCenter_adj_root
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (x : Fin 64)
    (p : {p // p ∈ rootedAllDistinctRoutingCyclePairs G hfree a b c x}) :
    G.Adj (rootedRoutingClosingCenter G hfree a b c x p) x := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨_hxy, _hyz, hzx, _ha, _hb, _hc⟩ :=
    (Finset.mem_filter.mp p.2).2
  rw [rootedRoutingClosingCenter]
  simp only [dif_pos hzx]
  exact (crossCommonNeighbor_spec G hfree hzx
    ⟨p.1.1, ConnectedComponent.connectedComponentMk_mem⟩
    ⟨x, ConnectedComponent.connectedComponentMk_mem⟩).2.symm

/-- A size-sixteen target component with two neighbors from every canonical
closing center supplies the concrete eight-center capacity hypothesis. -/
theorem rootedRoutingClosingCenters_card_le_eight_of_target
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (a b c target : (secondOrderDefectGraph G).ConnectedComponent)
    (x : Fin 64)
    (hxtarget : (secondOrderDefectGraph G).connectedComponentMk x ≠ target)
    (htwo : ∀ u ∈ rootedRoutingClosingCenters G hfree a b c x,
      (componentNeighborFinset G (secondOrderDefectGraph G) target u).card = 2)
    (htarget : target.supp.ncard = 16) :
    (rootedRoutingClosingCenters G hfree a b c x).card ≤ 8 := by
  apply card_centers_le_eight_of_sharedNeighbor_twoPointSelectors
    G (secondOrderDefectGraph G) hfree target
      (rootedRoutingClosingCenters G hfree a b c x) x hxtarget
  · intro u hu
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hu
    exact rootedRoutingClosingCenter_adj_root G hfree a b c x p
  · exact htwo
  · exact htarget

/-- Sixteen rooted cycles routed through at most eight canonical closing
centers force two distinct cycles to reuse the same center. -/
theorem exists_distinct_rootedRoutingCycles_same_closingCenter_of_card_ge_sixteen
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (x : Fin 64)
    (hcycles : 16 ≤
      (rootedAllDistinctRoutingCyclePairs G hfree a b c x).card)
    (hcenters : (rootedRoutingClosingCenters G hfree a b c x).card ≤ 8) :
    ∃ p q : {p // p ∈ rootedAllDistinctRoutingCyclePairs G hfree a b c x},
      p ≠ q ∧
        rootedRoutingClosingCenter G hfree a b c x p =
          rootedRoutingClosingCenter G hfree a b c x q := by
  classical
  let S := rootedAllDistinctRoutingCyclePairs G hfree a b c x
  let f := rootedRoutingClosingCenter G hfree a b c x
  by_contra h
  push Not at h
  have hinj : Function.Injective f := by
    intro p q hpq
    by_contra hpq'
    exact (h p q hpq') hpq
  have himage : (S.attach.image f).card = S.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
  change (S.attach.image f).card ≤ 8 at hcenters
  change 16 ≤ S.card at hcycles
  omega

/-- In the order-sixty-four no-rainbow branch, the rooted pressure theorem
supplies the sixteen cycles automatically.  Thus an eight-center capacity
bound immediately forces canonical closing-center reuse. -/
theorem orderSixtyFour_noRainbow_exists_distinct_rootedRoutingCycles_same_closingCenter
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hno : ¬ ∃ d : (secondOrderDefectGraph G).ConnectedComponent,
      routingOwnerRainbow G d a b c)
    (x : Fin 64)
    (hcenters : (rootedRoutingClosingCenters G hfree a b c x).card ≤ 8) :
    ∃ p q : {p // p ∈ rootedAllDistinctRoutingCyclePairs G hfree a b c x},
      p ≠ q ∧
        rootedRoutingClosingCenter G hfree a b c x p =
          rootedRoutingClosingCenter G hfree a b c x q := by
  apply exists_distinct_rootedRoutingCycles_same_closingCenter_of_card_ge_sixteen
    G hfree a b c x
  · exact
      orderSixtyFour_regular_fourComponents_noRainbow_rootedRoutingCycles_card_ge_sixteen
        G hfree hreg hcount a b c hab hac hbc hno x
  · exact hcenters

/-- Fully composed selector-packing form: a remote size-sixteen component
seen twice by every closing center turns no-rainbow pressure directly into
two distinct rooted cycles with a common canonical center. -/
theorem orderSixtyFour_noRainbow_exists_centerReuse_of_remote_twoPointSelectors
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (a b c target : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hno : ¬ ∃ d : (secondOrderDefectGraph G).ConnectedComponent,
      routingOwnerRainbow G d a b c)
    (x : Fin 64)
    (hxtarget : (secondOrderDefectGraph G).connectedComponentMk x ≠ target)
    (htwo : ∀ u ∈ rootedRoutingClosingCenters G hfree a b c x,
      (componentNeighborFinset G (secondOrderDefectGraph G) target u).card = 2)
    (htarget : target.supp.ncard = 16) :
    ∃ p q : {p // p ∈ rootedAllDistinctRoutingCyclePairs G hfree a b c x},
      p ≠ q ∧
        rootedRoutingClosingCenter G hfree a b c x p =
          rootedRoutingClosingCenter G hfree a b c x q := by
  apply orderSixtyFour_noRainbow_exists_distinct_rootedRoutingCycles_same_closingCenter
    G hfree hreg hcount a b c hab hac hbc hno x
  exact rootedRoutingClosingCenters_card_le_eight_of_target
    G hfree a b c target x hxtarget htwo htarget

/-- In the regular four-component all-sixteen branch, equitability makes the
two-point-selector hypothesis automatic.  Any component remote from the root
therefore forces closing-center reuse. -/
theorem orderSixtyFour_noRainbow_allSixteen_exists_centerReuse
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (hsize : ∀ d : (secondOrderDefectGraph G).ConnectedComponent,
      d.supp.ncard = 16)
    (a b c target : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hno : ¬ ∃ d : (secondOrderDefectGraph G).ConnectedComponent,
      routingOwnerRainbow G d a b c)
    (x : Fin 64)
    (hxtarget : (secondOrderDefectGraph G).connectedComponentMk x ≠ target) :
    ∃ p q : {p // p ∈ rootedAllDistinctRoutingCyclePairs G hfree a b c x},
      p ≠ q ∧
        rootedRoutingClosingCenter G hfree a b c x p =
          rootedRoutingClosingCenter G hfree a b c x q := by
  apply orderSixtyFour_noRainbow_exists_centerReuse_of_remote_twoPointSelectors
    G hfree hreg hcount a b c target hab hac hbc hno x hxtarget
  · intro u _hu
    have hmul := orderSixtyFour_eight_mul_componentNeighborFinset_card
      G hfree (fun v => by rw [hreg v])
        (fun {_v _w} _hvw => Or.inl (hreg _v)) target u
    rw [hsize target] at hmul
    omega
  · exact hsize target

end

end Erdos85
