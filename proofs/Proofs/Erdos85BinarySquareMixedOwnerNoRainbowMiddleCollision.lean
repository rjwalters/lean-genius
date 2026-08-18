import Proofs.Erdos85BinarySquareMixedOwnerNoRainbowMiddleConcentration
import Proofs.Erdos85BinarySquareSizeTwoRoutingRegularity

/-! # Repeated middle vertices in concentrated no-rainbow routing cycles -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 10000 in
/-- In the no-rainbow branch, every root has two distinct prescribed routing
cycles through the same external middle vertex.  More precisely, that middle
vertex lies in one external component and is joined to the root by owner
color `a`. -/
theorem orderSixtyFour_regular_fourComponents_noRainbow_exists_repeatedMiddle
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
    (x : Fin 64) :
    ∃ (e : (secondOrderDefectGraph G).ConnectedComponent) (y : Fin 64),
      e ≠ (secondOrderDefectGraph G).connectedComponentMk x ∧
      (secondOrderDefectGraph G).connectedComponentMk y = e ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) a).Adj x y ∧
      2 ≤ (((rootedAllDistinctRoutingCyclePairs G hfree a b c x).filter
        fun p => (secondOrderDefectGraph G).connectedComponentMk p.2 = e).filter
          fun p => p.2 = y).card := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨e, hene, hmiddle⟩ :=
    orderSixtyFour_regular_fourComponents_noRainbow_exists_middleComponent_six
      G hfree hreg hcount a b c hab hac hbc hno x
  have hxe : D.connectedComponentMk x ≠ e := hene.symm
  let xs : (D.connectedComponentMk x).supp :=
    ⟨x, ConnectedComponent.connectedComponentMk_mem⟩
  let R : Finset e.supp := (Finset.univ : Finset e.supp).filter fun y =>
    a = crossIntermediateComponent G hfree hxe xs y
  let Y : Finset (Fin 64) := R.image Subtype.val
  have hall := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hRcard : R.card = 4 := by
    dsimp [R]
    exact binarySquare_regular_threeSizeTwoParts_routing_row_card_eq_four
      G hfree (q := 8) (by norm_num) hreg (by norm_num)
        (D.connectedComponentMk x) a e hxe
        (by simpa using hall (D.connectedComponentMk x))
        (by simpa using hall a) (by simpa using hall e) xs
  have hYcard : Y.card = 4 := by
    dsimp [Y]
    rw [Finset.card_image_of_injective _ Subtype.val_injective, hRcard]
  let S := (rootedAllDistinctRoutingCyclePairs G hfree a b c x).filter
    fun p => D.connectedComponentMk p.2 = e
  have hmaps : ∀ p ∈ S, p.2 ∈ Y := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hroute := (Finset.mem_filter.mp hp'.1).2
    obtain ⟨hxy, _hyz, _hzx, ha, _hb, _hc⟩ := hroute
    have hyp : p.2 ∈ e.supp :=
      (ConnectedComponent.mem_supp_iff e p.2).mpr hp'.2
    apply Finset.mem_image.mpr
    refine ⟨⟨p.2, hyp⟩, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hadj : (componentOwnerGraph G D a).Adj x p.2 :=
      componentOwnerGraph_adj_of_crossIntermediateComponent_eq_owner
        G hfree hxy
          ⟨x, ConnectedComponent.connectedComponentMk_mem⟩
          ⟨p.2, ConnectedComponent.connectedComponentMk_mem⟩ a ha
    exact (crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hxe xs ⟨p.2, hyp⟩ a hadj).symm
  have hScard : 6 ≤ S.card := by
    simpa [S, D] using hmiddle
  have hcollision : ∃ y ∈ Y, 2 ≤ (S.filter fun p => p.2 = y).card := by
    by_contra hnone
    push Not at hnone
    have hfiber : ∀ y ∈ Y, (S.filter fun p => p.2 = y).card ≤ 1 := by
      intro y hy
      have hlt := hnone y hy
      omega
    have hle := Finset.card_le_mul_card_image_of_maps_to hmaps 1 hfiber
    rw [hYcard] at hle
    omega
  obtain ⟨y, hyY, hycard⟩ := hcollision
  obtain ⟨ys, hysR, hys⟩ := Finset.mem_image.mp hyY
  have hycomp : D.connectedComponentMk y = e := by
    subst y
    exact (ConnectedComponent.mem_supp_iff e ys.1).mp ys.2
  have hyroute :
      crossIntermediateComponent G hfree hxe xs ys = a := by
    have := (Finset.mem_filter.mp hysR).2
    exact this.symm
  have hyowner : (componentOwnerGraph G D a).Adj x y := by
    subst y
    exact componentOwnerGraph_adj_of_crossIntermediateComponent_eq_owner
      G hfree hxe xs ys a hyroute
  refine ⟨e, y, hene, hycomp, hyowner, ?_⟩
  simpa [S, D] using hycard

end

end Erdos85
