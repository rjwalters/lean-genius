import Proofs.Erdos85BinarySquareMixedOwnerNoRainbowPatternFour
import Proofs.Erdos85BinarySquareMixedOwnerRootedRoutingCycles

/-! # Middle-component concentration in the no-rainbow branch -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 10000 in
/-- If the owner colors have no same-component rainbow, then at every root
some external defect component contains the middle vertices of at least six
prescribed `(a,b,c)` routing cycles. -/
theorem orderSixtyFour_regular_fourComponents_noRainbow_exists_middleComponent_six
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
    ∃ e : (secondOrderDefectGraph G).ConnectedComponent,
      e ≠ (secondOrderDefectGraph G).connectedComponentMk x ∧
      6 ≤ ((rootedAllDistinctRoutingCyclePairs G hfree a b c x).filter
        fun p => (secondOrderDefectGraph G).connectedComponentMk p.2 = e).card := by
  classical
  let D := secondOrderDefectGraph G
  let S := rootedAllDistinctRoutingCyclePairs G hfree a b c x
  let f : Fin 64 × Fin 64 → D.ConnectedComponent := fun p =>
    D.connectedComponentMk p.2
  let t : Finset D.ConnectedComponent := Finset.univ.erase
    (D.connectedComponentMk x)
  have hS : 16 ≤ S.card := by
    dsimp [S]
    rw [← rootedPattern_four_eq_rootedAllDistinctRoutingCyclePairs
      G hfree a b c x]
    exact
      orderSixtyFour_regular_fourComponents_noRainbow_patternFour_card_ge_sixteen
        G hfree hreg hcount a b c hab hac hbc hno x
  have ht : t.card = 3 := by
    dsimp [t]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      hcount]
  have hmaps : ∀ p ∈ S, f p ∈ t := by
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    obtain ⟨hxy, _hyz, _hzx, _ha, _hb, _hc⟩ := hp'
    dsimp [t]
    rw [Finset.mem_erase]
    exact ⟨hxy.symm, Finset.mem_univ _⟩
  by_contra hnone
  push Not at hnone
  have hfiber : ∀ e ∈ t, (S.filter fun p => f p = e).card ≤ 5 := by
    intro e he
    have hene : e ≠ D.connectedComponentMk x :=
      (Finset.mem_erase.mp he).1
    have hlt := hnone e hene
    dsimp [S, f, D]
    omega
  have hle := Finset.card_le_mul_card_image_of_maps_to hmaps 5 hfiber
  rw [ht] at hle
  omega

end

end Erdos85
