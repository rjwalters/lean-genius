import Proofs.Erdos85BinarySquareMixedOwnerRootedPatternBounds
import Proofs.Erdos85BinarySquareMixedOwnerRainbowBridge

/-! # Rooted component-pattern pressure in the no-rainbow branch -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 10000 in
/-- If the prescribed three owner colors form no rainbow inside any defect
component, then at every root either the two external vertices share a
component at least twenty times or all three vertices occupy distinct
components at least twenty times. -/
theorem orderSixtyFour_regular_fourComponents_noRainbow_large_pattern_three_or_four
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
    20 ≤ (rootedComponentPatternPairs (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x 3).card ∨
    20 ≤ (rootedComponentPatternPairs (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x 4).card := by
  classical
  let D := secondOrderDefectGraph G
  let A := componentOwnerGraph G D a
  let B := componentOwnerGraph G D b
  let C := componentOwnerGraph G D c
  let P := fun i : Fin 5 =>
    (rootedComponentPatternPairs D A B C x i).card
  have hsum : (∑ i : Fin 5, P i) = 56 := by
    exact orderSixtyFour_regular_fourComponents_sum_rootedComponentPatterns_eq
      G hfree hreg hcount a b c hab hac hbc x
  rw [Fin.sum_univ_five] at hsum
  have hrootEmpty : rootedSameComponentCyclicColoredPairs D A B C x = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨p, hp⟩
    have hp' := Finset.mem_filter.mp hp
    have hcolor := (Finset.mem_filter.mp hp'.1).2
    have hsameNonempty : (sameComponentCyclicColoredTriples D A B C).Nonempty := by
      refine ⟨(x, p.1, p.2), ?_⟩
      rw [sameComponentCyclicColoredTriples, Finset.mem_filter,
        cyclicColoredTriples, Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _, hcolor⟩,
        hp'.2.1.symm, hp'.2.1.trans hp'.2.2.symm⟩
    exact hno
      ((sameComponent_mixedOwnerTriangles_nonempty_iff_exists_routingOwnerRainbow
        G a b c).mp hsameNonempty)
  have hzero : P 0 = 0 := by
    dsimp [P]
    rw [rootedComponentPatternPairs_zero_eq_sameComponent, hrootEmpty,
      Finset.card_empty]
  have hone : P 1 ≤ 8 :=
    orderSixtyFour_regular_fourComponents_rootedPattern_one_card_le_eight
      G hfree hreg hcount a b c hab hac hbc x
  have htwo : P 2 ≤ 8 :=
    orderSixtyFour_regular_fourComponents_rootedPattern_two_card_le_eight
      G hfree hreg hcount a b c hab hac hbc x
  change 20 ≤ P 3 ∨ 20 ≤ P 4
  omega

end

end Erdos85
