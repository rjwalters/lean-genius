import Proofs.Erdos85BinarySquareOwnerBlockRotatedRepeatedClosing

/-! # Three cyclic repeated closings in the `[3,3,2]` pressure block -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every directed owner-edge block in the `[3,3,2]` stratum has at most
216 edges, uniformly over its owner color and endpoint components. -/
theorem orderSixtyFour_threeThreeTwo_ownerColoredEdgesInBlocks_card_le
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 3)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = 8 * m d)
    (a b c owner e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hma : m a = 2) (hmb : m b = 3) (hmc : m c = 3) :
    (ownerColoredEdgesInBlocks (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) owner) e f).card ≤ 216 := by
  have hedge := binarySquare_regular_card_ownerColoredEdgesInBlocks
    G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm owner e f
  have ho := eq_first_or_second_or_third_of_card_eq_three
    hcount a b c owner hab hac hbc
  have he := eq_first_or_second_or_third_of_card_eq_three
    hcount a b c e hab hac hbc
  have hf := eq_first_or_second_or_third_of_card_eq_three
    hcount a b c f hab hac hbc
  rcases ho with ho | ho | ho <;>
    rcases he with he | he | he <;>
      rcases hf with hf | hf | hf
  all_goals subst owner; subst e; subst f
  all_goals simp [hma, hmb, hmc, hab, hac, hbc,
    Ne.symm hab, Ne.symm hac, Ne.symm hbc] at hedge ⊢ <;> omega

/-- A 253-point `[3,3,2]` pressure block exceeds all three cyclic owner-edge
spaces, hence produces a repeated closing in every orientation. -/
theorem orderSixtyFour_threeThreeTwo_tripleRepeatedClosing
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 3)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = 8 * m d)
    (a b c e f g : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hma : m a = 2) (hmb : m b = 3) (hmc : m c = 3)
    (hblock : 253 ≤
      (cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) c) e f g).card) :
    HasRepeatedClosingInBlock (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) c) e f g ∧
      HasRepeatedClosingInBlock (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) c)
        (componentOwnerGraph G (secondOrderDefectGraph G) a) f g e ∧
      HasRepeatedClosingInBlock (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) c)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) g e f := by
  have hedgeA := orderSixtyFour_threeThreeTwo_ownerColoredEdgesInBlocks_card_le
    G hfree hreg hcount m hm a b c a e f hab hac hbc hma hmb hmc
  have hedgeB := orderSixtyFour_threeThreeTwo_ownerColoredEdgesInBlocks_card_le
    G hfree hreg hcount m hm a b c b f g hab hac hbc hma hmb hmc
  have hedgeC := orderSixtyFour_threeThreeTwo_ownerColoredEdgesInBlocks_card_le
    G hfree hreg hcount m hm a b c c g e hab hac hbc hma hmb hmc
  refine ⟨?_, ?_, ?_⟩
  · apply exists_repeatedClosing_of_ownerEdge_card_lt_block_card
    omega
  · apply exists_rotated_repeatedClosing_of_secondOwnerEdge_card_lt_block_card
    omega
  · apply exists_twiceRotated_repeatedClosing_of_thirdOwnerEdge_card_lt_block_card
    omega

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_threeThreeTwo_ownerColoredEdgesInBlocks_card_le
#print axioms Erdos85.orderSixtyFour_threeThreeTwo_tripleRepeatedClosing
