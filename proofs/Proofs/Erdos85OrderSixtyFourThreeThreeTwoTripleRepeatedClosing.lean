import Proofs.Erdos85BinarySquareOwnerBlockRotatedRepeatedClosing
import Proofs.Erdos85BinarySquareSeparatedForkRowDensity

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

/-- In a rainbow `[3,3,2]` pressure block, the three cyclic repeated closings
force dense routing-row fragments for at least two of the three owner colors.
The fragments may have different roots and different ordered component rows. -/
theorem orderSixtyFour_threeThreeTwo_rainbow_forces_twoOwnerRoutingRowDensity
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
    (hef : e ≠ f) (hfg : f ≠ g) (heg : e ≠ g)
    (hblock : 253 ≤
      (cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) c) e f g).card) :
    (HasTwoCenterRoutingRowDensityForOwner G hfree m a ∧
        HasTwoCenterRoutingRowDensityForOwner G hfree m b) ∨
      (HasTwoCenterRoutingRowDensityForOwner G hfree m a ∧
        HasTwoCenterRoutingRowDensityForOwner G hfree m c) ∨
      (HasTwoCenterRoutingRowDensityForOwner G hfree m b ∧
        HasTwoCenterRoutingRowDensityForOwner G hfree m c) := by
  obtain ⟨hr₁, hr₂, hr₃⟩ :=
    orderSixtyFour_threeThreeTwo_tripleRepeatedClosing G hfree hreg hcount m hm
      a b c e f g hab hac hbc hma hmb hmc hblock
  have hd₁ := binarySquare_regular_rainbowRepeatedClosing_forces_twoCenterRoutingRowDensity
    G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm
      a b c e f g hef hfg heg hbc hr₁
  have hd₂ := binarySquare_regular_rainbowRepeatedClosing_forces_twoCenterRoutingRowDensity
    G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm
      b c a f g e hfg heg.symm hef.symm hac.symm hr₂
  have hd₃ := binarySquare_regular_rainbowRepeatedClosing_forces_twoCenterRoutingRowDensity
    G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm
      c a b g e f heg.symm hef hfg.symm hab hr₃
  rcases hd₁ with ⟨x, hx⟩ | ⟨y, hy⟩
  · have hc : HasTwoCenterRoutingRowDensityForOwner G hfree m c :=
      ⟨e, f, hef, x, hx⟩
    rcases hd₂ with ⟨y, hy⟩ | ⟨z, hz⟩
    · exact Or.inr (Or.inl ⟨⟨f, g, hfg, y, hy⟩, hc⟩)
    · rcases hd₃ with ⟨z, hz⟩ | ⟨x, hx⟩
      · exact Or.inr (Or.inr ⟨⟨g, e, heg.symm, z, hz⟩, hc⟩)
      · exact Or.inr (Or.inl ⟨⟨e, g, heg, x, hx⟩, hc⟩)
  · have hb : HasTwoCenterRoutingRowDensityForOwner G hfree m b :=
      ⟨f, e, hef.symm, y, hy⟩
    rcases hd₂ with ⟨y, hy⟩ | ⟨z, hz⟩
    · exact Or.inl ⟨⟨f, g, hfg, y, hy⟩, hb⟩
    · exact Or.inr (Or.inr ⟨hb, ⟨g, f, hfg.symm, z, hz⟩⟩)

/-- Sharpen the two-owner conclusion using the normalized sizes: either the
size-two owner `a` saturates a routing row, or both size-three owners carry
dense two-star fragments. -/
theorem orderSixtyFour_threeThreeTwo_rainbow_saturation_or_twoLargeOwnerDensities
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
    (hef : e ≠ f) (hfg : f ≠ g) (heg : e ≠ g)
    (hblock : 253 ≤
      (cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) c) e f g).card) :
    HasTwoCenterRoutingRowSaturationForOwner G hfree a ∨
      (HasTwoCenterRoutingRowDensityForOwner G hfree m b ∧
        HasTwoCenterRoutingRowDensityForOwner G hfree m c) := by
  have hd :=
    orderSixtyFour_threeThreeTwo_rainbow_forces_twoOwnerRoutingRowDensity
      G hfree hreg hcount m hm a b c e f g hab hac hbc hma hmb hmc
        hef hfg heg hblock
  rcases hd with ⟨ha, _hb⟩ | ⟨ha, _hc⟩ | hbcDensity
  · exact Or.inl
      (twoCenterRoutingRowDensityForOwner_saturates_of_m_eq_two
        G hfree m a hma ha)
  · exact Or.inl
      (twoCenterRoutingRowDensityForOwner_saturates_of_m_eq_two
        G hfree m a hma ha)
  · exact Or.inr hbcDensity

/-- Resolve the strict-density branch into its exact size-three form: each of
the two large owner colors has a unique unused third center at its dense-row
root. -/
theorem orderSixtyFour_threeThreeTwo_rainbow_saturation_or_twoUniqueThirdCenters
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
    (hef : e ≠ f) (hfg : f ≠ g) (heg : e ≠ g)
    (hblock : 253 ≤
      (cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) c) e f g).card) :
    HasTwoCenterRoutingRowSaturationForOwner G hfree a ∨
      (HasTwoCenterRoutingRowDensityWithUniqueThirdCenterForOwner
          G hfree m b ∧
        HasTwoCenterRoutingRowDensityWithUniqueThirdCenterForOwner
          G hfree m c) := by
  have hd :=
    orderSixtyFour_threeThreeTwo_rainbow_saturation_or_twoLargeOwnerDensities
      G hfree hreg hcount m hm a b c e f g hab hac hbc hma hmb hmc
        hef hfg heg hblock
  rcases hd with ha | ⟨hb, hc⟩
  · exact Or.inl ha
  · exact Or.inr ⟨
      twoCenterRoutingRowDensityForOwner_has_uniqueThirdCenter_of_m_eq_three
        G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm b hmb hb,
      twoCenterRoutingRowDensityForOwner_has_uniqueThirdCenter_of_m_eq_three
        G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm c hmc hc⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_threeThreeTwo_ownerColoredEdgesInBlocks_card_le
#print axioms Erdos85.orderSixtyFour_threeThreeTwo_tripleRepeatedClosing
#print axioms Erdos85.orderSixtyFour_threeThreeTwo_rainbow_forces_twoOwnerRoutingRowDensity
#print axioms Erdos85.orderSixtyFour_threeThreeTwo_rainbow_saturation_or_twoLargeOwnerDensities
#print axioms Erdos85.orderSixtyFour_threeThreeTwo_rainbow_saturation_or_twoUniqueThirdCenters
