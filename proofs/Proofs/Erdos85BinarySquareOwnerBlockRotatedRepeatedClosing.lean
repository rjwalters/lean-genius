import Proofs.Erdos85OrderSixtyFourThreeComponentRepeatedClosing

/-! # Rotating a component block before the repeated-closing pigeonhole -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Cyclic rotation preserves the cardinality of a fixed component-pattern
owner-colored triangle block. -/
theorem card_cyclicColoredTriplesInBlocks_rotate
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (e f g : D.ConnectedComponent) :
    (cyclicColoredTriplesInBlocks D A B C e f g).card =
      (cyclicColoredTriplesInBlocks D B C A f g e).card := by
  classical
  apply Finset.card_bij (fun p _ => (p.2.2, p.1, p.2.1))
  · intro p hp
    simp only [cyclicColoredTriplesInBlocks, cyclicColoredTriples,
      Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨⟨hp.1.2.1, hp.1.2.2, hp.1.1⟩,
      hp.2.2.1, hp.2.2.2, hp.2.1⟩
  · intro p hp q hq hpq
    rcases p with ⟨x, z, y⟩
    rcases q with ⟨x', z', y'⟩
    simp only at hpq
    cases hpq
    rfl
  · intro p hp
    refine ⟨(p.2.1, p.2.2, p.1), ?_, ?_⟩
    · simp only [cyclicColoredTriplesInBlocks, cyclicColoredTriples,
        Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact ⟨⟨hp.1.2.2, hp.1.1, hp.1.2.1⟩,
        hp.2.2.2, hp.2.1, hp.2.2.1⟩
    · rcases p with ⟨x, z, y⟩
      rfl

/-- If the second owner-edge space is smaller than the original block, rotate
the block and obtain a repeated closing whose fixed first edge has colors
`B`; its roots lie in components `f,g` and its closings in `e`. -/
theorem exists_rotated_repeatedClosing_of_secondOwnerEdge_card_lt_block_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (e f g : D.ConnectedComponent)
    (hmore : (ownerColoredEdgesInBlocks D B f g).card <
      (cyclicColoredTriplesInBlocks D A B C e f g).card) :
    HasRepeatedClosingInBlock D B C A f g e := by
  apply exists_repeatedClosing_of_ownerEdge_card_lt_block_card
  rwa [← card_cyclicColoredTriplesInBlocks_rotate D A B C e f g]

/-- Rotate twice and pigeonhole the third owner edge. -/
theorem exists_twiceRotated_repeatedClosing_of_thirdOwnerEdge_card_lt_block_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (e f g : D.ConnectedComponent)
    (hmore : (ownerColoredEdgesInBlocks D C g e).card <
      (cyclicColoredTriplesInBlocks D A B C e f g).card) :
    HasRepeatedClosingInBlock D C A B g e f := by
  apply exists_repeatedClosing_of_ownerEdge_card_lt_block_card
  rw [← card_cyclicColoredTriplesInBlocks_rotate D B C A f g e,
    ← card_cyclicColoredTriplesInBlocks_rotate D A B C e f g]
  exact hmore

/-- In the `[4,2,2]` owner ordering used by the pressure theorem, a block of
size at least 219 whose last two component labels agree exceeds the entire
second-owner edge space after cyclic rotation. -/
theorem orderSixtyFour_fourTwoTwo_rotatedRepeatedClosing_of_f_eq_g
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
    (hma : m a = 2) (hmb : m b = 2) (hmc : m c = 4)
    (hfg : f = g)
    (hblock : 219 ≤
      (cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) c) e f g).card) :
    HasRepeatedClosingInBlock (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c)
      (componentOwnerGraph G (secondOrderDefectGraph G) a) f g e := by
  subst g
  have hf := eq_first_or_second_or_third_of_card_eq_three
    hcount a b c f hab hac hbc
  have hedge := binarySquare_regular_card_ownerColoredEdgesInBlocks
    G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm b f f
  have hedgeLe :
      (ownerColoredEdgesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) f f).card ≤ 192 := by
    rcases hf with hf | hf | hf
    all_goals subst f
    all_goals simp [hma, hmb, hmc, hab, hac, hbc,
      Ne.symm hab, Ne.symm hac, Ne.symm hbc] at hedge ⊢ <;> omega
  apply exists_rotated_repeatedClosing_of_secondOwnerEdge_card_lt_block_card
  omega

/-- The analogous rotated pigeonhole for `[3,3,2]`; here the second-owner
edge space has size at most 144, far below the forced block size 253. -/
theorem orderSixtyFour_threeThreeTwo_rotatedRepeatedClosing_of_f_eq_g
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
    (hfg : f = g)
    (hblock : 253 ≤
      (cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) c) e f g).card) :
    HasRepeatedClosingInBlock (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c)
      (componentOwnerGraph G (secondOrderDefectGraph G) a) f g e := by
  subst g
  have hf := eq_first_or_second_or_third_of_card_eq_three
    hcount a b c f hab hac hbc
  have hedge := binarySquare_regular_card_ownerColoredEdgesInBlocks
    G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm b f f
  have hedgeLe :
      (ownerColoredEdgesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) f f).card ≤ 144 := by
    rcases hf with hf | hf | hf
    all_goals subst f
    all_goals simp [hma, hmb, hmc, hab, hac, hbc,
      Ne.symm hab, Ne.symm hac, Ne.symm hbc] at hedge ⊢ <;> omega
  apply exists_rotated_repeatedClosing_of_secondOwnerEdge_card_lt_block_card
  omega

/-- In `[3,3,2]`, the twice-rotated third-owner edge space is also at most
144, so the `e=g` asymmetric pattern becomes an equal-root closing. -/
theorem orderSixtyFour_threeThreeTwo_twiceRotatedRepeatedClosing_of_e_eq_g
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
    (heg : e = g)
    (hblock : 253 ≤
      (cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) c) e f g).card) :
    HasRepeatedClosingInBlock (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) c)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b) g e f := by
  subst g
  have he := eq_first_or_second_or_third_of_card_eq_three
    hcount a b c e hab hac hbc
  have hedge := binarySquare_regular_card_ownerColoredEdgesInBlocks
    G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm c e e
  have hedgeLe :
      (ownerColoredEdgesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) c) e e).card ≤ 144 := by
    rcases he with he | he | he
    all_goals subst e
    all_goals simp [hma, hmb, hmc, hab, hac, hbc,
      Ne.symm hab, Ne.symm hac, Ne.symm hbc] at hedge ⊢ <;> omega
  apply exists_twiceRotated_repeatedClosing_of_thirdOwnerEdge_card_lt_block_card
  omega

/-- In `[4,2,2]`, the same twice-rotated argument works unless the repeated
component is the normalized size-four component itself. -/
theorem orderSixtyFour_fourTwoTwo_twiceRotatedRepeatedClosing_of_e_eq_g_of_ne_c
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
    (hma : m a = 2) (hmb : m b = 2) (hmc : m c = 4)
    (heg : e = g) (hec : e ≠ c)
    (hblock : 219 ≤
      (cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) c) e f g).card) :
    HasRepeatedClosingInBlock (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) c)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b) g e f := by
  subst g
  have he := eq_first_or_second_or_third_of_card_eq_three
    hcount a b c e hab hac hbc
  have hedge := binarySquare_regular_card_ownerColoredEdgesInBlocks
    G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm c e e
  have hedgeLe :
      (ownerColoredEdgesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) c) e e).card ≤ 64 := by
    rcases he with he | he | he
    · subst e
      simp [hma, hmc, hac] at hedge ⊢
      omega
    · subst e
      simp [hmb, hmc, hbc] at hedge ⊢
      omega
    · exact (hec he).elim
  apply exists_twiceRotated_repeatedClosing_of_thirdOwnerEdge_card_lt_block_card
  omega

end

end Erdos85

#print axioms Erdos85.card_cyclicColoredTriplesInBlocks_rotate
#print axioms Erdos85.exists_rotated_repeatedClosing_of_secondOwnerEdge_card_lt_block_card
#print axioms Erdos85.orderSixtyFour_fourTwoTwo_rotatedRepeatedClosing_of_f_eq_g
#print axioms Erdos85.orderSixtyFour_threeThreeTwo_rotatedRepeatedClosing_of_f_eq_g
#print axioms Erdos85.exists_twiceRotated_repeatedClosing_of_thirdOwnerEdge_card_lt_block_card
#print axioms Erdos85.orderSixtyFour_threeThreeTwo_twiceRotatedRepeatedClosing_of_e_eq_g
#print axioms Erdos85.orderSixtyFour_fourTwoTwo_twiceRotatedRepeatedClosing_of_e_eq_g_of_ne_c
