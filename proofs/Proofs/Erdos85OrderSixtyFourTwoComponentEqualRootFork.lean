import Proofs.Erdos85OrderSixtyFourTwoComponentRepeatedClosing
import Proofs.Erdos85BinarySquareOwnerBlockRotatedRepeatedClosing

/-! # Equal-root normalization of two-component owner forks -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A cyclic block admits a repeated closing after rotating to a pair of equal
component labels. -/
def HasCyclicEqualRootRepeatedClosing
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (e f g : D.ConnectedComponent) : Prop :=
  (e = f ∧ HasRepeatedClosingInBlock D A B C e f g) ∨
  (f = g ∧ HasRepeatedClosingInBlock D B C A f g e) ∨
  (g = e ∧ HasRepeatedClosingInBlock D C A B g e f)

theorem componentTriple_has_equal_pair_of_card_eq_two
    {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 2) (e f g : α) :
    e = f ∨ f = g ∨ g = e := by
  by_cases hef : e = f
  · exact Or.inl hef
  rcases eq_first_or_second_of_card_eq_two hcard e f g hef with hge | hgf
  · exact Or.inr (Or.inr hge)
  · exact Or.inr (Or.inl hgf.symm)

/-- Abstract rotation step: in a two-component type, a nonlocal block has an
equal pair; if both rotated edge spaces are smaller than the block, a repeated
closing can always be placed on that equal pair. -/
theorem twoComponents_hasCyclicEqualRootRepeatedClosing
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (hcount : Fintype.card D.ConnectedComponent = 2)
    (e f g : D.ConnectedComponent)
    (hrepeat : HasRepeatedClosingInBlock D A B C e f g)
    (hsecond : (ownerColoredEdgesInBlocks D B f g).card <
      (cyclicColoredTriplesInBlocks D A B C e f g).card)
    (hthird : (ownerColoredEdgesInBlocks D C g e).card <
      (cyclicColoredTriplesInBlocks D A B C e f g).card) :
    HasCyclicEqualRootRepeatedClosing D A B C e f g := by
  rcases componentTriple_has_equal_pair_of_card_eq_two hcount e f g with
    hef | hfg | hge
  · exact Or.inl ⟨hef, hrepeat⟩
  · exact Or.inr (Or.inl ⟨hfg,
      exists_rotated_repeatedClosing_of_secondOwnerEdge_card_lt_block_card
        D A B C e f g hsecond⟩)
  · exact Or.inr (Or.inr ⟨hge,
      exists_twiceRotated_repeatedClosing_of_thirdOwnerEdge_card_lt_block_card
        D A B C e f g hthird⟩)

/-- `[5,3]` always has an equal-root repeated closing after cyclic
normalization of its pressured nonlocal block. -/
theorem orderSixtyFour_threeFive_twoOwner_exists_equalRootRepeatedClosing
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = 8 * m d)
    (a b : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hma : m a = 3) (hmb : m b = 5)
    (hcross : 6816 ≤
      (crossComponentCyclicColoredTriples (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)).card) :
    ∃ e f g,
      ¬ (e = f ∧ f = g) ∧
      HasCyclicEqualRootRepeatedClosing (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) e f g := by
  obtain ⟨e, f, g, hnonlocal, hblock, hrepeat⟩ :=
    orderSixtyFour_threeFive_twoOwner_exists_nonlocalRepeatedClosing
      G hfree hreg hcount m hm a b hab hma hmb hcross
  have hf := eq_first_or_second_of_card_eq_two hcount a b f hab
  have hg := eq_first_or_second_of_card_eq_two hcount a b g hab
  have he := eq_first_or_second_of_card_eq_two hcount a b e hab
  have hedgeSecond := binarySquare_regular_card_ownerColoredEdgesInBlocks
    G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm a f g
  have hedgeThird := binarySquare_regular_card_ownerColoredEdgesInBlocks
    G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm b g e
  have hsecond :
      (ownerColoredEdgesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a) f g).card <
      (cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) e f g).card := by
    rcases hf with hf | hf <;> rcases hg with hg | hg
    all_goals subst f; subst g
    all_goals simp [hma, hmb, hab, Ne.symm hab] at hedgeSecond ⊢ <;> omega
  have hthird :
      (ownerColoredEdgesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) g e).card <
      (cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) e f g).card := by
    rcases hg with hg | hg <;> rcases he with he | he
    all_goals subst g; subst e
    all_goals simp [hma, hmb, hab, Ne.symm hab] at hedgeThird ⊢ <;> omega
  exact ⟨e, f, g, hnonlocal,
    twoComponents_hasCyclicEqualRootRepeatedClosing
      _ _ _ _ hcount e f g hrepeat hsecond hthird⟩

/-- `[4,4]` also always normalizes to an equal-root repeated closing. -/
theorem orderSixtyFour_fourFour_twoOwner_exists_equalRootRepeatedClosing
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = 8 * m d)
    (a b : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hma : m a = 4) (hmb : m b = 4)
    (hcross : 12288 ≤
      (crossComponentCyclicColoredTriples (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)).card) :
    ∃ e f g,
      ¬ (e = f ∧ f = g) ∧
      HasCyclicEqualRootRepeatedClosing (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) e f g := by
  obtain ⟨e, f, g, hnonlocal, hblock, hrepeat⟩ :=
    orderSixtyFour_fourFour_twoOwner_exists_nonlocalRepeatedClosing
      G hfree hreg hcount m hm a b hab hma hmb hcross
  have hf := eq_first_or_second_of_card_eq_two hcount a b f hab
  have hg := eq_first_or_second_of_card_eq_two hcount a b g hab
  have he := eq_first_or_second_of_card_eq_two hcount a b e hab
  have hedgeSecond := binarySquare_regular_card_ownerColoredEdgesInBlocks
    G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm a f g
  have hedgeThird := binarySquare_regular_card_ownerColoredEdgesInBlocks
    G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm b g e
  have hsecond :
      (ownerColoredEdgesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a) f g).card <
      (cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) e f g).card := by
    rcases hf with hf | hf <;> rcases hg with hg | hg
    all_goals subst f; subst g
    all_goals simp [hma, hmb, hab, Ne.symm hab] at hedgeSecond ⊢ <;> omega
  have hthird :
      (ownerColoredEdgesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) g e).card <
      (cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) e f g).card := by
    rcases hg with hg | hg <;> rcases he with he | he
    all_goals subst g; subst e
    all_goals simp [hma, hmb, hab, Ne.symm hab] at hedgeThird ⊢ <;> omega
  exact ⟨e, f, g, hnonlocal,
    twoComponents_hasCyclicEqualRootRepeatedClosing
      _ _ _ _ hcount e f g hrepeat hsecond hthird⟩

end

end Erdos85

#print axioms Erdos85.componentTriple_has_equal_pair_of_card_eq_two
#print axioms Erdos85.twoComponents_hasCyclicEqualRootRepeatedClosing
#print axioms Erdos85.orderSixtyFour_threeFive_twoOwner_exists_equalRootRepeatedClosing
#print axioms Erdos85.orderSixtyFour_fourFour_twoOwner_exists_equalRootRepeatedClosing
