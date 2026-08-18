import Proofs.Erdos85OrderSixtyFourTwoComponentRepeatedClosing
import Proofs.Erdos85BinarySquareOwnerBlockRotatedRepeatedClosing
import Proofs.Erdos85BinarySquareSeparatedForkRowDensity

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

/-- For the two-owner color pattern `(a,a,b)`, every nonlocal cyclic
equal-root repeated closing yields a dense routing fragment of owner `a` or
owner `b`.  The third cyclic orientation uses the same-route adapter. -/
theorem binarySquare_regular_twoOwner_cyclicEqualRootRepeatedClosing_forces_ownerDensity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = q * m d)
    (a b e f g : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b)
    (hnonlocal : ¬ (e = f ∧ f = g))
    (hcyclic : HasCyclicEqualRootRepeatedClosing (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b) e f g) :
    HasTwoCenterRoutingRowDensityForOwner G hfree m a ∨
      HasTwoCenterRoutingRowDensityForOwner G hfree m b := by
  rcases hcyclic with ⟨hef, hr⟩ | ⟨hfg, hr⟩ | ⟨hge, hr⟩
  · have hfg' : f ≠ g := by
      intro h
      exact hnonlocal ⟨hef, h⟩
    have hd :=
      binarySquare_regular_equalRootsRepeatedClosing_forces_twoCenterRoutingRowDensity
        G hfree hq hreg hcard m hm a a b e f g hab hef hfg' hr
    rcases hd with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact Or.inl ⟨e, g, hef ▸ hfg', x, hx⟩
    · exact Or.inr ⟨e, g, hef ▸ hfg', x, hx⟩
  · have hge' : g ≠ e := by
      intro h
      apply hnonlocal
      exact ⟨(hfg.trans h).symm, hfg⟩
    have hd :=
      binarySquare_regular_equalRootsRepeatedClosing_forces_twoCenterRoutingRowDensity
        G hfree hq hreg hcard m hm a b a f g e hab.symm hfg hge' hr
    rcases hd with ⟨x, hx⟩ | ⟨x, hx⟩
    · exact Or.inr ⟨f, e, hfg ▸ hge', x, hx⟩
    · exact Or.inl ⟨f, e, hfg ▸ hge', x, hx⟩
  · have hef' : e ≠ f := by
      intro h
      apply hnonlocal
      exact ⟨h, h.symm.trans hge.symm⟩
    exact Or.inl
      (binarySquare_regular_equalRootsSameRouteRepeatedClosing_forces_ownerDensity
        G hfree hq hreg hcard m hm b a g e f hab.symm hge hef' hr)

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

/-- The `[5,3]` pressure route reaches a dense fragment for one of its two
owner colors. -/
theorem orderSixtyFour_threeFive_twoOwner_exists_ownerDensity
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
    HasTwoCenterRoutingRowDensityForOwner G hfree m a ∨
      HasTwoCenterRoutingRowDensityForOwner G hfree m b := by
  obtain ⟨e, f, g, hnonlocal, hcyclic⟩ :=
    orderSixtyFour_threeFive_twoOwner_exists_equalRootRepeatedClosing
      G hfree hreg hcount m hm a b hab hma hmb hcross
  exact binarySquare_regular_twoOwner_cyclicEqualRootRepeatedClosing_forces_ownerDensity
    G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm
      a b e f g hab hnonlocal hcyclic

/-- The `[4,4]` pressure route likewise reaches a dense fragment for one of
its two owner colors. -/
theorem orderSixtyFour_fourFour_twoOwner_exists_ownerDensity
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
    HasTwoCenterRoutingRowDensityForOwner G hfree m a ∨
      HasTwoCenterRoutingRowDensityForOwner G hfree m b := by
  obtain ⟨e, f, g, hnonlocal, hcyclic⟩ :=
    orderSixtyFour_fourFour_twoOwner_exists_equalRootRepeatedClosing
      G hfree hreg hcount m hm a b hab hma hmb hcross
  exact binarySquare_regular_twoOwner_cyclicEqualRootRepeatedClosing_forces_ownerDensity
    G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm
      a b e f g hab hnonlocal hcyclic

end

end Erdos85

#print axioms Erdos85.componentTriple_has_equal_pair_of_card_eq_two
#print axioms Erdos85.twoComponents_hasCyclicEqualRootRepeatedClosing
#print axioms Erdos85.binarySquare_regular_twoOwner_cyclicEqualRootRepeatedClosing_forces_ownerDensity
#print axioms Erdos85.orderSixtyFour_threeFive_twoOwner_exists_equalRootRepeatedClosing
#print axioms Erdos85.orderSixtyFour_fourFour_twoOwner_exists_equalRootRepeatedClosing
#print axioms Erdos85.orderSixtyFour_threeFive_twoOwner_exists_ownerDensity
#print axioms Erdos85.orderSixtyFour_fourFour_twoOwner_exists_ownerDensity
