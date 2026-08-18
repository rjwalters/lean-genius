import Proofs.Erdos85BinarySquareTwoOwnerCrossPressure
import Proofs.Erdos85OrderSixtyFourThreeComponentRepeatedClosing

/-! # Nonlocal repeated closings in the order-64 two-component strata -/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem eq_first_or_second_of_card_eq_two
    {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 2) (a b x : α) (hab : a ≠ b) :
    x = a ∨ x = b := by
  have hsetCard : ({a, b} : Finset α).card = 2 := by simp [hab]
  have huniv : ({a, b} : Finset α) = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa [hsetCard] using hcard.symm
  have hx : x ∈ ({a, b} : Finset α) := by simp [huniv]
  simpa [Finset.mem_insert, Finset.mem_singleton] using hx

/-- The `[5,3]` cross budget forces a nonlocal repeated closing in a fixed
component-pattern block. -/
theorem orderSixtyFour_threeFive_twoOwner_exists_nonlocalRepeatedClosing
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
    ∃ e f g : (secondOrderDefectGraph G).ConnectedComponent,
      ¬ (e = f ∧ f = g) ∧
      852 ≤ (cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) e f g).card ∧
      HasRepeatedClosingInBlock (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) e f g := by
  obtain ⟨e, f, g, hnonlocal, hblock⟩ :=
    twoComponents_exists_large_cross_componentBlock
      (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      hcount 851 (by omega)
  have he := eq_first_or_second_of_card_eq_two hcount a b e hab
  have hf := eq_first_or_second_of_card_eq_two hcount a b f hab
  have hedge := binarySquare_regular_card_ownerColoredEdgesInBlocks
    G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm a e f
  have hedgeLe :
      (ownerColoredEdgesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a) e f).card ≤ 480 := by
    rcases he with he | he <;> rcases hf with hf | hf
    all_goals subst e; subst f
    all_goals simp [hma, hmb, hab, Ne.symm hab] at hedge ⊢ <;> omega
  refine ⟨e, f, g, hnonlocal, by omega, ?_⟩
  apply exists_repeatedClosing_of_ownerEdge_card_lt_block_card
  omega

/-- The symmetric `[4,4]` cross budget forces the analogous nonlocal
repeated closing. -/
theorem orderSixtyFour_fourFour_twoOwner_exists_nonlocalRepeatedClosing
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
    ∃ e f g : (secondOrderDefectGraph G).ConnectedComponent,
      ¬ (e = f ∧ f = g) ∧
      1536 ≤ (cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) e f g).card ∧
      HasRepeatedClosingInBlock (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) e f g := by
  obtain ⟨e, f, g, hnonlocal, hblock⟩ :=
    twoComponents_exists_large_cross_componentBlock
      (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      hcount 1535 (by omega)
  have he := eq_first_or_second_of_card_eq_two hcount a b e hab
  have hf := eq_first_or_second_of_card_eq_two hcount a b f hab
  have hedge := binarySquare_regular_card_ownerColoredEdgesInBlocks
    G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm a e f
  have hedgeLe :
      (ownerColoredEdgesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a) e f).card ≤ 512 := by
    rcases he with he | he <;> rcases hf with hf | hf
    all_goals subst e; subst f
    all_goals simp [hma, hmb, hab, Ne.symm hab] at hedge ⊢ <;> omega
  refine ⟨e, f, g, hnonlocal, by omega, ?_⟩
  apply exists_repeatedClosing_of_ownerEdge_card_lt_block_card
  omega

end

end Erdos85

#print axioms Erdos85.eq_first_or_second_of_card_eq_two
#print axioms Erdos85.orderSixtyFour_threeFive_twoOwner_exists_nonlocalRepeatedClosing
#print axioms Erdos85.orderSixtyFour_fourFour_twoOwner_exists_nonlocalRepeatedClosing
