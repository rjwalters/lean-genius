import Proofs.Erdos85OrderSixtyFourThreeComponentPatternPressure
import Proofs.Erdos85BinarySquareOwnerBlockRepeatedClosing

/-! # Repeated closings in the order-64 three-component strata -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A fixed component-pattern block contains two distinct colored triangles
with the same first owner edge. -/
def HasRepeatedClosingInBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (e f g : D.ConnectedComponent) : Prop :=
  ∃ p ∈ cyclicColoredTriplesInBlocks D A B C e f g,
    ∃ r ∈ cyclicColoredTriplesInBlocks D A B C e f g,
      p ≠ r ∧ p.1 = r.1 ∧ p.2.2 = r.2.2 ∧ p.2.1 ≠ r.2.1

/-- Three pairwise-distinct elements exhaust a finite type of cardinality
three. -/
theorem eq_first_or_second_or_third_of_card_eq_three
    {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 3) (a b c x : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    x = a ∨ x = b ∨ x = c := by
  have hsetCard : ({a, b, c} : Finset α).card = 3 := by
    simp [hab, hac, hbc]
  have huniv : ({a, b, c} : Finset α) = Finset.univ := by
    apply Finset.eq_univ_of_card
    simpa [hsetCard] using hcard.symm
  have hx : x ∈ ({a, b, c} : Finset α) := by simp [huniv]
  simpa [Finset.mem_insert, Finset.mem_singleton] using hx

/-- The order-64 three-component pressure block always exceeds its available
first owner edges, hence contains a repeated closing. -/
theorem orderSixtyFour_regular_threeComponents_repeatedClosing
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 3) :
    ∃ m : (secondOrderDefectGraph G).ConnectedComponent → ℕ,
      (∀ d, d.supp.ncard = 8 * m d) ∧
      ((∃ a b c e f g : (secondOrderDefectGraph G).ConnectedComponent,
          a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
          m a = 2 ∧ m b = 2 ∧ m c = 4 ∧
          ¬ (e = f ∧ f = g) ∧
          HasRepeatedClosingInBlock (secondOrderDefectGraph G)
            (componentOwnerGraph G (secondOrderDefectGraph G) a)
            (componentOwnerGraph G (secondOrderDefectGraph G) b)
            (componentOwnerGraph G (secondOrderDefectGraph G) c) e f g) ∨
       (∃ a b c e f g : (secondOrderDefectGraph G).ConnectedComponent,
          a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
          m a = 2 ∧ m b = 3 ∧ m c = 3 ∧
          ¬ (e = f ∧ f = g) ∧
          HasRepeatedClosingInBlock (secondOrderDefectGraph G)
            (componentOwnerGraph G (secondOrderDefectGraph G) a)
            (componentOwnerGraph G (secondOrderDefectGraph G) b)
            (componentOwnerGraph G (secondOrderDefectGraph G) c) e f g)) := by
  obtain ⟨m, hm, hpressure⟩ :=
    orderSixtyFour_regular_threeComponents_patternPressure
      G hfree hreg hcount
  refine ⟨m, hm, ?_⟩
  rcases hpressure with h422 | h332
  · left
    obtain ⟨a, b, c, e, f, g, hab, hac, hbc,
      hma, hmb, hmc, hnonlocal, hblock⟩ := h422
    have he := eq_first_or_second_or_third_of_card_eq_three
      hcount a b c e hab hac hbc
    have hf := eq_first_or_second_or_third_of_card_eq_three
      hcount a b c f hab hac hbc
    have hedge := binarySquare_regular_card_ownerColoredEdgesInBlocks
      G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm a e f
    have hedgeLe :
        (ownerColoredEdgesInBlocks (secondOrderDefectGraph G)
          (componentOwnerGraph G (secondOrderDefectGraph G) a) e f).card ≤ 192 := by
      rcases he with he | he | he <;>
        rcases hf with hf | hf | hf
      all_goals subst e; subst f
      all_goals simp [hma, hmb, hmc, hab, hac, hbc,
        Ne.symm hab, Ne.symm hac, Ne.symm hbc] at hedge ⊢ <;> omega
    have hmore :
        (ownerColoredEdgesInBlocks (secondOrderDefectGraph G)
          (componentOwnerGraph G (secondOrderDefectGraph G) a) e f).card <
        (cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
          (componentOwnerGraph G (secondOrderDefectGraph G) a)
          (componentOwnerGraph G (secondOrderDefectGraph G) b)
          (componentOwnerGraph G (secondOrderDefectGraph G) c) e f g).card := by
      omega
    have hrepeat := exists_repeatedClosing_of_ownerEdge_card_lt_block_card
      (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c)
      e f g hmore
    exact ⟨a, b, c, e, f, g, hab, hac, hbc,
      hma, hmb, hmc, hnonlocal, hrepeat⟩
  · right
    obtain ⟨a, b, c, e, f, g, hab, hac, hbc,
      hma, hmb, hmc, hnonlocal, hblock⟩ := h332
    have he := eq_first_or_second_or_third_of_card_eq_three
      hcount a b c e hab hac hbc
    have hf := eq_first_or_second_or_third_of_card_eq_three
      hcount a b c f hab hac hbc
    have hedge := binarySquare_regular_card_ownerColoredEdgesInBlocks
      G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm a e f
    have hedgeLe :
        (ownerColoredEdgesInBlocks (secondOrderDefectGraph G)
          (componentOwnerGraph G (secondOrderDefectGraph G) a) e f).card ≤ 144 := by
      rcases he with he | he | he <;>
        rcases hf with hf | hf | hf
      all_goals subst e; subst f
      all_goals simp [hma, hmb, hmc, hab, hac, hbc,
        Ne.symm hab, Ne.symm hac, Ne.symm hbc] at hedge ⊢ <;> omega
    have hmore :
        (ownerColoredEdgesInBlocks (secondOrderDefectGraph G)
          (componentOwnerGraph G (secondOrderDefectGraph G) a) e f).card <
        (cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
          (componentOwnerGraph G (secondOrderDefectGraph G) a)
          (componentOwnerGraph G (secondOrderDefectGraph G) b)
          (componentOwnerGraph G (secondOrderDefectGraph G) c) e f g).card := by
      omega
    have hrepeat := exists_repeatedClosing_of_ownerEdge_card_lt_block_card
      (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c)
      e f g hmore
    exact ⟨a, b, c, e, f, g, hab, hac, hbc,
      hma, hmb, hmc, hnonlocal, hrepeat⟩

end

end Erdos85

#print axioms Erdos85.eq_first_or_second_or_third_of_card_eq_three
#print axioms Erdos85.orderSixtyFour_regular_threeComponents_repeatedClosing
