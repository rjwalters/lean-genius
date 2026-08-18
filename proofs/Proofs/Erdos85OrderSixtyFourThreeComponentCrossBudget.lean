import Proofs.Erdos85BinarySquareMixedOwnerGeneralFiberBound
import Proofs.Erdos85OrderSixtyFourRegularPartitionShapes

/-! # Cross-component mixed-owner budgets in the three-component strata -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In either three-component partition, one can order the owner colors with
the two smallest parts first.  The exact mixed trace and size-sensitive local
fiber bound then force the displayed large cross-component census. -/
theorem orderSixtyFour_regular_threeComponents_crossBudget
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
      ((∃ a b c : (secondOrderDefectGraph G).ConnectedComponent,
          a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
          m a = 2 ∧ m b = 2 ∧ m c = 4 ∧
          5888 ≤
            (crossComponentCyclicColoredTriples (secondOrderDefectGraph G)
              (componentOwnerGraph G (secondOrderDefectGraph G) a)
              (componentOwnerGraph G (secondOrderDefectGraph G) b)
              (componentOwnerGraph G (secondOrderDefectGraph G) c)).card) ∨
       (∃ a b c : (secondOrderDefectGraph G).ConnectedComponent,
          a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
          m a = 2 ∧ m b = 3 ∧ m c = 3 ∧
          6816 ≤
            (crossComponentCyclicColoredTriples (secondOrderDefectGraph G)
              (componentOwnerGraph G (secondOrderDefectGraph G) a)
              (componentOwnerGraph G (secondOrderDefectGraph G) b)
              (componentOwnerGraph G (secondOrderDefectGraph G) c)).card)) := by
  classical
  obtain ⟨m, E, hm, hshape⟩ :=
    orderSixtyFour_regular_three_defectComponents_partition_shape
      G hfree hreg hcount
  have hne01 : E.symm 0 ≠ E.symm 1 := by simp
  have hne02 : E.symm 0 ≠ E.symm 2 := by simp
  have hne12 : E.symm 1 ≠ E.symm 2 := by simp
  refine ⟨m, hm, ?_⟩
  rcases hshape with h | h | h | h | h | h
  · left
    let a := E.symm 1
    let b := E.symm 2
    let c := E.symm 0
    have hbudget := orderSixtyFour_regular_crossComponent_mixedOwner_card_ge
      G hfree hreg m hm a b c hne12 hne01.symm hne02.symm
    have hreindex := Equiv.sum_comp E.symm (fun source =>
      8 * m source * (m a * (m source - 1)) *
        (m b * (m source - 1)))
    rw [← hreindex, Fin.sum_univ_three] at hbudget
    dsimp [a, b, c] at hbudget
    norm_num [h.1, h.2.1, h.2.2] at hbudget
    exact ⟨a, b, c, hne12, hne01.symm, hne02.symm,
      h.2.1, h.2.2, h.1, hbudget⟩
  · left
    let a := E.symm 0
    let b := E.symm 2
    let c := E.symm 1
    have hbudget := orderSixtyFour_regular_crossComponent_mixedOwner_card_ge
      G hfree hreg m hm a b c hne02 hne01 hne12.symm
    have hreindex := Equiv.sum_comp E.symm (fun source =>
      8 * m source * (m a * (m source - 1)) *
        (m b * (m source - 1)))
    rw [← hreindex, Fin.sum_univ_three] at hbudget
    dsimp [a, b, c] at hbudget
    norm_num [h.1, h.2.1, h.2.2] at hbudget
    exact ⟨a, b, c, hne02, hne01, hne12.symm,
      h.1, h.2.2, h.2.1, hbudget⟩
  · left
    let a := E.symm 0
    let b := E.symm 1
    let c := E.symm 2
    have hbudget := orderSixtyFour_regular_crossComponent_mixedOwner_card_ge
      G hfree hreg m hm a b c hne01 hne02 hne12
    have hreindex := Equiv.sum_comp E.symm (fun source =>
      8 * m source * (m a * (m source - 1)) *
        (m b * (m source - 1)))
    rw [← hreindex, Fin.sum_univ_three] at hbudget
    dsimp [a, b, c] at hbudget
    norm_num [h.1, h.2.1, h.2.2] at hbudget
    exact ⟨a, b, c, hne01, hne02, hne12,
      h.1, h.2.1, h.2.2, hbudget⟩
  · right
    let a := E.symm 0
    let b := E.symm 1
    let c := E.symm 2
    have hbudget := orderSixtyFour_regular_crossComponent_mixedOwner_card_ge
      G hfree hreg m hm a b c hne01 hne02 hne12
    have hreindex := Equiv.sum_comp E.symm (fun source =>
      8 * m source * (m a * (m source - 1)) *
        (m b * (m source - 1)))
    rw [← hreindex, Fin.sum_univ_three] at hbudget
    dsimp [a, b, c] at hbudget
    norm_num [h.1, h.2.1, h.2.2] at hbudget
    exact ⟨a, b, c, hne01, hne02, hne12,
      h.1, h.2.1, h.2.2, hbudget⟩
  · right
    let a := E.symm 1
    let b := E.symm 0
    let c := E.symm 2
    have hbudget := orderSixtyFour_regular_crossComponent_mixedOwner_card_ge
      G hfree hreg m hm a b c hne01.symm hne12 hne02
    have hreindex := Equiv.sum_comp E.symm (fun source =>
      8 * m source * (m a * (m source - 1)) *
        (m b * (m source - 1)))
    rw [← hreindex, Fin.sum_univ_three] at hbudget
    dsimp [a, b, c] at hbudget
    norm_num [h.1, h.2.1, h.2.2] at hbudget
    exact ⟨a, b, c, hne01.symm, hne12, hne02,
      h.2.1, h.1, h.2.2, hbudget⟩
  · right
    let a := E.symm 2
    let b := E.symm 0
    let c := E.symm 1
    have hbudget := orderSixtyFour_regular_crossComponent_mixedOwner_card_ge
      G hfree hreg m hm a b c hne02.symm hne12.symm hne01
    have hreindex := Equiv.sum_comp E.symm (fun source =>
      8 * m source * (m a * (m source - 1)) *
        (m b * (m source - 1)))
    rw [← hreindex, Fin.sum_univ_three] at hbudget
    dsimp [a, b, c] at hbudget
    norm_num [h.1, h.2.1, h.2.2] at hbudget
    exact ⟨a, b, c, hne02.symm, hne12.symm, hne01,
      h.2.2, h.1, h.2.1, hbudget⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_regular_threeComponents_crossBudget
