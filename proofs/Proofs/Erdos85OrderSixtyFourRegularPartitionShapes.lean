import Proofs.Erdos85OrderSixtyFourRegularPartition

/-! # Exact shapes of the regular order-64 component partitions -/

open SimpleGraph

namespace Erdos85

/-- In the connected-defect branch, the unique normalized component size is
eight.  This is the explicit component-facing form of the `[8]` stratum. -/
theorem orderSixtyFour_regular_one_defectComponent_partition_shape
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 1) :
    ∃ (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
      (E : (secondOrderDefectGraph G).ConnectedComponent ≃ Fin 1),
      (∀ c, c.supp.ncard = 8 * m c) ∧
      m (E.symm 0) = 8 := by
  classical
  obtain ⟨m, hmSize, hmSum, _hmLower, _hcountLe⟩ :=
    orderSixtyFour_regular_defectComponent_partition_package G hfree hreg
  let E : (secondOrderDefectGraph G).ConnectedComponent ≃ Fin 1 :=
    Fintype.equivFinOfCardEq hcount
  have hreindex := Equiv.sum_comp E.symm m
  rw [Fin.sum_univ_one] at hreindex
  exact ⟨m, E, hmSize, hreindex.trans hmSum⟩

/-- With two defect components, an explicit reindexing displays exactly one
of the normalized shapes `[6,2]`, `[5,3]`, or `[4,4]`, up to swapping the two
components. -/
theorem orderSixtyFour_regular_two_defectComponents_partition_shape
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2) :
    ∃ (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
      (E : (secondOrderDefectGraph G).ConnectedComponent ≃ Fin 2),
      (∀ c, c.supp.ncard = 8 * m c) ∧
      ((m (E.symm 0) = 2 ∧ m (E.symm 1) = 6) ∨
       (m (E.symm 0) = 6 ∧ m (E.symm 1) = 2) ∨
       (m (E.symm 0) = 3 ∧ m (E.symm 1) = 5) ∨
       (m (E.symm 0) = 5 ∧ m (E.symm 1) = 3) ∨
       (m (E.symm 0) = 4 ∧ m (E.symm 1) = 4)) := by
  classical
  obtain ⟨m, hmSize, hmSum, hmLower, _hcountLe⟩ :=
    orderSixtyFour_regular_defectComponent_partition_package G hfree hreg
  let E : (secondOrderDefectGraph G).ConnectedComponent ≃ Fin 2 :=
    Fintype.equivFinOfCardEq hcount
  let a := m (E.symm 0)
  let b := m (E.symm 1)
  have hsum : a + b = 8 := by
    have hreindex := Equiv.sum_comp E.symm m
    rw [Fin.sum_univ_two] at hreindex
    exact hreindex.trans hmSum
  have ha : 2 ≤ a := hmLower (E.symm 0)
  have hb : 2 ≤ b := hmLower (E.symm 1)
  refine ⟨m, E, hmSize, ?_⟩
  change (a = 2 ∧ b = 6) ∨ (a = 6 ∧ b = 2) ∨
    (a = 3 ∧ b = 5) ∨ (a = 5 ∧ b = 3) ∨ (a = 4 ∧ b = 4)
  omega

/-- With three defect components, an explicit reindexing displays exactly
`[4,2,2]` or `[3,3,2]`, including all possible positions of the exceptional
component. -/
theorem orderSixtyFour_regular_three_defectComponents_partition_shape
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 3) :
    ∃ (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
      (E : (secondOrderDefectGraph G).ConnectedComponent ≃ Fin 3),
      (∀ c, c.supp.ncard = 8 * m c) ∧
      ((m (E.symm 0) = 4 ∧ m (E.symm 1) = 2 ∧ m (E.symm 2) = 2) ∨
       (m (E.symm 0) = 2 ∧ m (E.symm 1) = 4 ∧ m (E.symm 2) = 2) ∨
       (m (E.symm 0) = 2 ∧ m (E.symm 1) = 2 ∧ m (E.symm 2) = 4) ∨
       (m (E.symm 0) = 2 ∧ m (E.symm 1) = 3 ∧ m (E.symm 2) = 3) ∨
       (m (E.symm 0) = 3 ∧ m (E.symm 1) = 2 ∧ m (E.symm 2) = 3) ∨
       (m (E.symm 0) = 3 ∧ m (E.symm 1) = 3 ∧ m (E.symm 2) = 2)) := by
  classical
  obtain ⟨m, hmSize, hmSum, hmLower, _hcountLe⟩ :=
    orderSixtyFour_regular_defectComponent_partition_package G hfree hreg
  let E : (secondOrderDefectGraph G).ConnectedComponent ≃ Fin 3 :=
    Fintype.equivFinOfCardEq hcount
  let a := m (E.symm 0)
  let b := m (E.symm 1)
  let c := m (E.symm 2)
  have hsum : a + b + c = 8 := by
    have hreindex := Equiv.sum_comp E.symm m
    rw [Fin.sum_univ_three] at hreindex
    exact hreindex.trans hmSum
  have ha : 2 ≤ a := hmLower (E.symm 0)
  have hb : 2 ≤ b := hmLower (E.symm 1)
  have hc : 2 ≤ c := hmLower (E.symm 2)
  refine ⟨m, E, hmSize, ?_⟩
  change (a = 4 ∧ b = 2 ∧ c = 2) ∨
    (a = 2 ∧ b = 4 ∧ c = 2) ∨
    (a = 2 ∧ b = 2 ∧ c = 4) ∨
    (a = 2 ∧ b = 3 ∧ c = 3) ∨
    (a = 3 ∧ b = 2 ∧ c = 3) ∨
    (a = 3 ∧ b = 3 ∧ c = 2)
  omega

end Erdos85
