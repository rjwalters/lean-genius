import Proofs.Erdos85OrderSixtyFourFourComponentRoutingArray

/-! # Matrix certificate for the four-color order-64 routing system -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The zero-one matrix of endpoint pairs assigned routing color `k`. -/
def orderSixtyFourRoutingMatrix
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (k : Fin 4) : Matrix c.supp e.supp ℤ :=
  crossRoutingColorMatrix G hfree hce
    ((orderSixtyFourDefectComponentEquivFinFour G hcount).symm k)

/-- Matrix entries are precisely the indicator of the corresponding value of
the finite routing array. -/
theorem orderSixtyFourRoutingMatrix_apply
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (k : Fin 4) (x : c.supp) (z : e.supp) :
    orderSixtyFourRoutingMatrix G hfree hcount hce k x z =
      if orderSixtyFourRoutingArray G hfree hcount hce x z = k
      then 1 else 0 := by
  let E := orderSixtyFourDefectComponentEquivFinFour G hcount
  simp only [orderSixtyFourRoutingMatrix, crossRoutingColorMatrix,
    orderSixtyFourRoutingArray]
  by_cases h : E (crossIntermediateComponent G hfree hce x z) = k
  · rw [if_pos h]
    rw [if_pos]
    calc
      E.symm k = E.symm (E (crossIntermediateComponent G hfree hce x z)) :=
        congrArg E.symm h.symm
      _ = crossIntermediateComponent G hfree hce x z :=
        E.symm_apply_apply _
  · rw [if_neg h]
    rw [if_neg]
    intro heq
    apply h
    exact E.symm.injective (by simpa using heq.symm)

/-- Each routing matrix retains its exact factorization through the two
2-regular cross-incidence blocks indexed by its intermediate component. -/
theorem orderSixtyFourRoutingMatrix_eq_cross_factorization
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (k : Fin 4) :
    orderSixtyFourRoutingMatrix G hfree hcount hce k =
      (defectComponentCrossIncidenceMatrix (K := ℤ) G
          ((orderSixtyFourDefectComponentEquivFinFour G hcount).symm k) c).transpose *
        defectComponentCrossIncidenceMatrix (K := ℤ) G
          ((orderSixtyFourDefectComponentEquivFinFour G hcount).symm k) e := by
  symm
  exact transpose_cross_mul_cross_eq_routingColorMatrix
    G hfree hce _

/-- Reversing the endpoint pair transposes every routing matrix without
permuting its `Fin 4` color. -/
theorem orderSixtyFourRoutingMatrix_transpose
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (k : Fin 4) :
    (orderSixtyFourRoutingMatrix G hfree hcount hce k).transpose =
      orderSixtyFourRoutingMatrix G hfree hcount hce.symm k := by
  exact crossRoutingColorMatrix_transpose G hfree hce _

/-- The four routing matrices partition the all-ones matrix. -/
theorem sum_orderSixtyFourRoutingMatrix_eq_ones
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) :
    (∑ k : Fin 4, orderSixtyFourRoutingMatrix G hfree hcount hce k) =
      Matrix.of fun _ _ => (1 : ℤ) := by
  ext x z
  simp only [Matrix.sum_apply, Matrix.of_apply,
    orderSixtyFourRoutingMatrix_apply G hfree hcount hce]
  rw [Finset.sum_eq_single
    (orderSixtyFourRoutingArray G hfree hcount hce x z)]
  · simp
  · intro b _hb hne
    rw [if_neg]
    intro h
    exact hne h.symm
  · simp

/-- Every routing matrix has constant row sum four. -/
theorem orderSixtyFourRoutingMatrix_row_sum_eq_four
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (k : Fin 4) (x : c.supp) :
    (∑ z : e.supp,
      orderSixtyFourRoutingMatrix G hfree hcount hce k x z) = 4 := by
  simp_rw [orderSixtyFourRoutingMatrix_apply]
  rw [Finset.sum_boole]
  exact_mod_cast orderSixtyFourRoutingArray_row_color_card_eq_four
    G hfree hreg hcount hce x k

/-- Every routing matrix has constant column sum four. -/
theorem orderSixtyFourRoutingMatrix_column_sum_eq_four
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (k : Fin 4) (z : e.supp) :
    (∑ x : c.supp,
      orderSixtyFourRoutingMatrix G hfree hcount hce k x z) = 4 := by
  simp_rw [orderSixtyFourRoutingMatrix_apply]
  rw [Finset.sum_boole]
  exact_mod_cast orderSixtyFourRoutingArray_column_color_card_eq_four
    G hfree hreg hcount hce z k

/-- Distinct routing colors have disjoint supports, expressed entrywise as
vanishing products. -/
theorem orderSixtyFourRoutingMatrix_mul_apply_eq_zero_of_ne
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) {k l : Fin 4} (hkl : k ≠ l)
    (x : c.supp) (z : e.supp) :
    orderSixtyFourRoutingMatrix G hfree hcount hce k x z *
      orderSixtyFourRoutingMatrix G hfree hcount hce l x z = 0 := by
  rw [orderSixtyFourRoutingMatrix_apply,
    orderSixtyFourRoutingMatrix_apply]
  by_cases hk : orderSixtyFourRoutingArray G hfree hcount hce x z = k
  · rw [if_pos hk, if_neg]
    · norm_num
    · intro hl
      exact hkl (hk.symm.trans hl)
  · simp [hk]

end

end Erdos85
