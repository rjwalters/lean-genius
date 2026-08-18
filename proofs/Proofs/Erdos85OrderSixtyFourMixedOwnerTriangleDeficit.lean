import Proofs.Erdos85BinarySquareMixedOwnerTriangleDeficitNonnegative

/-!
# Quantization of the mixed-owner triangle deficit at order 64

At `q = 8`, the binary square-order cubic congruence says that the literal
mixed-owner triangle deficit is a multiple of `32`.  Thus any independent
strict upper bound by `32` forces the deficit to vanish.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- For an eight-regular C4-free graph on 64 vertices, the mixed-owner
triangle deficit is quantized in units of 32. -/
theorem orderSixtyFour_thirtyTwo_dvd_mixedOwnerTriangleDeficit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = 8 * m c)
    (hsum : ∑ c, m c = 8) :
    (32 : ℤ) ∣ binarySquareMixedOwnerTriangleDeficit G := by
  have hdiv :=
    binarySquare_regular_six_mul_two_pow_pred_dvd_goodman_sub_mixedOwnerDeficit
      G hfree (k := 3) (by norm_num) hreg (by norm_num at hcard ⊢; exact hcard)
      m (by norm_num at hm ⊢; exact hm) (by norm_num at hsum ⊢; exact hsum)
  norm_num at hdiv
  obtain ⟨z, hz⟩ := hdiv
  refine ⟨910 - z, ?_⟩
  omega

/-- A sub-32 mixed-owner deficit at order 64 must be zero. -/
theorem orderSixtyFour_mixedOwnerTriangleDeficit_eq_zero_of_lt_thirtyTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = 8 * m c)
    (hsum : ∑ c, m c = 8)
    (hlt : binarySquareMixedOwnerTriangleDeficit G < 32) :
    binarySquareMixedOwnerTriangleDeficit G = 0 := by
  have hnonneg := binarySquareMixedOwnerTriangleDeficit_nonneg G hfree
    (by omega)
  obtain ⟨z, hz⟩ :=
    orderSixtyFour_thirtyTwo_dvd_mixedOwnerTriangleDeficit
      G hfree hreg hcard m hm hsum
  omega

end

end Erdos85

#print axioms
  Erdos85.orderSixtyFour_thirtyTwo_dvd_mixedOwnerTriangleDeficit
#print axioms
  Erdos85.orderSixtyFour_mixedOwnerTriangleDeficit_eq_zero_of_lt_thirtyTwo
