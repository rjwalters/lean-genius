import Proofs.Erdos85BinarySquareMixedOwnerTriangleDeficitDivisibility

/-!
# Residual congruence in the order-64 mixed mu=3 sector

The binary square-order algebra quantizes the mixed-owner triangle deficit in
units of 32.  In the all-triangle `mu = 3` grid, the ambient cross-triangle
contribution is expected to be exactly 48.  This file isolates the exact
consumer: once the remaining combinatorial bookkeeping proves
`deficit = 48 + R`, the residual count must be congruent to 16 modulo 32.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Pure arithmetic form of the `48 + R` residual reduction. -/
theorem thirtyTwo_dvd_residual_sub_sixteen_of_dvd_deficit_of_eq_fortyEight_add
    {deficit residual : ℤ}
    (hdiv : (32 : ℤ) ∣ deficit)
    (hdecomp : deficit = 48 + residual) :
    (32 : ℤ) ∣ residual - 16 := by
  obtain ⟨z, hz⟩ := hdiv
  refine ⟨z - 2, ?_⟩
  rw [hdecomp] at hz
  omega

/-- **Order-64 mixed-grid residual socket.**  Any decomposition of the
mixed-owner deficit as the forced 48 cross triangles plus a residual count
places that residual in the congruence class 16 modulo 32. -/
theorem orderSixtyFour_mixedOwnerResidual_sub_sixteen_dvd
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
    (residual : ℤ)
    (hdecomp : binarySquareMixedOwnerTriangleDeficit G = 48 + residual) :
    (32 : ℤ) ∣ residual - 16 := by
  have hdiv : (32 : ℤ) ∣ binarySquareMixedOwnerTriangleDeficit G := by
    simpa using
      (binarySquare_regular_two_pow_pred_dvd_mixedOwnerTriangleDeficit
        G hfree (k := 3) (by norm_num)
          (by simpa using hreg)
          (by norm_num at hcard ⊢; exact hcard)
          m (by simpa using hm) (by simpa using hsum))
  exact thirtyTwo_dvd_residual_sub_sixteen_of_dvd_deficit_of_eq_fortyEight_add
    hdiv hdecomp

end

end Erdos85

#print axioms
  Erdos85.thirtyTwo_dvd_residual_sub_sixteen_of_dvd_deficit_of_eq_fortyEight_add
#print axioms Erdos85.orderSixtyFour_mixedOwnerResidual_sub_sixteen_dvd
