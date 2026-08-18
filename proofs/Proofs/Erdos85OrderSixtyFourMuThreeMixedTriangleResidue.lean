import Proofs.Erdos85BinarySquareCrossTriangleLiteralMixed

/-!
# Order-64 residue after the mu-three ambient triangle count

The all-triangle-free `mu = 3` mixed-grid analysis predicts 48 unoriented,
hence 288 ordered, multi-component ambient triangles.  This file isolates the
arithmetic consumer: that count forces the ordered nonambient mixed census to
be congruent to 96 modulo 192 (equivalently 16 modulo 32 after dividing the
six orientations).
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem orderSixtyFour_mixedNonambient_add_96_dvd_192_of_multiComponentAmbient_eq_288
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
    (hmulti : (multiComponentAmbientCyclicTriangles G).card = 288) :
    (192 : ℤ) ∣
      ((literalMixedOwnerNonambientCyclicTriples G).card : ℤ) + 96 := by
  have hdiv :=
    binarySquare_regular_six_mul_two_pow_pred_dvd_multiComponentAmbient_add_mixedNonambient
      G hfree (k := 3) (by norm_num) hreg
        (by norm_num at hcard ⊢; exact hcard) m
        (by norm_num at hm ⊢; exact hm)
        (by norm_num at hsum ⊢; exact hsum)
  norm_num [hmulti] at hdiv
  obtain ⟨z, hz⟩ := hdiv
  refine ⟨z - 1, ?_⟩
  omega

end

end Erdos85

#print axioms
  Erdos85.orderSixtyFour_mixedNonambient_add_96_dvd_192_of_multiComponentAmbient_eq_288
