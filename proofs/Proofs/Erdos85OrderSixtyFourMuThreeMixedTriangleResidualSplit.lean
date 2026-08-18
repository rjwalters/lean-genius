import Proofs.Erdos85BinarySquareCrossTriangleLiteralMixed

/-!
# Corrected order-64 mixed-triangle residual socket

The chosen all-triangle-free component supplies 48 unoriented (288 ordered)
multi-component ambient triangles, but further ambient mixed triangles may
remain.  This file retains that additional ambient residual instead of
incorrectly setting the entire global ambient census equal to 288.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Corrected residual congruence.**  Write the global ordered
multi-component ambient census as `288 + 6A`, and the ordered nonambient
mixed-owner census as `6B`.  At the binary order-64 boundary their combined
divisibility forces `A + B ≡ 16 (mod 32)`.

Here `A` includes all mixed ambient triangles not incident to the selected
all-triangle-free component; it must not be silently discarded. -/
theorem orderSixtyFour_mixedTriangleResidual_sum_sub_sixteen_dvd
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
    (A B : ℕ)
    (hmulti : (multiComponentAmbientCyclicTriangles G).card = 288 + 6 * A)
    (hnonambient :
      (literalMixedOwnerNonambientCyclicTriples G).card = 6 * B) :
    (32 : ℤ) ∣ (A : ℤ) + (B : ℤ) - 16 := by
  have hdiv :=
    binarySquare_regular_six_mul_two_pow_pred_dvd_multiComponentAmbient_add_mixedNonambient
      G hfree (k := 3) (by norm_num) hreg
        (by norm_num at hcard ⊢; exact hcard) m
        (by norm_num at hm ⊢; exact hm)
        (by norm_num at hsum ⊢; exact hsum)
  rw [hmulti, hnonambient] at hdiv
  norm_num at hdiv
  obtain ⟨z, hz⟩ := hdiv
  refine ⟨z - 2, ?_⟩
  omega

end

end Erdos85

#print axioms
  Erdos85.orderSixtyFour_mixedTriangleResidual_sum_sub_sixteen_dvd
