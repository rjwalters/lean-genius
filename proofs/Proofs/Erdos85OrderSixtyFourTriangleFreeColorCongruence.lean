import Proofs.Erdos85OrderSixtyFourTriangleFreeColorOrder
import Proofs.Erdos85OrderSixtyFourTriangleFreeEdgeNecessity

/-!
# The mixed triangle-free color has order one modulo three

In the all-size-sixteen stratum every triangle-free degree is zero or two.
The global cubic trace says the total triangle-free degree is two modulo six,
so the number of degree-two vertices is one modulo three.  This applies to
the live mixed sector without assuming an all-triangle-free component.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The triangle-free colored support has cardinality `3k+1`. -/
theorem orderSixtyFour_allSixteen_triangleFreeColorOrder_eq_three_mul_add_one
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hsize : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16) :
    ∃ k : ℕ,
      (Finset.univ.filter fun x : Fin 64 =>
        (triangleFreeEdgeGraph G).degree x = 2).card = 3 * k + 1 := by
  let T := triangleFreeEdgeGraph G
  let C := (Finset.univ.filter fun x : Fin 64 => T.degree x = 2).card
  have hdegree (x : Fin 64) : T.degree x = 0 ∨ T.degree x = 2 := by
    simpa [T] using
      orderSixtyFour_allSixteen_triangleFree_degree_zero_or_two
        G hfree hreg hsize x
  have hsumNat : (∑ x : Fin 64, T.degree x) = 2 * C := by
    calc
      (∑ x : Fin 64, T.degree x) =
          ∑ x : Fin 64, if T.degree x = 2 then 2 else 0 := by
        apply Finset.sum_congr rfl
        intro x _hx
        rcases hdegree x with hx0 | hx2
        · simp [hx0]
        · simp [hx2]
      _ = 2 * C := by
        rw [← Finset.sum_filter]
        simp [C, Nat.mul_comm]
  obtain ⟨z, hz⟩ :=
    orderSixtyFour_regular_sum_triangleFreeDegrees_eq_six_mul_add_two
      G hfree hreg
  have hcast : (∑ x : Fin 64, (T.degree x : ℤ)) =
      ((∑ x : Fin 64, T.degree x : ℕ) : ℤ) := by
    push_cast
    rfl
  rw [hcast, hsumNat] at hz
  have hznonneg : 0 ≤ z := by omega
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hznonneg
  refine ⟨k, ?_⟩
  simpa [C, T] using (by omega : C = 3 * k + 1)

/-- Congruence form of the mixed-sector color-order constraint. -/
theorem orderSixtyFour_allSixteen_triangleFreeColorOrder_mod_three_eq_one
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hsize : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16) :
    (Finset.univ.filter fun x : Fin 64 =>
      (triangleFreeEdgeGraph G).degree x = 2).card % 3 = 1 := by
  obtain ⟨k, hk⟩ :=
    orderSixtyFour_allSixteen_triangleFreeColorOrder_eq_three_mul_add_one
      G hfree hreg hsize
  rw [hk]
  omega

end

end Erdos85

#print axioms
  Erdos85.orderSixtyFour_allSixteen_triangleFreeColorOrder_eq_three_mul_add_one
#print axioms
  Erdos85.orderSixtyFour_allSixteen_triangleFreeColorOrder_mod_three_eq_one
