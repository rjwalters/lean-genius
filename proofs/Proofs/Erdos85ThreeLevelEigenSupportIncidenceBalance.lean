import Proofs.Erdos85ThreeLevelEigenSupportDegreeBalance

/-!
# Global incidence balance between extreme fibres

Summing the exact local degree-difference law gives the global edge-incidence
constraints used to classify the negative joint-eigenvalue support graphs.
-/

open SimpleGraph

namespace Erdos85

/-- Sum vertexwise extreme-fibre degree balance and double-count the cross
incidences. -/
theorem extreme_support_incidenceBalance_of_degreeBalance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Sp Sm : Finset V)
    (hp : ∀ u ∈ Sp,
      ((G.neighborFinset u).filter fun y => y ∈ Sp).card =
        ((G.neighborFinset u).filter fun y => y ∈ Sm).card + 2)
    (hm : ∀ u ∈ Sm,
      ((G.neighborFinset u).filter fun y => y ∈ Sm).card =
        ((G.neighborFinset u).filter fun y => y ∈ Sp).card + 2) :
    (∑ u ∈ Sp,
        (((G.neighborFinset u).filter fun y => y ∈ Sp).card : ℤ)) =
      (∑ u ∈ Sp,
        (((G.neighborFinset u).filter fun y => y ∈ Sm).card : ℤ)) +
        2 * (Sp.card : ℤ) ∧
    (∑ u ∈ Sm,
        (((G.neighborFinset u).filter fun y => y ∈ Sm).card : ℤ)) =
      (∑ u ∈ Sm,
        (((G.neighborFinset u).filter fun y => y ∈ Sp).card : ℤ)) +
        2 * (Sm.card : ℤ) ∧
    (∑ u ∈ Sp,
        (((G.neighborFinset u).filter fun y => y ∈ Sm).card : ℤ)) =
      ∑ u ∈ Sm,
        (((G.neighborFinset u).filter fun y => y ∈ Sp).card : ℤ) := by
  have hP : (∑ u ∈ Sp,
        (((G.neighborFinset u).filter fun y => y ∈ Sp).card : ℤ)) =
      (∑ u ∈ Sp,
        (((G.neighborFinset u).filter fun y => y ∈ Sm).card : ℤ)) +
        2 * (Sp.card : ℤ) := by
    calc
      _ = ∑ u ∈ Sp,
          ((((G.neighborFinset u).filter fun y => y ∈ Sm).card + 2 : ℕ) : ℤ) := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [hp u hu]
      _ = _ := by
        simp only [Nat.cast_add, Nat.cast_ofNat, Finset.sum_add_distrib,
          Finset.sum_const, nsmul_eq_mul]
        ring
  have hM : (∑ u ∈ Sm,
        (((G.neighborFinset u).filter fun y => y ∈ Sm).card : ℤ)) =
      (∑ u ∈ Sm,
        (((G.neighborFinset u).filter fun y => y ∈ Sp).card : ℤ)) +
        2 * (Sm.card : ℤ) := by
    calc
      _ = ∑ u ∈ Sm,
          ((((G.neighborFinset u).filter fun y => y ∈ Sp).card + 2 : ℕ) : ℤ) := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [hm u hu]
      _ = _ := by
        simp only [Nat.cast_add, Nat.cast_ofNat, Finset.sum_add_distrib,
          Finset.sum_const, nsmul_eq_mul]
        ring
  have hcross := sum_sum_filter_neighborFinset_comm
    G Sp Sm (fun _ _ => (1 : ℤ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hcross
  exact ⟨hP, hM, hcross⟩

/-- Campaign-facing global incidence balance from the standard local signed
joint-line interface. -/
theorem orderSixtyFour_sizeTwo_signedJoint_extreme_incidenceBalance_of_local
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ) (mu : ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = mu * s z) :
    let w := fun x => (G.adjMatrix ℤ).mulVec s x + 2 * s x
    let Sp := Finset.univ.filter fun x => w x = 2
    let Sm := Finset.univ.filter fun x => w x = -2
    (∑ u ∈ Sp,
        (((G.neighborFinset u).filter fun y => y ∈ Sp).card : ℤ)) =
      (∑ u ∈ Sp,
        (((G.neighborFinset u).filter fun y => y ∈ Sm).card : ℤ)) +
        2 * (Sp.card : ℤ) ∧
    (∑ u ∈ Sm,
        (((G.neighborFinset u).filter fun y => y ∈ Sm).card : ℤ)) =
      (∑ u ∈ Sm,
        (((G.neighborFinset u).filter fun y => y ∈ Sp).card : ℤ)) +
        2 * (Sm.card : ℤ) ∧
    (∑ u ∈ Sp,
        (((G.neighborFinset u).filter fun y => y ∈ Sm).card : ℤ)) =
      ∑ u ∈ Sm,
        (((G.neighborFinset u).filter fun y => y ∈ Sp).card : ℤ) := by
  dsimp only
  let w := fun x => (G.adjMatrix ℤ).mulVec s x + 2 * s x
  let Sp := Finset.univ.filter fun x => w x = 2
  let Sm := Finset.univ.filter fun x => w x = -2
  have hdeg := orderSixtyFour_sizeTwo_signedJoint_extreme_degreeBalance_of_local
    G hfree hreg hcard c hc s mu hs_out hs_in hH hD
  change (∀ u ∈ Sp,
      ((G.neighborFinset u).filter fun y => y ∈ Sp).card =
        ((G.neighborFinset u).filter fun y => y ∈ Sm).card + 2) ∧
    (∀ u ∈ Sm,
      ((G.neighborFinset u).filter fun y => y ∈ Sm).card =
        ((G.neighborFinset u).filter fun y => y ∈ Sp).card + 2) at hdeg
  exact extreme_support_incidenceBalance_of_degreeBalance
    G Sp Sm hdeg.1 hdeg.2

end Erdos85

#print axioms Erdos85.extreme_support_incidenceBalance_of_degreeBalance
#print axioms Erdos85.orderSixtyFour_sizeTwo_signedJoint_extreme_incidenceBalance_of_local
