import Proofs.Erdos85OrderSixtyFourRoutingColorRectangularOrthogonality

/-! # Routing colors as cross-incidence products -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The rectangular routing-color matrix is exactly the product of its two
cross-incidence blocks through the intermediate component. -/
theorem routingColorIncidenceMatrix_eq_transpose_cross_mul_cross
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    (d : (secondOrderDefectGraph G).ConnectedComponent) :
    routingColorIncidenceMatrix G hfree c e hce d =
      (defectComponentCrossIncidenceMatrix (K := ℤ) G d c).transpose *
        defectComponentCrossIncidenceMatrix (K := ℤ) G d e := by
  ext x z
  rw [transpose_cross_mul_cross_apply_eq_ite_intermediate
    G hfree hce x z d]
  by_cases hd : d = crossIntermediateComponent G hfree hce x z
  · simp [routingColorIncidenceMatrix, routingColorBipartiteGraph,
      SimpleGraph.adjMatrix_apply, hd]
  · simp [routingColorIncidenceMatrix, routingColorBipartiteGraph,
      SimpleGraph.adjMatrix_apply, hd]

/-- Every cross-incidence product entry is Boolean. -/
theorem transpose_cross_mul_cross_apply_eq_zero_or_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    (d : (secondOrderDefectGraph G).ConnectedComponent)
    (x : c.supp) (z : e.supp) :
    ((defectComponentCrossIncidenceMatrix (K := ℤ) G d c).transpose *
      defectComponentCrossIncidenceMatrix (K := ℤ) G d e) x z = 0 ∨
    ((defectComponentCrossIncidenceMatrix (K := ℤ) G d c).transpose *
      defectComponentCrossIncidenceMatrix (K := ℤ) G d e) x z = 1 := by
  rw [transpose_cross_mul_cross_apply_eq_ite_intermediate
    G hfree hce x z d]
  split <;> simp

/-- Summing the incidence products over all intermediate components gives
exactly one route for every endpoint pair. -/
theorem sum_transpose_cross_mul_cross_apply_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    (x : c.supp) (z : e.supp) :
    (∑ d : (secondOrderDefectGraph G).ConnectedComponent,
      ((defectComponentCrossIncidenceMatrix (K := ℤ) G d c).transpose *
        defectComponentCrossIncidenceMatrix (K := ℤ) G d e) x z) = 1 := by
  calc
    (∑ d : (secondOrderDefectGraph G).ConnectedComponent,
        ((defectComponentCrossIncidenceMatrix (K := ℤ) G d c).transpose *
          defectComponentCrossIncidenceMatrix (K := ℤ) G d e) x z) =
      ∑ d : (secondOrderDefectGraph G).ConnectedComponent,
        routingColorIncidenceMatrix G hfree c e hce d x z := by
          apply Finset.sum_congr rfl
          intro d _hd
          exact congrFun (congrFun
            (routingColorIncidenceMatrix_eq_transpose_cross_mul_cross
              G hfree c e hce d).symm x) z
    _ = 1 := sum_routingColorIncidenceMatrix_apply_eq_one
      G hfree c e hce x z

/-- Products through distinct intermediate components are Frobenius
orthogonal. -/
theorem transpose_cross_mul_cross_frobenius_inner_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    {d₁ d₂ : (secondOrderDefectGraph G).ConnectedComponent} (hdd : d₁ ≠ d₂) :
    (∑ x : c.supp, ∑ z : e.supp,
      ((defectComponentCrossIncidenceMatrix (K := ℤ) G d₁ c).transpose *
          defectComponentCrossIncidenceMatrix (K := ℤ) G d₁ e) x z *
        ((defectComponentCrossIncidenceMatrix (K := ℤ) G d₂ c).transpose *
          defectComponentCrossIncidenceMatrix (K := ℤ) G d₂ e) x z) = 0 := by
  simpa only [routingColorIncidenceMatrix_eq_transpose_cross_mul_cross] using
    (routingColorIncidenceMatrix_frobenius_inner_eq_zero
      G hfree c e hce hdd)

end

end Erdos85
