import Proofs.Erdos85OrderSixtyFourRoutingColorResolution
import Proofs.Erdos85OrderSixtyFourFourComponentRoutingArray

/-! # Rectangular orthogonality of routing colors -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The `c × e` rectangular incidence matrix of one routing color. -/
def routingColorIncidenceMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    (d : (secondOrderDefectGraph G).ConnectedComponent) :
    Matrix c.supp e.supp ℤ := fun x z =>
  (routingColorBipartiteGraph G hfree c e hce d).adjMatrix ℤ
    (Sum.inl x) (Sum.inr z)

/-- The rectangular routing matrices resolve the all-ones matrix entrywise. -/
theorem sum_routingColorIncidenceMatrix_apply_eq_one
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
      routingColorIncidenceMatrix G hfree c e hce d x z) = 1 := by
  simpa [routingColorIncidenceMatrix, endpointCompleteBipartiteGraph,
    SimpleGraph.adjMatrix_apply] using
    (sum_routingColorBipartiteGraph_adjMatrix_apply_eq_complete
      G hfree c e hce (Sum.inl x) (Sum.inr z))

/-- Distinct rectangular routing colors are orthogonal for the Frobenius
inner product. -/
theorem routingColorIncidenceMatrix_frobenius_inner_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    {d₁ d₂ : (secondOrderDefectGraph G).ConnectedComponent} (hdd : d₁ ≠ d₂) :
    (∑ x : c.supp, ∑ z : e.supp,
      routingColorIncidenceMatrix G hfree c e hce d₁ x z *
        routingColorIncidenceMatrix G hfree c e hce d₂ x z) = 0 := by
  apply Finset.sum_eq_zero
  intro x _hx
  apply Finset.sum_eq_zero
  intro z _hz
  exact routingColorBipartiteGraph_adjMatrix_mul_apply_eq_zero
    G hfree c e hce hdd (Sum.inl x) (Sum.inr z)

/-- In the order-64 all-size-16 branch every routing matrix has exactly 64
ones, hence squared Frobenius norm 64. -/
theorem orderSixtyFour_fourSizeSixteenComponents_routingColor_frobenius_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hcard : Fintype.card V = 64)
    (hparts : ∀ d : (secondOrderDefectGraph G).ConnectedComponent,
      d.supp.ncard = 16)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    (d : (secondOrderDefectGraph G).ConnectedComponent) :
    (∑ x : c.supp, ∑ z : e.supp,
      routingColorIncidenceMatrix G hfree c e hce d x z *
        routingColorIncidenceMatrix G hfree c e hce d x z) = 64 := by
  have hrow : ∀ x : c.supp,
      (∑ z : e.supp,
        routingColorIncidenceMatrix G hfree c e hce d x z *
          routingColorIncidenceMatrix G hfree c e hce d x z) = 4 := by
    intro x
    have hclass :=
      orderSixtyFour_fourSizeSixteenComponents_routingColorClass_card_four
        G hfree hreg hcard hparts c e hce x d
    rw [show (∑ z : e.supp,
          routingColorIncidenceMatrix G hfree c e hce d x z *
            routingColorIncidenceMatrix G hfree c e hce d x z) =
          ((crossRoutingColorClass G hfree c e hce x d).card : ℤ) by
      calc
        (∑ z : e.supp,
            routingColorIncidenceMatrix G hfree c e hce d x z *
              routingColorIncidenceMatrix G hfree c e hce d x z) =
            ∑ z : e.supp,
              routingColorIncidenceMatrix G hfree c e hce d x z := by
                apply Finset.sum_congr rfl
                intro z _hz
                by_cases hadj :
                    (routingColorBipartiteGraph G hfree c e hce d).Adj
                      (Sum.inl x) (Sum.inr z)
                · simp [routingColorIncidenceMatrix,
                    SimpleGraph.adjMatrix_apply, hadj]
                · simp [routingColorIncidenceMatrix,
                    SimpleGraph.adjMatrix_apply, hadj]
        _ = ((crossRoutingColorClass G hfree c e hce x d).card : ℤ) := by
          simp only [routingColorIncidenceMatrix, SimpleGraph.adjMatrix_apply]
          rw [Finset.sum_boole]
          have heq : (Finset.univ.filter fun z : e.supp =>
              (routingColorBipartiteGraph G hfree c e hce d).Adj
                (Sum.inl x) (Sum.inr z)) =
              crossRoutingColorClass G hfree c e hce x d := by
            ext z
            simp [crossRoutingColorClass, routingColorBipartiteGraph]
          rw [heq]]
    exact_mod_cast hclass
  calc
    (∑ x : c.supp, ∑ z : e.supp,
        routingColorIncidenceMatrix G hfree c e hce d x z *
          routingColorIncidenceMatrix G hfree c e hce d x z) =
        ∑ _x : c.supp, (4 : ℤ) := by
          apply Finset.sum_congr rfl
          intro x _hx
          exact hrow x
    _ = 64 := by
      have hc : Fintype.card c.supp = 16 := by
        rw [Set.fintypeCard_eq_ncard]
        exact hparts c
      simp [hc]

end

end Erdos85
