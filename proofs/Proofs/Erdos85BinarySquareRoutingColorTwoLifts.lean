import Proofs.Erdos85BinarySquareRoutingColorComposition

/-! # Two same-color lifts of every routed endpoint pair -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem routingColorMatrix_mul_apply_eq_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {c e f : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (hef : e ≠ f)
    (d : (secondOrderDefectGraph G).ConnectedComponent)
    (x : c.supp) (w : f.supp) :
    (crossRoutingColorMatrix (K := ℤ) G hfree hce d *
        crossRoutingColorMatrix (K := ℤ) G hfree hef d) x w =
      (((Finset.univ : Finset e.supp).filter fun z =>
        d = crossIntermediateComponent G hfree hce x z ∧
        d = crossIntermediateComponent G hfree hef z w).card : ℤ) := by
  rw [Matrix.mul_apply]
  simp only [crossRoutingColorMatrix]
  calc
    (∑ z : e.supp,
      (if d = crossIntermediateComponent G hfree hce x z then (1 : ℤ) else 0) *
        if d = crossIntermediateComponent G hfree hef z w then 1 else 0) =
        ∑ z : e.supp, if
          d = crossIntermediateComponent G hfree hce x z ∧
          d = crossIntermediateComponent G hfree hef z w
            then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro z _hz
      by_cases hxz : d = crossIntermediateComponent G hfree hce x z <;>
        by_cases hzw : d = crossIntermediateComponent G hfree hef z w <;>
          simp [hxz, hzw]
    _ = _ := by rw [Finset.sum_boole]

/-- If the direct `c`-to-`f` endpoint pair is routed through `d`, then through
every size-two intermediate endpoint component `e` there are at least two
vertices for which both legs are routed through the same `d`. -/
theorem binarySquare_regular_sizeTwoRoutingColor_two_le_lift_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f)
    (he : e.supp.ncard = q * 2)
    (x : c.supp) (w : f.supp)
    (hroute : d = crossIntermediateComponent G hfree hcf x w) :
    2 ≤ ((Finset.univ : Finset e.supp).filter fun z =>
      d = crossIntermediateComponent G hfree hce x z ∧
      d = crossIntermediateComponent G hfree hef z w).card := by
  let Bdc := defectComponentCrossIncidenceMatrix (K := ℤ) G d c
  let Bdf := defectComponentCrossIncidenceMatrix (K := ℤ) G d f
  let A := (restrictedComponentOwnerGraph G d e).adjMatrix ℤ
  have hcorrection : 0 ≤ (Bdc.transpose * A * Bdf) x w := by
    rw [Matrix.mul_apply]
    apply Finset.sum_nonneg
    intro i _hi
    apply mul_nonneg
    · rw [Matrix.mul_apply]
      apply Finset.sum_nonneg
      intro j _hj
      apply mul_nonneg
      · change 0 ≤ if G.Adj j.1 x.1 then (1 : ℤ) else 0
        split <;> norm_num
      · change 0 ≤ if (restrictedComponentOwnerGraph G d e).Adj j i
          then (1 : ℤ) else 0
        split <;> norm_num
    · change 0 ≤ if G.Adj i.1 w.1 then (1 : ℤ) else 0
      split <;> norm_num
  have hcomp := congrArg (fun M : Matrix c.supp f.supp ℤ => M x w)
    (binarySquare_regular_sizeTwoRoutingColor_comp
      G hfree hq hreg hcard c d e f hce hef hcf he)
  rw [routingColorMatrix_mul_apply_eq_card G hfree hce hef d x w] at hcomp
  have hdirect :
      ((2 : ℤ) • crossRoutingColorMatrix (K := ℤ) G hfree hcf d) x w = 2 := by
    simp [crossRoutingColorMatrix, hroute]
  rw [Matrix.add_apply, hdirect] at hcomp
  change (((Finset.univ : Finset e.supp).filter fun z =>
      d = crossIntermediateComponent G hfree hce x z ∧
      d = crossIntermediateComponent G hfree hef z w).card : ℤ) =
        2 + (Bdc.transpose * A * Bdf) x w at hcomp
  omega

end

end Erdos85
