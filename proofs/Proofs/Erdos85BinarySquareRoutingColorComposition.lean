import Proofs.Erdos85BinarySquareCrossRoutingSymmetry
import Proofs.Erdos85BinarySquareSizeTwoCrossFactorCospectral

/-! # Composition of cross-routing colors -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Routing through one fixed defect component composes across a third
endpoint component. The leading term gives two copies of the direct routing
relation; the correction records one owner-factor step inside the routing
component. -/
theorem binarySquare_regular_sizeTwoRoutingColor_comp
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
    (he : e.supp.ncard = q * 2) :
    crossRoutingColorMatrix (K := ℤ) G hfree hce d *
        crossRoutingColorMatrix (K := ℤ) G hfree hef d =
      (2 : ℤ) • crossRoutingColorMatrix (K := ℤ) G hfree hcf d +
        (defectComponentCrossIncidenceMatrix (K := ℤ) G d c).transpose *
          (restrictedComponentOwnerGraph G d e).adjMatrix ℤ *
            defectComponentCrossIncidenceMatrix (K := ℤ) G d f := by
  let Bdc := defectComponentCrossIncidenceMatrix (K := ℤ) G d c
  let Bde := defectComponentCrossIncidenceMatrix (K := ℤ) G d e
  let Bdf := defectComponentCrossIncidenceMatrix (K := ℤ) G d f
  let A := (restrictedComponentOwnerGraph G d e).adjMatrix ℤ
  have hgram : Bde * Bde.transpose =
      Matrix.diagonal (fun _ => (2 : ℤ)) + A := by
    simpa [Bde, A] using
      binarySquare_regular_sizeTwoTarget_crossIncidence_mul_transpose
        G hfree hq hreg hcard d e he
  have hdiag : Matrix.diagonal (fun _ : d.supp => (2 : ℤ)) =
      (2 : ℤ) • (1 : Matrix d.supp d.supp ℤ) := by
    ext x y
    by_cases hxy : x = y <;> simp [hxy]
  rw [← transpose_cross_mul_cross_eq_routingColorMatrix G hfree hce d,
    ← transpose_cross_mul_cross_eq_routingColorMatrix G hfree hef d,
    ← transpose_cross_mul_cross_eq_routingColorMatrix G hfree hcf d]
  change (Bdc.transpose * Bde) * (Bde.transpose * Bdf) =
    (2 : ℤ) • (Bdc.transpose * Bdf) + Bdc.transpose * A * Bdf
  calc
    (Bdc.transpose * Bde) * (Bde.transpose * Bdf) =
        Bdc.transpose * (Bde * Bde.transpose) * Bdf := by
      simp only [Matrix.mul_assoc]
    _ = Bdc.transpose *
          (Matrix.diagonal (fun _ : d.supp => (2 : ℤ)) + A) * Bdf := by
      rw [hgram]
    _ = (2 : ℤ) • (Bdc.transpose * Bdf) +
          Bdc.transpose * A * Bdf := by
      rw [hdiag]
      rw [Matrix.mul_add, Matrix.add_mul]
      simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul]

end

end Erdos85
