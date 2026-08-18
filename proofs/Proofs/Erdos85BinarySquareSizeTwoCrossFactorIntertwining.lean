import Proofs.Erdos85BinarySquareSizeTwoCrossFactorCospectral

/-! # Paired cross-block factors intertwine

The cross-incidence matrix does more than prove that the two restricted owner
factors are cospectral: it intertwines their adjacency actions exactly.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- For two size-two defect components, their cross-incidence matrix
intertwines the paired restricted owner adjacency matrices. -/
theorem binarySquare_regular_twoSizeTwoParts_crossIncidence_intertwines_owner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2) :
    (restrictedComponentOwnerGraph G c d).adjMatrix ℤ *
        defectComponentCrossIncidenceMatrix (K := ℤ) G c d =
      defectComponentCrossIncidenceMatrix (K := ℤ) G c d *
        (restrictedComponentOwnerGraph G d c).adjMatrix ℤ := by
  let B := defectComponentCrossIncidenceMatrix (K := ℤ) G c d
  let A := (restrictedComponentOwnerGraph G c d).adjMatrix ℤ
  let C := (restrictedComponentOwnerGraph G d c).adjMatrix ℤ
  let Ic : Matrix c.supp c.supp ℤ := Matrix.diagonal fun _ => 2
  let Id : Matrix d.supp d.supp ℤ := Matrix.diagonal fun _ => 2
  have hrow : B * B.transpose = Ic + A := by
    simpa [B, A, Ic] using
      binarySquare_regular_sizeTwoTarget_crossIncidence_mul_transpose
        G hfree hq hreg hcard c d hd
  have hcol : B.transpose * B = Id + C := by
    simpa [B, C, Id] using
      binarySquare_regular_twoSizeTwoParts_transpose_crossIncidence_mul_self
        G hfree hq hreg hcard c d hc
  change A * B = B * C
  calc
    A * B = (Ic + A) * B - Ic * B := by
      rw [Matrix.add_mul]
      abel
    _ = (B * B.transpose) * B - Ic * B := by rw [hrow]
    _ = B * (B.transpose * B) - B * Id := by
      rw [Matrix.mul_assoc]
      congr 1
      ext x y
      simp [Ic, Id, Matrix.mul_apply, Matrix.diagonal]
      ring
    _ = B * (Id + C) - B * Id := by rw [hcol]
    _ = B * C := by
      rw [Matrix.mul_add]
      abel

end

end Erdos85
