import Proofs.Erdos85BinaryTransportResidualGraph

/-!
# Residual transport of a two-pole potential

This is the exact algebraic first line of `(73rnz_bq)`.  If `Ax=h`, then
the polynomial transport part `H=A²(A+I)` sends `x` to `A²h+Ah`.  Therefore
the residual graph `K=H△T` sends `x` to `Tx+A²h+Ah`.
-/

open SimpleGraph

namespace Erdos85

/-- The correction carried by the two-pole syndrome itself. -/
def twoPoleResidualCorrection
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (h : V → ZMod 2) : V → ZMod 2 :=
  let M := A.adjMatrix (ZMod 2)
  (M * M).mulVec h + M.mulVec h

/-- The polynomial transport matrix sends a potential to `A²h+Ah`, where
`h=Ax`. -/
theorem binaryTransportMatrix_mulVec_of_adjMatrix_mulVec_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (x h : V → ZMod 2)
    (hAx : (A.adjMatrix (ZMod 2)).mulVec x = h) :
    (binaryTransportMatrix A).mulVec x =
      twoPoleResidualCorrection A h := by
  let M := A.adjMatrix (ZMod 2)
  have hplus : (M + 1).mulVec x = h + x := by
    rw [Matrix.add_mulVec, hAx, Matrix.one_mulVec]
  have hsqx : (M * M).mulVec x = M.mulVec h := by
    rw [← Matrix.mulVec_mulVec, hAx]
  change (M * M * (M + 1)).mulVec x =
    (M * M).mulVec h + M.mulVec h
  calc
    (M * M * (M + 1)).mulVec x =
        (M * M).mulVec ((M + 1).mulVec x) := by
      rw [Matrix.mulVec_mulVec]
    _ = (M * M).mulVec (h + x) := by rw [hplus]
    _ = (M * M).mulVec h + (M * M).mulVec x := by
      rw [Matrix.mulVec_add]
    _ = (M * M).mulVec h + M.mulVec h := by rw [hsqx]

/-- **Two-pole residual transport (`73rnz_bq`, first equality).** -/
theorem binaryTransportResidualGraph_mulVec_of_adjMatrix_mulVec_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ u, A.degree u = q)
    (x h : V → ZMod 2)
    (hAx : (A.adjMatrix (ZMod 2)).mulVec x = h) :
    ((binaryTransportResidualGraph A hq hreg).adjMatrix (ZMod 2)).mulVec x =
      ((triangleFreeEdgeGraph A).adjMatrix (ZMod 2)).mulVec x +
        twoPoleResidualCorrection A h := by
  let H := binaryTransportSupportGraph A hq hreg
  let T := triangleFreeEdgeGraph A
  have hKmatrix :
      (binaryTransportResidualGraph A hq hreg).adjMatrix (ZMod 2) =
        H.adjMatrix (ZMod 2) + T.adjMatrix (ZMod 2) := by
    unfold binaryTransportResidualGraph graphF2SymmetricDifference
    exact f2MatrixSupportGraph_adjMatrix_eq _ _ _
  have hHmatrix : H.adjMatrix (ZMod 2) = binaryTransportMatrix A :=
    f2MatrixSupportGraph_adjMatrix_eq _ _ _
  rw [hKmatrix, Matrix.add_mulVec, hHmatrix,
    binaryTransportMatrix_mulVec_of_adjMatrix_mulVec_eq A x h hAx]
  exact add_comm _ _

/-- Coordinate form, suitable for retaining endpoint labels in the
two-pole correction alphabet. -/
theorem binaryTransportResidualGraph_mulVec_apply_of_twoPolePotential
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ u, A.degree u = q)
    (x : V → ZMod 2) (pole₁ pole₂ center : V)
    (hAx : (A.adjMatrix (ZMod 2)).mulVec x =
      Pi.single pole₁ 1 + Pi.single pole₂ 1) :
    ((binaryTransportResidualGraph A hq hreg).adjMatrix (ZMod 2)).mulVec x center =
      ((triangleFreeEdgeGraph A).adjMatrix (ZMod 2)).mulVec x center +
        twoPoleResidualCorrection A
          (Pi.single pole₁ 1 + Pi.single pole₂ 1) center := by
  exact congrFun
    (binaryTransportResidualGraph_mulVec_of_adjMatrix_mulVec_eq
      A hq hreg x _ hAx) center

end Erdos85

#print axioms Erdos85.binaryTransportMatrix_mulVec_of_adjMatrix_mulVec_eq
#print axioms Erdos85.binaryTransportResidualGraph_mulVec_of_adjMatrix_mulVec_eq
#print axioms Erdos85.binaryTransportResidualGraph_mulVec_apply_of_twoPolePotential
