import Proofs.Erdos85MuThreeMixedGridResidualSector

/-!
# Residual commutation on the mixed-grid zero sector

The residual graph is a polynomial in the exterior adjacency operator after
restriction to simultaneous zero row and column sums.  Consequently that
sector is residual-invariant, and the exterior and residual operators commute
there without any ambient pairwise-commutation hypothesis.
-/

open SimpleGraph

namespace Erdos85

/-- The square-residual adjacency operator preserves the zero row/column
sector. -/
theorem MuThreeMixedGridCode.zeroRowColumn_residual_invariant
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {f : muThreeMixedCell K → ℤ}
    (hf : MixedGridZeroRowColumn K f) :
    MixedGridZeroRowColumn K
      (((mixedGridSquareResidualGraph K C).adjMatrix ℤ).mulVec f) := by
  rw [MuThreeMixedGridCode.residual_adjMatrix_mulVec_eq_on_zeroSector
    H K C code hf]
  have hf1 := MuThreeMixedGridCode.zeroRowColumn_adjMatrix_invariant
    H K C code hf
  have hf2 := MuThreeMixedGridCode.zeroRowColumn_adjMatrix_invariant
    H K C code hf1
  exact MixedGridZeroRowColumn.sub (MixedGridZeroRowColumn.smul hf 7) hf2

/-- **Restricted residual commutation.**  On the zero row/column sector,
`A_C A_D f = A_D A_C f`. -/
theorem MuThreeMixedGridCode.adjMatrix_residual_commute_on_zeroSector
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {f : muThreeMixedCell K → ℤ}
    (hf : MixedGridZeroRowColumn K f) :
    (C.adjMatrix ℤ).mulVec
        (((mixedGridSquareResidualGraph K C).adjMatrix ℤ).mulVec f) =
      ((mixedGridSquareResidualGraph K C).adjMatrix ℤ).mulVec
        ((C.adjMatrix ℤ).mulVec f) := by
  let A := C.adjMatrix ℤ
  let D := (mixedGridSquareResidualGraph K C).adjMatrix ℤ
  have hCf := MuThreeMixedGridCode.zeroRowColumn_adjMatrix_invariant
    H K C code hf
  have hDf := MuThreeMixedGridCode.residual_adjMatrix_mulVec_eq_on_zeroSector
    H K C code hf
  have hDCf := MuThreeMixedGridCode.residual_adjMatrix_mulVec_eq_on_zeroSector
    H K C code hCf
  change A.mulVec (D.mulVec f) = D.mulVec (A.mulVec f)
  rw [hDf, hDCf, Matrix.mulVec_sub, Matrix.mulVec_smul]

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.zeroRowColumn_residual_invariant
#print axioms
  Erdos85.MuThreeMixedGridCode.adjMatrix_residual_commute_on_zeroSector
