import Proofs.Erdos85MuThreeAllTriangleTenSixPerCellCnf
import Proofs.Erdos85MuThreeAllTfTenSixFiberMargin
import Proofs.Erdos85MuThreeMixedGridPerCellColumnMates

/-!
# Graph semantics for the all-triangle C10+C6 per-cell certificate

`tenSixHole` is the fixed bipartite C10+C6 relation used by the external
DIMACS generator.  This file specializes the abstract mixed-grid per-cell
laws to those coordinates.  The resulting equations are the semantic input
for the Boolean `D` variables: the residual degree in every foreign row or
column is determined by the fixed cycle overlap and by whether the crossing
cell is occupied.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the fixed C10+C6 coordinates, `mixedGridHCommonColumns` is the
row-overlap function used by the certificate generator. -/
theorem mixedGridHCommonColumns_tenSix (x x' : Fin 8) :
    (mixedGridHCommonColumns tenSixHole x x').card =
      tenSixRowOverlap x x' := by
  rfl

/-- Column-dual identification of the fixed overlap function. -/
theorem mixedGridHCommonRows_tenSix (y y' : Fin 8) :
    (mixedGridHCommonRows tenSixHole y y').card =
      tenSixColumnOverlap y y' := by
  rfl

/-- Fixed-coordinate row semantics of every `D` block emitted by
`percell_D_alltri_tensix.py`. -/
theorem MuThreeMixedGridCode.tenSix_residualMatesInRow
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode tenSixHole K C)
    (u : muThreeMixedCell K) (x : Fin 8) (hxu : x ≠ u.1.1) :
    (mixedGridGraphMatesInRow (mixedGridSquareResidualGraph K C) u x).card +
      tenSixRowOverlap u.1.1 x +
      (if K x u.1.2 then 0 else 1) = 2 := by
  simpa [mixedGridHCommonColumns_tenSix] using
    code.residualMatesInRow_add_overlap_add_indicator
      tenSixHole K C u x hxu

/-- Fixed-coordinate column semantics of every `D` block emitted by
`percell_D_alltri_tensix.py`. -/
theorem MuThreeMixedGridCode.tenSix_residualMatesInColumn
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode tenSixHole K C)
    (u : muThreeMixedCell K) (y : Fin 8) (hyu : y ≠ u.1.2) :
    (mixedGridGraphMatesInColumn (mixedGridSquareResidualGraph K C) u y).card +
      tenSixColumnOverlap u.1.2 y +
      (if K u.1.1 y then 0 else 1) = 2 := by
  simpa [mixedGridHCommonRows_tenSix] using
    code.residualMatesInColumn_add_overlap_add_indicator
      tenSixHole K C u y hyu

/-- The graph hypotheses also supply the two-hole row constraints of the
certificate without any additional census assumption. -/
theorem MuThreeMixedGridCode.tenSix_holesInRow_card
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode tenSixHole K C) (x : Fin 8) :
    ((Finset.univ : Finset (Fin 8)).filter fun y => K x y).card = 2 :=
  code.K_twoRegular.1 x

/-- Column-dual two-hole constraint. -/
theorem MuThreeMixedGridCode.tenSix_holesInColumn_card
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode tenSixHole K C) (y : Fin 8) :
    ((Finset.univ : Finset (Fin 8)).filter fun x => K x y).card = 2 :=
  code.K_twoRegular.2 y

end

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.tenSix_residualMatesInRow
#print axioms Erdos85.MuThreeMixedGridCode.tenSix_residualMatesInColumn
#print axioms Erdos85.MuThreeMixedGridCode.tenSix_holesInRow_card
#print axioms Erdos85.MuThreeMixedGridCode.tenSix_holesInColumn_card
