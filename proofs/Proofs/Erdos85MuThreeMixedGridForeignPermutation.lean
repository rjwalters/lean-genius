import Proofs.Erdos85MuThreeMixedGridForeignFiberEquiv

/-!
# The canonical foreign row-to-column permutation

The two canonical descriptions of a cell's exterior neighborhood compose to
give a six-point equivalence from eligible foreign rows to eligible foreign
columns.  Its value on the row containing an actual neighbor is exactly the
column containing that neighbor.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The canonical foreign row-to-column permutation at `u`. -/
noncomputable def MuThreeMixedGridCode.foreignRowColumnEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : muThreeMixedCell K) :
    {x : X // ¬ H x u.1.2} ≃ {y : Y // ¬ H u.1.1 y} :=
  (code.foreignRowEquivNeighbor H K C u).trans
    (code.foreignColumnEquivNeighbor H K C u).symm

theorem MuThreeMixedGridCode.foreignRowColumnEquiv_value
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : muThreeMixedCell K)
    (x : {x : X // ¬ H x u.1.2}) :
    (code.foreignRowColumnEquiv H K C u x).1 =
      (code.foreignRowNeighbor H K C u x).1.2 := by
  rfl

/-- The row-to-column permutation recovers the column of every actual
neighbor from its row. -/
theorem MuThreeMixedGridCode.foreignRowColumnEquiv_of_adj
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) {u v : muThreeMixedCell K}
    (huv : C.Adj u v) :
    code.foreignRowColumnEquiv H K C u
        ⟨v.1.1, code.not_H_row_of_adj H K C huv⟩ =
      ⟨v.1.2, code.not_H_column_of_adj H K C huv⟩ := by
  apply Subtype.ext
  rw [code.foreignRowColumnEquiv_value H K C]
  exact congrArg (fun w : muThreeMixedCell K => w.1.2)
    (code.foreignRowNeighbor_unique H K C u
      ⟨v.1.1, code.not_H_row_of_adj H K C huv⟩ v huv rfl).symm

end

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.foreignRowColumnEquiv
#print axioms Erdos85.MuThreeMixedGridCode.foreignRowColumnEquiv_value
#print axioms Erdos85.MuThreeMixedGridCode.foreignRowColumnEquiv_of_adj
