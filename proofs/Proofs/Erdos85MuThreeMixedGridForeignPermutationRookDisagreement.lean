import Proofs.Erdos85MuThreeMixedGridForeignAgreementGraph
import Proofs.Erdos85MuThreeMixedGridHSupportFiberCounts

/-!
# Rook disagreement of the foreign permutations

The generic C4 bound allows one agreement between two local permutations.
For centers sharing a row or column, the rook law improves this to zero:
their permutations disagree on every row eligible for both.  In particular,
the row and column partners in the occupied H-support two-factor are forced
zero-agreement pairs.
-/

open SimpleGraph

namespace Erdos85

/-- Rook-related centers have no agreement on any shared eligible row. -/
theorem MuThreeMixedGridCode.foreignRowColumnEquiv_ne_of_rowColumn
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {u w : muThreeMixedCell K}
    (hrook : (mixedGridRowColumnGraph K).Adj u w)
    (x : X) (hxu : ¬ H x u.1.2) (hxw : ¬ H x w.1.2) :
    (code.foreignRowColumnEquiv H K C u ⟨x, hxu⟩).1 ≠
      (code.foreignRowColumnEquiv H K C w ⟨x, hxw⟩).1 := by
  intro hagree
  have hag : (mixedGridForeignAgreementGraph H K C code).Adj u w :=
    ⟨hrook.1, x, hxu, hxw, hagree⟩
  rw [code.foreignAgreementGraph_eq_commonNeighborGraph H K C] at hag
  have hzero := code.rowColumn_common_neighbor_card_eq_zero H K C hrook
  exact Nat.zero_ne_one (hzero.symm.trans hag.2)

/-- Same-row specialization. -/
theorem MuThreeMixedGridCode.foreignRowColumnEquiv_ne_of_same_row
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {u w : muThreeMixedCell K} (huw : u ≠ w) (hrow : u.1.1 = w.1.1)
    (x : X) (hxu : ¬ H x u.1.2) (hxw : ¬ H x w.1.2) :
    (code.foreignRowColumnEquiv H K C u ⟨x, hxu⟩).1 ≠
      (code.foreignRowColumnEquiv H K C w ⟨x, hxw⟩).1 :=
  code.foreignRowColumnEquiv_ne_of_rowColumn H K C
    ⟨huw, Or.inl hrow⟩ x hxu hxw

/-- Same-column specialization. -/
theorem MuThreeMixedGridCode.foreignRowColumnEquiv_ne_of_same_column
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {u w : muThreeMixedCell K} (huw : u ≠ w) (hcolumn : u.1.2 = w.1.2)
    (x : X) (hxu : ¬ H x u.1.2) (hxw : ¬ H x w.1.2) :
    (code.foreignRowColumnEquiv H K C u ⟨x, hxu⟩).1 ≠
      (code.foreignRowColumnEquiv H K C w ⟨x, hxw⟩).1 :=
  code.foreignRowColumnEquiv_ne_of_rowColumn H K C
    ⟨huw, Or.inr hcolumn⟩ x hxu hxw

/-- Any distinct occupied H-support partners in one row or column are forced
zero-agreement centers. -/
theorem MuThreeMixedGridCode.HSupport_partner_foreign_disagreement
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {u w : muThreeMixedCell K}
    (_hu : u ∈ mixedGridHSupport H K) (_hw : w ∈ mixedGridHSupport H K)
    (huw : u ≠ w) (hrook : u.1.1 = w.1.1 ∨ u.1.2 = w.1.2)
    (x : X) (hxu : ¬ H x u.1.2) (hxw : ¬ H x w.1.2) :
    (code.foreignRowColumnEquiv H K C u ⟨x, hxu⟩).1 ≠
      (code.foreignRowColumnEquiv H K C w ⟨x, hxw⟩).1 :=
  code.foreignRowColumnEquiv_ne_of_rowColumn H K C
    ⟨huw, hrook⟩ x hxu hxw

end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRowColumnEquiv_ne_of_rowColumn
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRowColumnEquiv_ne_of_same_row
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRowColumnEquiv_ne_of_same_column
#print axioms
  Erdos85.MuThreeMixedGridCode.HSupport_partner_foreign_disagreement
