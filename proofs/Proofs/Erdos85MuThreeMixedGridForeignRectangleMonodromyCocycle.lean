import Proofs.Erdos85MuThreeMixedGridForeignRectangleMonodromyConjugacy

/-!
# Rectangle monodromy cocycle

For fixed endpoint columns, rectangle monodromy is the relative quotient of
the two endpoint-row transports.  Consequently the monodromies through three
rows satisfy an exact cocycle law.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Rectangle monodromy is the first row transport followed by the inverse
of the second row transport. -/
theorem MuThreeMixedGridCode.foreignRectangleMonodromyEquiv_eq_rowTransport_trans_symm
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a a' : X) (b b' : Y)
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b') :
    code.foreignRectangleMonodromyEquiv H K C a a' b b'
        hab hab' ha'b ha'b' =
      (code.foreignRowTransportEquiv H K C a b b' hab hab').trans
        (code.foreignRowTransportEquiv H K C a' b b' ha'b ha'b').symm := by
  ext u
  simp [MuThreeMixedGridCode.foreignRectangleMonodromyEquiv,
    MuThreeMixedGridCode.foreignRectangleThreeStepEquiv,
    MuThreeMixedGridCode.foreignRowTransportEquiv]

/-- For fixed columns, rectangle monodromies compose through an intermediate
row exactly as a cocycle. -/
theorem MuThreeMixedGridCode.foreignRectangleMonodromyEquiv_trans
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a a' a'' : X) (b b' : Y)
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b')
    (ha''b : ¬ H a'' b) (ha''b' : ¬ H a'' b') :
    (code.foreignRectangleMonodromyEquiv H K C a a' b b'
        hab hab' ha'b ha'b').trans
      (code.foreignRectangleMonodromyEquiv H K C a' a'' b b'
        ha'b ha'b' ha''b ha''b') =
      code.foreignRectangleMonodromyEquiv H K C a a'' b b'
        hab hab' ha''b ha''b' := by
  rw [code.foreignRectangleMonodromyEquiv_eq_rowTransport_trans_symm H K C,
    code.foreignRectangleMonodromyEquiv_eq_rowTransport_trans_symm H K C,
    code.foreignRectangleMonodromyEquiv_eq_rowTransport_trans_symm H K C]
  ext u
  simp

end

end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleMonodromyEquiv_eq_rowTransport_trans_symm
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleMonodromyEquiv_trans
