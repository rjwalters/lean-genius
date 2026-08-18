import Proofs.Erdos85MuThreeMixedGridForeignRectangleMonodromyInverse

/-!
# Column-reversal conjugacy of rectangle monodromy

Swapping the endpoint columns changes the source fiber.  After identifying
the two column fibers by row transport, the swapped-column monodromy is the
conjugate of the inverse original monodromy.  Thus orientation reversal
preserves the monodromy cycle type up to inversion.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Swapping the two endpoint columns gives the transport-conjugate inverse
monodromy. -/
theorem MuThreeMixedGridCode.foreignRectangleMonodromyEquiv_swap_columns
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a a' : X) (b b' : Y)
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b') :
    code.foreignRectangleMonodromyEquiv H K C a a' b' b
        hab' hab ha'b' ha'b =
      (((code.foreignRowTransportEquiv H K C a b b' hab hab').symm.trans
        (code.foreignRectangleMonodromyEquiv H K C a a' b b'
          hab hab' ha'b ha'b').symm).trans
        (code.foreignRowTransportEquiv H K C a b b' hab hab')) := by
  ext u
  simp [MuThreeMixedGridCode.foreignRectangleMonodromyEquiv,
    MuThreeMixedGridCode.foreignRectangleThreeStepEquiv,
    MuThreeMixedGridCode.foreignRowTransportEquiv]

/-- Pointwise conjugacy form. -/
theorem MuThreeMixedGridCode.foreignRectangleMonodromy_swap_columns_apply
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a a' : X) (b b' : Y)
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b')
    (u : {u : muThreeMixedCell K // u.1.2 = b'}) :
    code.foreignRectangleMonodromyEquiv H K C a a' b' b
        hab' hab ha'b' ha'b u =
      code.foreignRowTransportEquiv H K C a b b' hab hab'
        ((code.foreignRectangleMonodromyEquiv H K C a a' b b'
          hab hab' ha'b ha'b').symm
          ((code.foreignRowTransportEquiv H K C a b b' hab hab').symm u)) := by
  rw [code.foreignRectangleMonodromyEquiv_swap_columns H K C
    a a' b b' hab hab' ha'b ha'b']
  rfl

end


end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleMonodromyEquiv_swap_columns
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleMonodromy_swap_columns_apply
