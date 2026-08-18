import Proofs.Erdos85MuThreeMixedGridForeignRectangleMonodromy

/-!
# Reversal coherence of rectangle monodromy

Swapping the two endpoint rows reverses the four matching maps in a rectangle
circuit.  The resulting monodromy is therefore the inverse permutation on
the source column fiber.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Reversing the row orientation inverts rectangle monodromy. -/
theorem MuThreeMixedGridCode.foreignRectangleMonodromyEquiv_swap_rows
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a a' : X) (b b' : Y)
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b') :
    code.foreignRectangleMonodromyEquiv H K C a' a b b'
        ha'b ha'b' hab hab' =
      (code.foreignRectangleMonodromyEquiv H K C a a' b b'
        hab hab' ha'b ha'b').symm := by
  ext u
  rfl

/-- Pointwise inverse law in the forward-then-reverse direction. -/
theorem MuThreeMixedGridCode.foreignRectangleMonodromy_swap_rows_apply
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a a' : X) (b b' : Y)
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b')
    (u : {u : muThreeMixedCell K // u.1.2 = b}) :
    code.foreignRectangleMonodromyEquiv H K C a' a b b'
        ha'b ha'b' hab hab'
        (code.foreignRectangleMonodromyEquiv H K C a a' b b'
          hab hab' ha'b ha'b' u) = u := by
  rw [code.foreignRectangleMonodromyEquiv_swap_rows H K C
    a a' b b' hab hab' ha'b ha'b']
  exact Equiv.symm_apply_apply _ u

end


end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleMonodromyEquiv_swap_rows
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleMonodromy_swap_rows_apply
