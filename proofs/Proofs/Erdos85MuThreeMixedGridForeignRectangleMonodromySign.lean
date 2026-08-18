import Proofs.Erdos85MuThreeMixedGridForeignRectangleMonodromyCocycle
import Mathlib.GroupTheory.Perm.Sign

/-!
# Parity coherence of rectangle monodromy

Applying the permutation-sign character to the rectangle cocycle gives a
multiplicative parity law.  In particular, the three oriented monodromies
around any triangle of eligible rows have positive total sign.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The sign of rectangle monodromy is a multiplicative row cocycle. -/
theorem MuThreeMixedGridCode.foreignRectangleMonodromy_sign_cocycle
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a a' a'' : X) (b b' : Y)
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b')
    (ha''b : ¬ H a'' b) (ha''b' : ¬ H a'' b') :
    Equiv.Perm.sign
        (code.foreignRectangleMonodromyEquiv H K C a a' b b'
          hab hab' ha'b ha'b') *
      Equiv.Perm.sign
        (code.foreignRectangleMonodromyEquiv H K C a' a'' b b'
          ha'b ha'b' ha''b ha''b') =
      Equiv.Perm.sign
        (code.foreignRectangleMonodromyEquiv H K C a a'' b b'
          hab hab' ha''b ha''b') := by
  have h := congrArg Equiv.Perm.sign
    (code.foreignRectangleMonodromyEquiv_trans H K C
      a a' a'' b b' hab hab' ha'b ha'b' ha''b ha''b')
  simpa [Equiv.Perm.sign_trans, mul_comm] using h

/-- The product of the three oriented rectangle-monodromy signs around a
triangle of eligible rows is positive. -/
theorem MuThreeMixedGridCode.foreignRectangleMonodromy_sign_triangle
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a a' a'' : X) (b b' : Y)
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b')
    (ha''b : ¬ H a'' b) (ha''b' : ¬ H a'' b') :
    Equiv.Perm.sign
        (code.foreignRectangleMonodromyEquiv H K C a a' b b'
          hab hab' ha'b ha'b') *
      Equiv.Perm.sign
        (code.foreignRectangleMonodromyEquiv H K C a' a'' b b'
          ha'b ha'b' ha''b ha''b') *
      Equiv.Perm.sign
        (code.foreignRectangleMonodromyEquiv H K C a'' a b b'
          ha''b ha''b' hab hab') = 1 := by
  rw [code.foreignRectangleMonodromy_sign_cocycle H K C
    a a' a'' b b' hab hab' ha'b ha'b' ha''b ha''b']
  rw [code.foreignRectangleMonodromyEquiv_swap_rows H K C
    a a'' b b' hab hab' ha''b ha''b']
  rw [Equiv.Perm.sign_symm]
  exact Int.units_mul_self _

/-- Reversing the row orientation does not change monodromy parity. -/
theorem MuThreeMixedGridCode.foreignRectangleMonodromy_sign_swap_rows
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a a' : X) (b b' : Y)
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b') :
    Equiv.Perm.sign
        (code.foreignRectangleMonodromyEquiv H K C a' a b b'
          ha'b ha'b' hab hab') =
      Equiv.Perm.sign
        (code.foreignRectangleMonodromyEquiv H K C a a' b b'
          hab hab' ha'b ha'b') := by
  rw [code.foreignRectangleMonodromyEquiv_swap_rows H K C
    a a' b b' hab hab' ha'b ha'b', Equiv.Perm.sign_symm]

/-- Reversing the column orientation does not change monodromy parity, even
though it changes the source fiber and conjugates the inverse permutation. -/
theorem MuThreeMixedGridCode.foreignRectangleMonodromy_sign_swap_columns
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a a' : X) (b b' : Y)
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b') :
    Equiv.Perm.sign
        (code.foreignRectangleMonodromyEquiv H K C a a' b' b
          hab' hab ha'b' ha'b) =
      Equiv.Perm.sign
        (code.foreignRectangleMonodromyEquiv H K C a a' b b'
          hab hab' ha'b ha'b') := by
  rw [code.foreignRectangleMonodromyEquiv_swap_columns H K C
    a a' b b' hab hab' ha'b ha'b']
  simp

end

end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleMonodromy_sign_cocycle
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleMonodromy_sign_triangle
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleMonodromy_sign_swap_rows
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleMonodromy_sign_swap_columns
