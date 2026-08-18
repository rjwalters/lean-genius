import Proofs.Erdos85MuThreeMixedGridForeignRectangleMonodromyEvenCycleCount

/-!
# Rectangle sign as an eligible-row coboundary

Fixing a base eligible row two-colors every other eligible row by the sign of
its base rectangle.  The sign of the rectangle between two rows is exactly
the product of their colors.  Thus even rectangles are the within-color
pairs and odd rectangles are the cross-color pairs.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Relative rectangle sign is the product of the two base-row signs. -/
theorem MuThreeMixedGridCode.foreignRectangleMonodromy_sign_eq_base_mul_base
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (r a a' : X) (b b' : Y)
    (hrb : ¬ H r b) (hrb' : ¬ H r b')
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b') :
    Equiv.Perm.sign
        (code.foreignRectangleMonodromyEquiv H K C a a' b b'
          hab hab' ha'b ha'b') =
      Equiv.Perm.sign
          (code.foreignRectangleMonodromyEquiv H K C r a b b'
            hrb hrb' hab hab') *
        Equiv.Perm.sign
          (code.foreignRectangleMonodromyEquiv H K C r a' b b'
            hrb hrb' ha'b ha'b') := by
  have hcoc := code.foreignRectangleMonodromy_sign_cocycle H K C
    r a a' b b' hrb hrb' hab hab' ha'b ha'b'
  have hsolve := (eq_inv_mul_iff_mul_eq).2 hcoc
  simpa [Int.units_inv_eq_self] using hsolve

/-- Two eligible rows define an even rectangle exactly when their base-row
colors agree. -/
theorem MuThreeMixedGridCode.foreignRectangleMonodromy_sign_eq_one_iff_base_eq
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (r a a' : X) (b b' : Y)
    (hrb : ¬ H r b) (hrb' : ¬ H r b')
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b') :
    Equiv.Perm.sign
          (code.foreignRectangleMonodromyEquiv H K C a a' b b'
            hab hab' ha'b ha'b') = 1 ↔
      Equiv.Perm.sign
          (code.foreignRectangleMonodromyEquiv H K C r a b b'
            hrb hrb' hab hab') =
        Equiv.Perm.sign
          (code.foreignRectangleMonodromyEquiv H K C r a' b b'
            hrb hrb' ha'b ha'b') := by
  rw [code.foreignRectangleMonodromy_sign_eq_base_mul_base H K C
    r a a' b b' hrb hrb' hab hab' ha'b ha'b']
  rw [mul_eq_one_iff_eq_inv, Int.units_inv_eq_self]

/-- Two eligible rows define an odd rectangle exactly when their base-row
colors differ. -/
theorem MuThreeMixedGridCode.foreignRectangleMonodromy_sign_eq_neg_one_iff_base_ne
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (r a a' : X) (b b' : Y)
    (hrb : ¬ H r b) (hrb' : ¬ H r b')
    (hab : ¬ H a b) (hab' : ¬ H a b')
    (ha'b : ¬ H a' b) (ha'b' : ¬ H a' b') :
    Equiv.Perm.sign
          (code.foreignRectangleMonodromyEquiv H K C a a' b b'
            hab hab' ha'b ha'b') = -1 ↔
      Equiv.Perm.sign
          (code.foreignRectangleMonodromyEquiv H K C r a b b'
            hrb hrb' hab hab') ≠
        Equiv.Perm.sign
          (code.foreignRectangleMonodromyEquiv H K C r a' b b'
            hrb hrb' ha'b ha'b') := by
  rw [code.foreignRectangleMonodromy_sign_eq_base_mul_base H K C
    r a a' b b' hrb hrb' hab hab' ha'b ha'b']
  rcases Int.units_eq_one_or
      (Equiv.Perm.sign
        (code.foreignRectangleMonodromyEquiv H K C r a b b'
          hrb hrb' hab hab')) with h | h <;>
    rcases Int.units_eq_one_or
      (Equiv.Perm.sign
        (code.foreignRectangleMonodromyEquiv H K C r a' b b'
          hrb hrb' ha'b ha'b')) with h' | h' <;>
    simp [h, h']

end

end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleMonodromy_sign_eq_base_mul_base
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleMonodromy_sign_eq_one_iff_base_eq
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRectangleMonodromy_sign_eq_neg_one_iff_base_ne
