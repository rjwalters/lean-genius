import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationInvolution

/-!
# Canonical reflected routing permutations

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3.

The routing bijection has different source and target types.  Reflection in
the source difference canonically identifies target columns with source rows:
`c ↦ t-c`.  Composing with routing therefore gives a genuine permutation of
the `q-2` admissible rows, to which the permutation-sign character applies.

Reciprocity has a particularly clean form in these coordinates: reversing a
route negates both its input row and the value of the reflected permutation.
This is the line/base-resolved sign interface that remains after the global
route-reversal sign collapses to `+1`.
-/

namespace Erdos85

noncomputable section

/-- Reflection in `t` identifies the two punctured cyclic lines. -/
def sizeTwoTargetColumnReflectionEquiv
    (q : ℕ) [NeZero q] (t : ZMod q) :
    SizeTwoAdmissibleTargetColumn q ≃ SizeTwoAdmissibleTargetRow q t where
  toFun c := ⟨t - c.1, by
    constructor
    · intro h
      apply c.2.1
      have := congrArg (fun z : ZMod q => t - z) h
      simpa using this.symm
    · intro h
      apply c.2.2
      have := congrArg (fun z : ZMod q => t - z) h
      have hc : c.1 + 1 = 0 := by
        calc
          c.1 + 1 = t - (t - c.1 - 1) := by abel
          _ = t - t := this.symm
          _ = 0 := sub_self t
      calc
        c.1 = (c.1 + 1) - 1 := by abel
        _ = 0 - 1 := by rw [hc]
        _ = -1 := by abel⟩
  invFun r := ⟨t - r.1, by
    constructor
    · intro h
      apply r.2.1
      have := congrArg (fun z : ZMod q => t - z) h
      simpa using this.symm
    · intro h
      apply r.2.2
      have := congrArg (fun z : ZMod q => t - z) h
      have hr : r.1 = t + 1 := by simpa using this
      calc
        t = (t + 1) - 1 := by abel
        _ = r.1 - 1 := by rw [hr]⟩
  left_inv c := by apply Subtype.ext; dsimp; abel
  right_inv r := by apply Subtype.ext; dsimp; abel

/-- The canonical local permutation obtained by reflecting routing columns
back into the source-row line. -/
def SizeTwoCyclicReciprocalPermutationCode.reflectedPerm
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
    Equiv.Perm (SizeTwoAdmissibleTargetRow q t.1) :=
  (code.toPermutationCode.perm x t).trans
    (sizeTwoTargetColumnReflectionEquiv q t.1)

@[simp] theorem SizeTwoCyclicReciprocalPermutationCode.reflectedPerm_val
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1) :
    (code.reflectedPerm x t r).1 =
      t.1 - (code.toPermutationCode.perm x t r).1 := rfl

/-- Pointwise reversal coherence for the canonical reflected permutations.
If `s` is the target difference of a route, then at the reversed cell both
the row and the reflected-permutation value are negated. -/
theorem SizeTwoCyclicReciprocalPermutationCode.reflectedPerm_reverse
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1) :
    let s := code.targetDifference x t r
    let reverseRow : SizeTwoAdmissibleTargetRow q s.1 :=
      ⟨-r.1, code.reverse_admissible x t r⟩
    (code.reflectedPerm (x + r.1) s reverseRow).1 =
      -(code.reflectedPerm x t r).1 := by
  dsimp only
  let s := code.targetDifference x t r
  let reverseRow : SizeTwoAdmissibleTargetRow q s.1 :=
    ⟨-r.1, code.reverse_admissible x t r⟩
  rw [code.reflectedPerm_val, code.reflectedPerm_val,
    code.reciprocity x t r]
  change s.1 - (t.1 - r.1) =
    -(t.1 - (code.toPermutationCode.perm x t r).1)
  rw [show s.1 = (code.toPermutationCode.perm x t r).1 - r.1 by
    have hs := code.target_column_eq x t r
    change r.1 + s.1 = (code.toPermutationCode.perm x t r).1 at hs
    calc
      s.1 = -r.1 + (r.1 + s.1) := by abel
      _ = -r.1 + (code.toPermutationCode.perm x t r).1 := by rw [hs]
      _ = (code.toPermutationCode.perm x t r).1 - r.1 := by abel]
  abel

end

end Erdos85

#print axioms Erdos85.SizeTwoCyclicReciprocalPermutationCode.reflectedPerm_reverse
