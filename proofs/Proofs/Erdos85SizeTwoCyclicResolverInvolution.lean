import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationInvolution

/-!
# The row-resolver involution in the cyclic size-two code

Node: `BinarySizeTwoCyclicPackingBound` beneath `GAP A-REG-NONBIP`.

At a fixed base coordinate, the routes with relative row zero are exactly the
resolver edges sharing the first component endpoint.  They pair the non-edge
difference fibers.  This file exposes that pairing directly from reciprocity:
it is an involution, and graph looplessness makes it fixed-point-free.
-/

namespace Erdos85

noncomputable section

/-- Difference fibers other than the two internal-cycle edge differences
`0,-1`.  These are precisely the fibers on which relative row zero is
admissible. -/
def SizeTwoCyclicNonedgeDifference
    (q : ℕ) [NeZero q] (a : ZMod q) :=
  {t : sizeTwoAllowedDifference q a // t.1 ≠ 0 ∧ t.1 ≠ -1}

/-- Relative row zero, admissible exactly on a non-edge difference fiber. -/
def sizeTwoCyclicResolverZeroRow
    {q : ℕ} [NeZero q] {a : ZMod q}
    (t : SizeTwoCyclicNonedgeDifference q a) :
    SizeTwoAdmissibleTargetRow q t.1.1 :=
  ⟨0, by
    constructor
    · simpa using t.2.1
    · simpa using t.2.2⟩

/-- The target difference of the row-zero resolver route.  Reverse
admissibility shows that it is again a non-edge difference. -/
def SizeTwoCyclicReciprocalPermutationCode.resolverFiber
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : SizeTwoCyclicNonedgeDifference q a) :
    SizeTwoCyclicNonedgeDifference q a := by
  let r := sizeTwoCyclicResolverZeroRow t
  let s := code.targetDifference x t.1 r
  refine ⟨s, ?_⟩
  have h := code.reverse_admissible x t.1 r
  constructor
  · intro hs
    apply h.1
    change s.1 = -(0 : ZMod q)
    simpa using hs
  · intro hs
    apply h.2
    change s.1 = -(0 : ZMod q) - 1
    simpa using hs

/-- Reciprocity says that resolving twice at the same base returns to the
original difference fiber. -/
theorem SizeTwoCyclicReciprocalPermutationCode.resolverFiber_involutive
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : SizeTwoCyclicNonedgeDifference q a) :
    code.resolverFiber x (code.resolverFiber x t) = t := by
  apply Subtype.ext
  apply Subtype.ext
  simpa [SizeTwoCyclicReciprocalPermutationCode.resolverFiber,
    sizeTwoCyclicResolverZeroRow] using
      congrArg Subtype.val
        (code.reverse_targetDifference x t.1
          (sizeTwoCyclicResolverZeroRow t))

/-- The row-resolver pairing as a self-equivalence of the non-edge fibers. -/
def SizeTwoCyclicReciprocalPermutationCode.resolverFiberEquiv
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) :
    SizeTwoCyclicNonedgeDifference q a ≃
      SizeTwoCyclicNonedgeDifference q a where
  toFun := code.resolverFiber x
  invFun := code.resolverFiber x
  left_inv := code.resolverFiber_involutive x
  right_inv := code.resolverFiber_involutive x

/-- Looplessness makes every row-resolver involution fixed-point-free. -/
theorem SizeTwoCyclicReciprocalPermutationCode.resolverFiber_ne
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (hloop : code.Loopless)
    (x : ZMod q) (t : SizeTwoCyclicNonedgeDifference q a) :
    code.resolverFiber x t ≠ t := by
  intro h
  apply hloop x t.1 (sizeTwoCyclicResolverZeroRow t)
  constructor
  · rfl
  · have hv := congrArg Subtype.val h
    simpa [SizeTwoCyclicReciprocalPermutationCode.resolverFiber] using hv

end

end Erdos85

#print axioms Erdos85.SizeTwoCyclicReciprocalPermutationCode.resolverFiber_involutive
#print axioms Erdos85.SizeTwoCyclicReciprocalPermutationCode.resolverFiber_ne
