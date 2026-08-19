import Proofs.Erdos85SizeTwoEigenlineCyclicTwoFiberSubsystem
import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationExactCode

/-!
# Loopless single-fiber subsystem

The direct Boolean graph probe at q=8 is already UNSAT when the common-target
cap is retained at only the central difference fiber.  Symmetry and
looplessness remain global through the reciprocal code.  This is a weaker and
more faithful target than the loopless-free packing conjecture.
-/

namespace Erdos85

noncomputable section

structure SizeTwoCyclicLooplessSingleFiberCode
    (q : ℕ) [NeZero q] (a : ZMod q)
    (t : sizeTwoAllowedDifference q a) where
  code : SizeTwoCyclicReciprocalPermutationCode q a
  loopless : code.Loopless
  agreement : code.toRoutingData.AgreementAt t

def SizeTwoCyclicExactPermutationCode.toSingleFiberCode
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicExactPermutationCode q a)
    (t : sizeTwoAllowedDifference q a) :
    SizeTwoCyclicLooplessSingleFiberCode q a t where
  code := code.toReciprocalCode
  loopless := code.loopless
  agreement := by
    intro x d hd
    exact code.toFullCode.cross_agreement_le_one x d t t (Or.inl hd)

def sizeTwoCyclicEightFiberThree :
    sizeTwoAllowedDifference 8 (1 : ZMod 8) := ⟨3, by decide⟩

/-- Exact finite target supported by the q=8 one-fiber Boolean UNSAT run. -/
def SizeTwoCyclicEightCentralFiberExclusion : Prop :=
  IsEmpty (SizeTwoCyclicLooplessSingleFiberCode 8 (1 : ZMod 8)
    sizeTwoCyclicEightFiberThree)

theorem sizeTwoCyclicExactCode_isEmpty_eight_one_of_centralFiber
    (h : SizeTwoCyclicEightCentralFiberExclusion) :
    IsEmpty (SizeTwoCyclicExactPermutationCode 8 (1 : ZMod 8)) := by
  constructor
  intro code
  exact h.false (code.toSingleFiberCode sizeTwoCyclicEightFiberThree)

/-- Consumer all the way back to a hypothetical q=8 cyclic grid. -/
theorem false_of_sizeTwoCyclicEightCentralFiberExclusion
    (C : SimpleGraph (sizeTwoCyclicExteriorCell 8 (1 : ZMod 8)))
    [DecidableRel C.Adj]
    (hfree : ¬ containsC4 (sizeTwoCyclicExteriorCell 8 (1 : ZMod 8)) C)
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell 8 (1 : ZMod 8))
      (y : ZMod 8),
      ((C.neighborFinset u).filter fun v => v.1.1 = y).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1)
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell 8 (1 : ZMod 8))
      (z : ZMod 8),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1)
    (h : SizeTwoCyclicEightCentralFiberExclusion) : False := by
  let code := sizeTwoCyclicExactPermutationCode_of_grid
    8 (1 : ZMod 8) C hfree hrow_hit hcol_hit
  exact h.false (code.toSingleFiberCode sizeTwoCyclicEightFiberThree)

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicExactCode_isEmpty_eight_one_of_centralFiber
#print axioms Erdos85.false_of_sizeTwoCyclicEightCentralFiberExclusion
