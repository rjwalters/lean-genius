import Proofs.Erdos85SizeTwoEigenlineCyclicTwoFiberSubsystem

/-!
# Three-fiber subsystem of the cyclic packing code

Node: `BinarySizeTwoCyclicPackingBound` beneath outline F.3.

The verified q=8 finite core uses same-difference agreement only on the three
fibers `0, 2, 4`.  Reciprocity is retained on those source fibers and may
route into any of the six allowed target fibers.  This file isolates exactly
that weakened mathematical object, without importing agreement assumptions
on the other three fibers.
-/

namespace Erdos85

noncomputable section

/-- Routing data with agreement and reciprocity imposed at exactly three
selected source-difference fibers. -/
structure SizeTwoCyclicThreeFiberCode
    (q : ℕ) [NeZero q] (a : ZMod q)
    (t u v : sizeTwoAllowedDifference q a) where
  data : SizeTwoCyclicRoutingData q a
  agreement_t : data.AgreementAt t
  agreement_u : data.AgreementAt u
  agreement_v : data.AgreementAt v
  reciprocity_t : data.ReciprocityAt t
  reciprocity_u : data.ReciprocityAt u
  reciprocity_v : data.ReciprocityAt v

/-- Every reduced same-difference code restricts to any chosen three-fiber
subsystem. -/
def SizeTwoCyclicSameDifferenceCode.toThreeFiberCode
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicSameDifferenceCode q a)
    (t u v : sizeTwoAllowedDifference q a) :
    SizeTwoCyclicThreeFiberCode q a t u v where
  data := code.toReciprocalCode.toRoutingData
  agreement_t := by
    intro x d hd
    exact code.same_difference_agreement_le_one x d hd t
  agreement_u := by
    intro x d hd
    exact code.same_difference_agreement_le_one x d hd u
  agreement_v := by
    intro x d hd
    exact code.same_difference_agreement_le_one x d hd v
  reciprocity_t :=
    code.toReciprocalCode.toRoutingData_reciprocityAt t
  reciprocity_u :=
    code.toReciprocalCode.toRoutingData_reciprocityAt u
  reciprocity_v :=
    code.toReciprocalCode.toRoutingData_reciprocityAt v

/-- The first fiber in the q=8 three-fiber core. -/
def sizeTwoCyclicEightFiberZero :
    sizeTwoAllowedDifference 8 (1 : ZMod 8) := ⟨0, by decide⟩

/-- The second fiber in the q=8 three-fiber core. -/
def sizeTwoCyclicEightFiberTwo :
    sizeTwoAllowedDifference 8 (1 : ZMod 8) := ⟨2, by decide⟩

/-- The third fiber in the q=8 three-fiber core. -/
def sizeTwoCyclicEightFiberFour :
    sizeTwoAllowedDifference 8 (1 : ZMod 8) := ⟨4, by decide⟩

/-- Exact formal target corresponding to the verified q=8 `{0,2,4}` core. -/
def SizeTwoCyclicEightThreeFiberExclusion : Prop :=
  IsEmpty (SizeTwoCyclicThreeFiberCode 8 (1 : ZMod 8)
    sizeTwoCyclicEightFiberZero sizeTwoCyclicEightFiberTwo
      sizeTwoCyclicEightFiberFour)

/-- Excluding the exact three-fiber core proves the q=8, a=1 instance of the
abstract packing conjecture. -/
theorem sizeTwoCyclicPackingExclusion_eight_one_of_threeFiber
    (h : SizeTwoCyclicEightThreeFiberExclusion) :
    SizeTwoCyclicPackingExclusion 8 (1 : ZMod 8) := by
  constructor
  intro code
  exact h.false (code.toThreeFiberCode
    sizeTwoCyclicEightFiberZero sizeTwoCyclicEightFiberTwo
      sizeTwoCyclicEightFiberFour)

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicPackingExclusion_eight_one_of_threeFiber
