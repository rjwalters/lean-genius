import Proofs.Erdos85SizeTwoEigenlineCyclicPackingBound

/-!
# Two-fiber subsystem of the cyclic packing code

The q=6 tracked UNSAT core uses agreement and reciprocity on only two
non-antipodal difference fibers.  This file isolates exactly that weakened
finite object.  In particular, it does not silently retain reciprocity or
agreement assumptions on the unused fibers.
-/

namespace Erdos85

noncomputable section

/-- Routing data before either agreement or reciprocity is imposed. -/
structure SizeTwoCyclicRoutingData (q : ℕ) [NeZero q] (a : ZMod q) where
  perm : SizeTwoCyclicPermutationFamily q a
  targetDifference : ∀ (x : ZMod q)
    (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1),
      sizeTwoAllowedDifference q a
  target_column_eq : ∀ (x : ZMod q)
    (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1),
      r.1 + (targetDifference x t r).1 = (perm x t r).1

theorem SizeTwoCyclicRoutingData.reverse_admissible
    {q : ℕ} [NeZero q] {a : ZMod q}
    (data : SizeTwoCyclicRoutingData q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1) :
    let s := data.targetDifference x t r
    s.1 ≠ -r.1 ∧ s.1 ≠ (-r.1) - 1 := by
  let s := data.targetDifference x t r
  have hc := (data.perm x t r).2
  constructor
  · intro hs
    apply hc.1
    rw [← data.target_column_eq x t r, hs]
    abel
  · intro hs
    apply hc.2
    rw [← data.target_column_eq x t r, hs]
    abel

/-- Same-difference agreement restricted to one selected fiber. -/
def SizeTwoCyclicRoutingData.AgreementAt
    {q : ℕ} [NeZero q] {a : ZMod q}
    (data : SizeTwoCyclicRoutingData q a)
    (t : sizeTwoAllowedDifference q a) : Prop :=
  ∀ (x d : ZMod q), d ≠ 0 →
    Fintype.card (SizeTwoCrossShiftedPermutationAgreement
      q a data.perm x d t t) ≤ 1

/-- Reciprocity restricted to routes whose source difference is `t`. -/
def SizeTwoCyclicRoutingData.ReciprocityAt
    {q : ℕ} [NeZero q] {a : ZMod q}
    (data : SizeTwoCyclicRoutingData q a)
    (t : sizeTwoAllowedDifference q a) : Prop :=
  ∀ (x : ZMod q) (r : SizeTwoAdmissibleTargetRow q t.1),
    let s := data.targetDifference x t r
    let reverseRow : SizeTwoAdmissibleTargetRow q s.1 :=
      ⟨-r.1, data.reverse_admissible x t r⟩
    (data.perm (x + r.1) s reverseRow).1 = t.1 - r.1

/-- The exact two-difference subsystem found by the tracked q=6 core. -/
structure SizeTwoCyclicTwoFiberCode
    (q : ℕ) [NeZero q] (a : ZMod q)
    (t u : sizeTwoAllowedDifference q a) where
  data : SizeTwoCyclicRoutingData q a
  agreement_t : data.AgreementAt t
  agreement_u : data.AgreementAt u
  reciprocity_t : data.ReciprocityAt t
  reciprocity_u : data.ReciprocityAt u

/-- Forget a reciprocal code down to raw routing data. -/
def SizeTwoCyclicReciprocalPermutationCode.toRoutingData
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a) :
    SizeTwoCyclicRoutingData q a where
  perm := code.toPermutationCode.perm
  targetDifference := code.targetDifference
  target_column_eq := code.target_column_eq

theorem SizeTwoCyclicReciprocalPermutationCode.toRoutingData_reciprocityAt
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (t : sizeTwoAllowedDifference q a) :
    code.toRoutingData.ReciprocityAt t := by
  intro x r
  change (code.toPermutationCode.perm
    (x + r.1) (code.targetDifference x t r)
      ⟨-r.1, code.toRoutingData.reverse_admissible x t r⟩).1 = t.1 - r.1
  convert code.reciprocity x t r using 1

/-- Every reduced same-difference code contains each selected two-fiber
subsystem. -/
def SizeTwoCyclicSameDifferenceCode.toTwoFiberCode
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicSameDifferenceCode q a)
    (t u : sizeTwoAllowedDifference q a) :
    SizeTwoCyclicTwoFiberCode q a t u where
  data := code.toReciprocalCode.toRoutingData
  agreement_t := by
    intro x d hd
    exact code.same_difference_agreement_le_one x d hd t
  agreement_u := by
    intro x d hd
    exact code.same_difference_agreement_le_one x d hd u
  reciprocity_t :=
    code.toReciprocalCode.toRoutingData_reciprocityAt t
  reciprocity_u :=
    code.toReciprocalCode.toRoutingData_reciprocityAt u

/-- The precise finite statement supported by the minimal tracked core:
at q=6 and a=1, fibers 0 and 2 already contradict each other. -/
def sizeTwoCyclicSixFiberZero :
    sizeTwoAllowedDifference 6 (1 : ZMod 6) := ⟨0, by decide⟩

def sizeTwoCyclicSixFiberTwo :
    sizeTwoAllowedDifference 6 (1 : ZMod 6) := ⟨2, by decide⟩

def SizeTwoCyclicSixTwoFiberExclusion : Prop :=
  IsEmpty (SizeTwoCyclicTwoFiberCode 6 (1 : ZMod 6)
    sizeTwoCyclicSixFiberZero sizeTwoCyclicSixFiberTwo)

/-- The two-fiber exclusion implies the previously stated q=6 packing
exclusion at a=1. -/
theorem sizeTwoCyclicPackingExclusion_six_one_of_twoFiber
    (h : SizeTwoCyclicSixTwoFiberExclusion) :
    SizeTwoCyclicPackingExclusion 6 (1 : ZMod 6) := by
  constructor
  intro code
  exact h.false (code.toTwoFiberCode
    sizeTwoCyclicSixFiberZero sizeTwoCyclicSixFiberTwo)

end

end Erdos85

#print axioms Erdos85.SizeTwoCyclicRoutingData.reverse_admissible
#print axioms Erdos85.sizeTwoCyclicPackingExclusion_six_one_of_twoFiber
