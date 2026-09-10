import Proofs.Erdos85ColorTripleSupportClosure
import Proofs.Erdos85ThreeHighSupportedSearchStabilization
import Proofs.Erdos85OrderFortyNineThreeHighTripleSupportedCandidateSearch

namespace Erdos85

/-- Run joint exact cover after support filtering has reached a fixed point. -/
def threeHighClosedJointSearch (B : Fin 24 → Fin 24 → Bool) : Bool :=
  threeHighListedJointSearch B
    (threeHighTripleSupportClosure B
      (fun k => (threeHighCanonicalTripleShapes k).filter (threeHighTripleNoCommonNeighbor B)))
    threeHighCanonicalResidual

/-- Early stopping computes exactly the same ordered candidates as 1608 rounds. -/
theorem threeHighClosedJointSearch_eq (B : Fin 24 → Fin 24 → Bool) :
    threeHighClosedJointSearch B = threeHighSupportedJointSearch B 1608 := by
  let D := fun k => (threeHighCanonicalTripleShapes k).filter (threeHighTripleNoCommonNeighbor B)
  have hsize : threeHighTripleSupportSize D ≤ 1608 := threeHighCanonicalSupportSize_le B
  have h := threeHighTripleSupportRounds_add_stable B D (threeHighTripleSupportSize D)
    (1608 - threeHighTripleSupportSize D) (Nat.le_refl _)
  rw [Nat.add_sub_of_le hsize] at h
  unfold threeHighClosedJointSearch threeHighSupportedJointSearch threeHighTripleSupportClosure
  rw [threeHighTripleSupportUntilStable_eq_rounds]
  exact congrArg (fun E => threeHighListedJointSearch B E threeHighCanonicalResidual) h.symm

/-- The existing generic compact certificate interface accepts the executable closure. -/
theorem threeHighClosedJointSearch_sound : ThreeHighTerminalSound threeHighClosedJointSearch := by
  intro B h
  rw [threeHighClosedJointSearch_eq]
  exact threeHighSupportedJointSearch_sound 1608 B h

theorem threeHighFullClosedCandidateSearch_eq (p : ThreeBlockFirstRowParameters)
    (q : ThreeHighSecondaryTuple) :
    threeHighFullTerminalCandidateSearch threeHighClosedJointSearch p q =
      threeHighFullSupportedCandidateSearch 1608 p q := by
  simp only [threeHighFullTerminalCandidateSearch, threeHighFullSupportedCandidateSearch,
    threeHighClosedJointSearch_eq]

theorem threeHighDeficientClosedCandidateSearch_eq (p : ThreeBlockDeficientFirstRowParameters)
    (q : ThreeHighSecondaryTuple) :
    threeHighDeficientTerminalCandidateSearch threeHighClosedJointSearch p q =
      threeHighDeficientSupportedCandidateSearch 1608 p q := by
  simp only [threeHighDeficientTerminalCandidateSearch, threeHighDeficientSupportedCandidateSearch,
    threeHighClosedJointSearch_eq]

end Erdos85
#print axioms Erdos85.threeHighClosedJointSearch_eq
#print axioms Erdos85.threeHighClosedJointSearch_sound
#print axioms Erdos85.threeHighFullClosedCandidateSearch_eq
#print axioms Erdos85.threeHighDeficientClosedCandidateSearch_eq
