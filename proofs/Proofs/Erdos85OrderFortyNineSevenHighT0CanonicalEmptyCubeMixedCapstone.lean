import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeCounting
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeSplitTerminal

/-!
# Mixed-evidence H7 capstones (stratum level)

Thin wrappers turning the canonical-completion exclusions of
`...EmptyCubeSemanticExclusion` / `...EmptyCubeCounting` into
`OrderFortyNineStratumExcluded 7`.  The LRAT-only capstone
`orderFortyNineStratumExcluded_seven_of_emptyCubeEvidenceVectors` is kept.

This module imports `...CanonicalTerminal`, hence the positive-triple
certificate modules (`SevenHighT{1..7}Rep*Certificate`), which embed external
packed LRAT files by absolute host path.
-/

namespace Erdos85

/-- Per-cube LRAT campaign evidence (direct, binary split, binary tree) or a
semantic exclusion. -/
def SevenHighT0CanonicalEmptyCubeLratOrSemantic
    (edgeCount typeIndex : Nat) : Prop :=
  SevenHighT0CanonicalEmptyCubeLratEvidence edgeCount typeIndex ∨
    SevenHighT0CanonicalEmptyCubeSemanticExclusion edgeCount typeIndex

theorem SevenHighT0CanonicalEmptyCubeLratOrSemantic.mixed
    {edgeCount typeIndex : Nat}
    (h : SevenHighT0CanonicalEmptyCubeLratOrSemantic edgeCount typeIndex) :
    SevenHighT0CanonicalEmptyCubeMixedEvidence edgeCount typeIndex := by
  rcases h with h | h
  · exact .checked h.unsat
  · exact .semantic h

/-- Mixed-evidence H7 capstone: per cube, LRAT evidence or a semantic
exclusion, over the exact `19/15/7/2` inventory. -/
theorem orderFortyNineStratumExcluded_seven_of_mixedEmptyCubeEvidenceVectors
    (e6 : ∀ i : Fin 19, SevenHighT0CanonicalEmptyCubeLratOrSemantic 6 i)
    (e7 : ∀ i : Fin 15, SevenHighT0CanonicalEmptyCubeLratOrSemantic 7 i)
    (e8 : ∀ i : Fin 7, SevenHighT0CanonicalEmptyCubeLratOrSemantic 8 i)
    (e9 : ∀ i : Fin 2, SevenHighT0CanonicalEmptyCubeLratOrSemantic 9 i) :
    OrderFortyNineStratumExcluded 7 :=
  orderFortyNineStratumExcluded_seven_of_canonicalCompletion
    (sevenHighT0Canonical_noCompletion_of_mixedEvidenceVectors
      (fun i => (e6 i).mixed) (fun i => (e7 i).mixed)
      (fun i => (e8 i).mixed) (fun i => (e9 i).mixed))

/-- H7 capstone with the 15 counting classes (including `F6_t2`) discharged
in Lean: LRAT evidence for the 28 structural cubes alone suffices. -/
theorem orderFortyNineStratumExcluded_seven_of_structuralEmptyCubeEvidence
    (hstruct : ∀ edgeCount typeIndex,
      (edgeCount, typeIndex) ∈ sevenHighT0StructuralCubes →
        SevenHighT0CanonicalEmptyCubeLratEvidence edgeCount typeIndex) :
    OrderFortyNineStratumExcluded 7 :=
  orderFortyNineStratumExcluded_seven_of_canonicalCompletion
    (sevenHighT0Canonical_noCompletion_of_structuralChecked
      (fun edgeCount typeIndex h => (hstruct edgeCount typeIndex h).unsat))

end Erdos85

#print axioms Erdos85.orderFortyNineStratumExcluded_seven_of_mixedEmptyCubeEvidenceVectors
#print axioms Erdos85.orderFortyNineStratumExcluded_seven_of_structuralEmptyCubeEvidence
