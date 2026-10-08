import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptySemanticOrbitCover
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeSatisfaction
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalCnfTerminal

/-!
# Semantic exclusion of canonical H7/T0 empty cubes (mixed evidence)

The LRAT-only capstone
`orderFortyNineStratumExcluded_seven_of_emptyCubeEvidenceVectors` requires a
checked UNSAT certificate for each of the 43 canonical empty cubes.  Some
cubes are instead excluded by a direct graph argument (for example the
singleton-capacity counting argument).  This file defines, per cube, a
*semantic exclusion*: no canonical completion graph has that cube's
representative empty-sector mask.

The semantic cover reaches a cube only through
`exists_relabel_emptyRepresentative`, which produces a canonical completion
graph whose empty-sector mask equals the representative mask, so semantic
exclusion of all 43 cubes excludes every canonical completion.  UNSAT of a
cube CNF implies its semantic exclusion through the compact-CNF satisfaction
bridge, so mixed evidence strictly generalizes the checked-UNSAT route.

This module deliberately avoids importing the positive-triple certificate
modules (`...CanonicalTerminal`), so it builds without the external LRAT
files; the stratum-level wrapper lives in
`Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeMixedCapstone`.
-/

namespace Erdos85

open Std Sat

/-- Semantic exclusion of one canonical `(F,type)` empty cube: no canonical
H7/T0 completion graph has the cube's representative empty-sector mask. -/
def SevenHighT0CanonicalEmptyCubeSemanticExclusion
    (edgeCount typeIndex : Nat) : Prop :=
  ∀ (H : SimpleGraph SevenHighT0CanonicalIndex) (_ : DecidableRel H.Adj),
    SevenHighT0CanonicalCompletionSemantics H →
      sevenHighT0CanonicalEmptySemanticMask H ≠
        sevenHighT0CanonicalEmptyRepresentativeMask edgeCount typeIndex

/-- A checked UNSAT cube CNF yields the semantic exclusion of that cube. -/
theorem SevenHighT0CanonicalEmptyCubeChecked.semanticExclusion
    {edgeCount typeIndex : Nat}
    (hunsat : SevenHighT0CanonicalEmptyCubeChecked edgeCount typeIndex) :
    SevenHighT0CanonicalEmptyCubeSemanticExclusion edgeCount typeIndex := by
  intro H _ semantics hmask
  obtain ⟨val, hbase, hagree⟩ := sevenHighT0CanonicalBaseSat H semantics
  have hsat := sevenHighT0CanonicalEmptyRepresentativeCube_sat
    H val edgeCount typeIndex hbase hagree hmask
  have hfalse := hunsat (satAssignmentOfDimacs val)
  rw [CNF.sat_def] at hsat
  rw [hsat] at hfalse
  contradiction

/-- Per-cube evidence for the mixed campaign: either a checked UNSAT proof
of the cube CNF (any LRAT evidence supplies one via `.unsat`) or a semantic
exclusion. -/
inductive SevenHighT0CanonicalEmptyCubeMixedEvidence
    (edgeCount typeIndex : Nat) : Prop where
  | checked (unsat : SevenHighT0CanonicalEmptyCubeChecked
      edgeCount typeIndex)
  | semantic (exclusion : SevenHighT0CanonicalEmptyCubeSemanticExclusion
      edgeCount typeIndex)

/-- Either kind of mixed evidence gives the semantic exclusion. -/
theorem SevenHighT0CanonicalEmptyCubeMixedEvidence.exclusion
    {edgeCount typeIndex : Nat}
    (evidence : SevenHighT0CanonicalEmptyCubeMixedEvidence
      edgeCount typeIndex) :
    SevenHighT0CanonicalEmptyCubeSemanticExclusion edgeCount typeIndex := by
  cases evidence with
  | checked unsat => exact unsat.semanticExclusion
  | semantic exclusion => exact exclusion

/-- Semantic exclusion of all 43 canonical empty cubes excludes every
canonical H7/T0 completion (this is `SevenHighT0CanonicalCompletionExcluded`
unfolded). -/
theorem sevenHighT0Canonical_noCompletion_of_semanticExclusions
    (hexcluded : ∀ edgeCount, 6 ≤ edgeCount → edgeCount ≤ 9 →
      ∀ typeIndex,
        typeIndex <
          (sevenHighT0CanonicalEmptyRepresentativeMasks edgeCount).length →
        SevenHighT0CanonicalEmptyCubeSemanticExclusion edgeCount typeIndex) :
    ∀ (H : SimpleGraph SevenHighT0CanonicalIndex) (_ : DecidableRel H.Adj),
      SevenHighT0CanonicalCompletionSemantics H → False := by
  intro H _ semantics
  obtain ⟨edgeCount, hlow, hhigh, typeIndex, hindex, σ,
      relabeledSemantics, hmask⟩ :=
    semantics.exists_relabel_emptyRepresentative
  exact hexcluded edgeCount hlow hhigh typeIndex hindex
    (sevenHighT0CanonicalRelabel σ H) inferInstance relabeledSemantics hmask

/-- Mixed evidence vectors over the exact `19/15/7/2` inventory exclude every
canonical H7/T0 completion. -/
theorem sevenHighT0Canonical_noCompletion_of_mixedEvidenceVectors
    (e6 : ∀ i : Fin 19,
      SevenHighT0CanonicalEmptyCubeMixedEvidence 6 i)
    (e7 : ∀ i : Fin 15,
      SevenHighT0CanonicalEmptyCubeMixedEvidence 7 i)
    (e8 : ∀ i : Fin 7,
      SevenHighT0CanonicalEmptyCubeMixedEvidence 8 i)
    (e9 : ∀ i : Fin 2,
      SevenHighT0CanonicalEmptyCubeMixedEvidence 9 i) :
    ∀ (H : SimpleGraph SevenHighT0CanonicalIndex) (_ : DecidableRel H.Adj),
      SevenHighT0CanonicalCompletionSemantics H → False := by
  apply sevenHighT0Canonical_noCompletion_of_semanticExclusions
  intro edgeCount hlow hhigh typeIndex hindex
  interval_cases edgeCount
  · have hcount :
        (sevenHighT0CanonicalEmptyRepresentativeMasks 6).length = 19 := by rfl
    exact (e6 ⟨typeIndex, by omega⟩).exclusion
  · have hcount :
        (sevenHighT0CanonicalEmptyRepresentativeMasks 7).length = 15 := by rfl
    exact (e7 ⟨typeIndex, by omega⟩).exclusion
  · have hcount :
        (sevenHighT0CanonicalEmptyRepresentativeMasks 8).length = 7 := by rfl
    exact (e8 ⟨typeIndex, by omega⟩).exclusion
  · have hcount :
        (sevenHighT0CanonicalEmptyRepresentativeMasks 9).length = 2 := by rfl
    exact (e9 ⟨typeIndex, by omega⟩).exclusion

end Erdos85

#print axioms Erdos85.SevenHighT0CanonicalEmptyCubeChecked.semanticExclusion
#print axioms Erdos85.SevenHighT0CanonicalEmptyCubeMixedEvidence.exclusion
#print axioms Erdos85.sevenHighT0Canonical_noCompletion_of_semanticExclusions
#print axioms Erdos85.sevenHighT0Canonical_noCompletion_of_mixedEvidenceVectors
