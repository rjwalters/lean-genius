import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeCounting
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalHsbLeaves

/-! # H7/T0 completion exclusion from `hsb` evidence on the structural cubes

The 15 counting cubes are excluded in Lean.  For each of the 28 structural
cubes it suffices to have either a checked UNSAT proof of the cube CNF or a
semantic exclusion; `hsb` evidence (UNSAT of `cube ∧ hsb<depth>`, or checked
leaves plus a checked cover) supplies the latter.  This module does not
import the positive-triple certificate modules; the stratum-level wrapper is
in `...CanonicalHsbStratumCapstone`.
-/

namespace Erdos85

/-- Semantic exclusions of the 28 structural cubes exclude every canonical
H7/T0 completion. -/
theorem sevenHighT0Canonical_noCompletion_of_structuralSemanticExclusion
    (hstruct : ∀ edgeCount typeIndex,
      (edgeCount, typeIndex) ∈ sevenHighT0StructuralCubes →
        SevenHighT0CanonicalEmptyCubeSemanticExclusion edgeCount typeIndex) :
    ∀ (H : SimpleGraph SevenHighT0CanonicalIndex) (_ : DecidableRel H.Adj),
      SevenHighT0CanonicalCompletionSemantics H → False := by
  have hmixed : ∀ edgeCount typeIndex,
      ((edgeCount, typeIndex) ∈ sevenHighT0CountingCubes ∨
        (edgeCount, typeIndex) ∈ sevenHighT0StructuralCubes) →
      SevenHighT0CanonicalEmptyCubeMixedEvidence edgeCount typeIndex := by
    intro edgeCount typeIndex h
    rcases h with h | h
    · exact .semantic
        (sevenHighT0CanonicalEmptyCube_semanticExclusion_of_counting h)
    · exact .semantic (hstruct _ _ h)
  obtain ⟨h6, h7, h8, h9⟩ := sevenHighT0EmptyCube_counting_or_structural
  exact sevenHighT0Canonical_noCompletion_of_mixedEvidenceVectors
    (fun i => hmixed _ _ (h6 i)) (fun i => hmixed _ _ (h7 i))
    (fun i => hmixed _ _ (h8 i)) (fun i => hmixed _ _ (h9 i))

/-- UNSAT of `cube ∧ hsb<depth>` for the 28 structural cubes excludes every
canonical H7/T0 completion. -/
theorem sevenHighT0Canonical_noCompletion_of_structuralHsbUnsat
    (depth : Nat)
    (hstruct : ∀ edgeCount typeIndex,
      (edgeCount, typeIndex) ∈ sevenHighT0StructuralCubes →
        (orderFortyNineSevenHighT0CanonicalHsbCubeSatCnf
          depth edgeCount typeIndex).Unsat) :
    ∀ (H : SimpleGraph SevenHighT0CanonicalIndex) (_ : DecidableRel H.Adj),
      SevenHighT0CanonicalCompletionSemantics H → False :=
  sevenHighT0Canonical_noCompletion_of_structuralSemanticExclusion
    fun edgeCount typeIndex h =>
      sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_hsbUnsat
        depth edgeCount typeIndex (hstruct edgeCount typeIndex h)

/-- Checked `hsb` leaves and covers for the 28 structural cubes exclude every
canonical H7/T0 completion. -/
theorem sevenHighT0Canonical_noCompletion_of_structuralHsbEvidence
    (depth : Nat)
    (hstruct : ∀ edgeCount typeIndex,
      (edgeCount, typeIndex) ∈ sevenHighT0StructuralCubes →
        SevenHighT0CanonicalHsbEvidence depth edgeCount typeIndex) :
    ∀ (H : SimpleGraph SevenHighT0CanonicalIndex) (_ : DecidableRel H.Adj),
      SevenHighT0CanonicalCompletionSemantics H → False :=
  sevenHighT0Canonical_noCompletion_of_structuralSemanticExclusion
    fun edgeCount typeIndex h => (hstruct edgeCount typeIndex h).semanticExclusion

end Erdos85

#print axioms Erdos85.sevenHighT0Canonical_noCompletion_of_structuralSemanticExclusion
#print axioms Erdos85.sevenHighT0Canonical_noCompletion_of_structuralHsbUnsat
#print axioms Erdos85.sevenHighT0Canonical_noCompletion_of_structuralHsbEvidence
