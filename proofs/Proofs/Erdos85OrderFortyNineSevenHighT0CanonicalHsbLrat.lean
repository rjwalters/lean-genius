import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalHsbLeaves
import Proofs.Erdos85CubeTreeComposition

/-! Certificate-facing LRAT interface for the exact H7 hsb leaf and cover
formulas. The existing extension-padding soundness theorem removes the
tautological padding after `LRAT.check_sound`. No certificate is supplied here.

The raw proof determines only a safe extension-variable bound. The prepared
proof is checked against the resulting exact formula, so soundness does not
require trusting parsing, renumbering, or a relation between the two arrays. -/

namespace Erdos85

open Std Sat
open Std.Tactic.BVDecide

/-- Positive Lean checker evidence for one generated leaf, allowing extension
variables through the existing tautological-padding construction. -/
def SevenHighT0CanonicalHsbLeafLratChecked
    (depth edgeCount typeIndex : Nat) (rows : List (List Nat)) : Prop :=
  ∃ rawProof preparedProof : Array LRAT.IntAction,
    LRAT.check preparedProof (LratExtensionVariables.padCnfForProof
      (orderFortyNineSevenHighT0CanonicalHsbCubeSatCnf depth edgeCount typeIndex ++
        cnfClauseNegUnits (SevenHighT0Hsb.clause rows)) rawProof)

/-- Positive Lean checker evidence for the cover of an arbitrary leaf list. -/
def SevenHighT0CanonicalHsbCoverLratChecked
    (depth edgeCount typeIndex : Nat) (leafRows : List (List (List Nat))) : Prop :=
  ∃ rawProof preparedProof : Array LRAT.IntAction,
    LRAT.check preparedProof (LratExtensionVariables.padCnfForProof
      (orderFortyNineSevenHighT0CanonicalHsbCubeSatCnf depth edgeCount typeIndex ++
        cnfOfClauseList (leafRows.map SevenHighT0Hsb.clause)) rawProof)

theorem SevenHighT0CanonicalHsbLeafLratChecked.unsat
    {depth edgeCount typeIndex : Nat} {rows : List (List Nat)}
    (h : SevenHighT0CanonicalHsbLeafLratChecked depth edgeCount typeIndex rows) :
    SevenHighT0CanonicalHsbLeafChecked depth edgeCount typeIndex rows := by
  obtain ⟨rawProof, preparedProof, hcheck⟩ := h
  exact cnf_unsat_of_extension_lrat _ rawProof preparedProof hcheck

theorem SevenHighT0CanonicalHsbCoverLratChecked.unsat
    {depth edgeCount typeIndex : Nat} {leafRows : List (List (List Nat))}
    (h : SevenHighT0CanonicalHsbCoverLratChecked depth edgeCount typeIndex leafRows) :
    SevenHighT0CanonicalHsbCoverChecked depth edgeCount typeIndex leafRows := by
  obtain ⟨rawProof, preparedProof, hcheck⟩ := h
  exact cnf_unsat_of_extension_lrat _ rawProof preparedProof hcheck

/-- The exact generated leaf inventory and its cover supply the existing H7
evidence structure when all corresponding Lean LRAT checks succeed. -/
theorem sevenHighT0CanonicalHsbEvidence_of_lratChecks
    (depth edgeCount typeIndex : Nat)
    (hleaf : ∀ rows ∈ SevenHighT0Hsb.leaves depth
        (sevenHighT0CanonicalEmptyRepresentativeMask edgeCount typeIndex),
      SevenHighT0CanonicalHsbLeafLratChecked depth edgeCount typeIndex rows)
    (hcover : SevenHighT0CanonicalHsbCoverLratChecked depth edgeCount typeIndex
      (SevenHighT0Hsb.leaves depth
        (sevenHighT0CanonicalEmptyRepresentativeMask edgeCount typeIndex))) :
    SevenHighT0CanonicalHsbEvidence depth edgeCount typeIndex where
  cover := hcover.unsat
  leaf := fun rows hrows => (hleaf rows hrows).unsat

/-- An arbitrary checked leaf list may also be consumed directly; its checked
cover supplies exhaustiveness even when it differs from the generated list. -/
theorem sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_hsbLratChecks
    (depth edgeCount typeIndex : Nat) (leafRows : List (List (List Nat)))
    (hleaf : ∀ rows ∈ leafRows,
      SevenHighT0CanonicalHsbLeafLratChecked depth edgeCount typeIndex rows)
    (hcover : SevenHighT0CanonicalHsbCoverLratChecked depth edgeCount typeIndex leafRows) :
    SevenHighT0CanonicalEmptyCubeSemanticExclusion edgeCount typeIndex :=
  sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_hsbLeaves
    depth edgeCount typeIndex leafRows (fun rows hrows => (hleaf rows hrows).unsat)
    hcover.unsat

end Erdos85

#print axioms Erdos85.SevenHighT0CanonicalHsbLeafLratChecked.unsat
#print axioms Erdos85.SevenHighT0CanonicalHsbCoverLratChecked.unsat
#print axioms Erdos85.sevenHighT0CanonicalHsbEvidence_of_lratChecks
#print axioms Erdos85.sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_hsbLratChecks
