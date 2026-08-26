import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeCnf
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalTerminal

/-!
# Checked empty-cube terminal for canonical H7/T0 completions

This file separates the two remaining obligations cleanly: semantic coverage
says every canonical completion satisfies one of the 43 stable cube CNFs;
the checked provider supplies an UNSAT proof for each such CNF.
-/

namespace Erdos85

open Std Sat
open Std.Tactic.BVDecide

/-- Every canonical completion reaches one of the bounded `F=6..9` stable
empty-sector cube CNFs.  The relabeling/orbit theorem and compact-CNF
satisfaction theorem together discharge this proposition. -/
def SevenHighT0CanonicalEmptyCubeSemanticCover : Prop :=
  ∀ (H : SimpleGraph SevenHighT0CanonicalIndex) (_ : DecidableRel H.Adj),
    SevenHighT0CanonicalCompletionSemantics H →
      ∃ edgeCount, 6 ≤ edgeCount ∧ edgeCount ≤ 9 ∧
        ∃ typeIndex,
          typeIndex <
            (sevenHighT0CanonicalEmptyRepresentativeMasks edgeCount).length ∧
          ∃ assignment : Nat → Bool,
            (orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf
              edgeCount typeIndex).Sat assignment

/-- Raw checked LRAT witnesses supply the bounded UNSAT provider expected by
the composition terminal. -/
theorem sevenHighT0CanonicalEmptyCubeCheckedProvider_of_lratChecks
    (hchecks : ∀ edgeCount, 6 ≤ edgeCount → edgeCount ≤ 9 →
      ∀ typeIndex,
        typeIndex <
          (sevenHighT0CanonicalEmptyRepresentativeMasks edgeCount).length →
        ∃ proof : Array LRAT.IntAction,
          LRAT.check proof
            (orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf
              edgeCount typeIndex)) :
    SevenHighT0CanonicalEmptyCubeCheckedProvider := by
  intro edgeCount hlow hhigh typeIndex hindex
  obtain ⟨proof, hcheck⟩ := hchecks edgeCount hlow hhigh typeIndex hindex
  exact LRAT.check_sound proof
    (orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf edgeCount typeIndex)
    hcheck

/-- Exhaustive semantic coverage plus the bounded checked provider excludes
every canonical completion. -/
theorem sevenHighT0CanonicalCompletionExcluded_of_emptyCubeChecks
    (hcover : SevenHighT0CanonicalEmptyCubeSemanticCover)
    (hchecks : SevenHighT0CanonicalEmptyCubeCheckedProvider) :
    SevenHighT0CanonicalCompletionExcluded := by
  intro H _ hsemantics
  obtain ⟨edgeCount, hlow, hhigh, typeIndex, hindex, assignment, hsat⟩ :=
    hcover H inferInstance hsemantics
  have hunsat := hchecks edgeCount hlow hhigh typeIndex hindex
  have hfalse := hunsat assignment
  rw [hsat] at hfalse
  contradiction

/-- The same two campaign inputs close the entire seven-high stratum, since
all positive-triple cells are already checked. -/
theorem orderFortyNineStratumExcluded_seven_of_emptyCubeChecks
    (hcover : SevenHighT0CanonicalEmptyCubeSemanticCover)
    (hchecks : SevenHighT0CanonicalEmptyCubeCheckedProvider) :
    OrderFortyNineStratumExcluded 7 :=
  orderFortyNineStratumExcluded_seven_of_canonicalCompletion
    (sevenHighT0CanonicalCompletionExcluded_of_emptyCubeChecks hcover hchecks)

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalCompletionExcluded_of_emptyCubeChecks
#print axioms Erdos85.sevenHighT0CanonicalEmptyCubeCheckedProvider_of_lratChecks
#print axioms Erdos85.orderFortyNineStratumExcluded_seven_of_emptyCubeChecks
