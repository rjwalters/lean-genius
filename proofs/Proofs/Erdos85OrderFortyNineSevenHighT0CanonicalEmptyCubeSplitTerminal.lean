import Proofs.Erdos85CnfBinarySplit
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeTerminal

/-!
# Binary-split terminal for canonical H7/T0 empty cubes

This adapter lets the external cube-and-conquer campaign replace a hard
canonical `(F,type)` parent certificate by two certificates obtained by
fixing one additional SAT variable.  Split variables here are zero-based Lean
SAT variables; an external one-based DIMACS split id `d` is therefore passed
as `d - 1`.
-/

namespace Erdos85

open Std Sat
open Std.Tactic.BVDecide

/-- The child CNF for one Boolean branch of a canonical empty-cube split. -/
def orderFortyNineSevenHighT0CanonicalEmptyCubeSplitSatCnf
    (edgeCount typeIndex splitVariable : Nat) (value : Bool) : CNF Nat :=
  cnfWithSignedUnit
    (orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf edgeCount typeIndex)
    splitVariable value

/-- Checked LRAT witnesses for both children of every canonical empty cube
supply the parent-level provider consumed by the semantic terminal. -/
theorem sevenHighT0CanonicalEmptyCubeCheckedProvider_of_binarySplitLratChecks
    (splitVariable : Nat → Nat → Nat)
    (hchecks : ∀ edgeCount, 6 ≤ edgeCount → edgeCount ≤ 9 →
      ∀ typeIndex,
        typeIndex <
          (sevenHighT0CanonicalEmptyRepresentativeMasks edgeCount).length →
        ∀ value : Bool,
          ∃ proof : Array LRAT.IntAction,
            LRAT.check proof
              (orderFortyNineSevenHighT0CanonicalEmptyCubeSplitSatCnf
                edgeCount typeIndex (splitVariable edgeCount typeIndex) value)) :
    SevenHighT0CanonicalEmptyCubeCheckedProvider := by
  intro edgeCount hlow hhigh typeIndex hindex
  have branchUnsat : ∀ value : Bool,
      (orderFortyNineSevenHighT0CanonicalEmptyCubeSplitSatCnf
        edgeCount typeIndex (splitVariable edgeCount typeIndex) value).Unsat := by
    intro value
    obtain ⟨proof, hcheck⟩ :=
      hchecks edgeCount hlow hhigh typeIndex hindex value
    exact LRAT.check_sound proof _ hcheck
  exact cnf_unsat_of_binaryUnitSplit
    (orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf edgeCount typeIndex)
    (splitVariable edgeCount typeIndex)
    (branchUnsat false) (branchUnsat true)

/-- Per-parent certificate evidence for the mixed campaign: already completed
parents retain their direct LRAT, while hard parents may instead provide the
two leaves of one exhaustive binary split. -/
inductive SevenHighT0CanonicalEmptyCubeLratEvidence
    (edgeCount typeIndex : Nat) : Prop where
  | direct (proof : Array LRAT.IntAction)
      (checked : LRAT.check proof
        (orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf
          edgeCount typeIndex))
  | binarySplit (splitVariable : Nat)
      (falseProof trueProof : Array LRAT.IntAction)
      (falseChecked : LRAT.check falseProof
        (orderFortyNineSevenHighT0CanonicalEmptyCubeSplitSatCnf
          edgeCount typeIndex splitVariable false))
      (trueChecked : LRAT.check trueProof
        (orderFortyNineSevenHighT0CanonicalEmptyCubeSplitSatCnf
          edgeCount typeIndex splitVariable true))
  | binaryTree
      (tree : CnfBinaryCheckedTree
        (orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf
          edgeCount typeIndex))

/-- Either form of campaign evidence proves its canonical parent cube UNSAT. -/
theorem SevenHighT0CanonicalEmptyCubeLratEvidence.unsat
    {edgeCount typeIndex : Nat}
    (evidence : SevenHighT0CanonicalEmptyCubeLratEvidence
      edgeCount typeIndex) :
    SevenHighT0CanonicalEmptyCubeChecked edgeCount typeIndex := by
  cases evidence with
  | direct proof checked =>
      exact LRAT.check_sound proof _ checked
  | binarySplit splitVariable falseProof trueProof falseChecked trueChecked =>
      exact cnf_unsat_of_binaryUnitSplit
        (orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf edgeCount typeIndex)
        splitVariable
        (LRAT.check_sound falseProof _ falseChecked)
        (LRAT.check_sound trueProof _ trueChecked)
  | binaryTree tree =>
      exact tree.unsat

/-- A heterogeneous manifest containing direct certificates for completed
parents and binary-split certificates for the remaining parents supplies the
same bounded checked provider. -/
theorem sevenHighT0CanonicalEmptyCubeCheckedProvider_of_lratEvidence
    (evidence : ∀ edgeCount, 6 ≤ edgeCount → edgeCount ≤ 9 →
      ∀ typeIndex,
        typeIndex <
          (sevenHighT0CanonicalEmptyRepresentativeMasks edgeCount).length →
        SevenHighT0CanonicalEmptyCubeLratEvidence edgeCount typeIndex) :
    SevenHighT0CanonicalEmptyCubeCheckedProvider := by
  intro edgeCount hlow hhigh typeIndex hindex
  exact (evidence edgeCount hlow hhigh typeIndex hindex).unsat

/-- The certificate generator's exact `19/15/7/2` inventory, exposed without
requiring generated code to repeat arithmetic dispatch over bounded naturals. -/
theorem sevenHighT0CanonicalEmptyCubeCheckedProvider_of_evidenceVectors
    (e6 : ∀ i : Fin 19,
      SevenHighT0CanonicalEmptyCubeLratEvidence 6 i)
    (e7 : ∀ i : Fin 15,
      SevenHighT0CanonicalEmptyCubeLratEvidence 7 i)
    (e8 : ∀ i : Fin 7,
      SevenHighT0CanonicalEmptyCubeLratEvidence 8 i)
    (e9 : ∀ i : Fin 2,
      SevenHighT0CanonicalEmptyCubeLratEvidence 9 i) :
    SevenHighT0CanonicalEmptyCubeCheckedProvider := by
  intro edgeCount hlow hhigh typeIndex hindex
  interval_cases edgeCount
  · have hcount :
        (sevenHighT0CanonicalEmptyRepresentativeMasks 6).length = 19 := by rfl
    exact (e6 ⟨typeIndex, by omega⟩).unsat
  · have hcount :
        (sevenHighT0CanonicalEmptyRepresentativeMasks 7).length = 15 := by rfl
    exact (e7 ⟨typeIndex, by omega⟩).unsat
  · have hcount :
        (sevenHighT0CanonicalEmptyRepresentativeMasks 8).length = 7 := by rfl
    exact (e8 ⟨typeIndex, by omega⟩).unsat
  · have hcount :
        (sevenHighT0CanonicalEmptyRepresentativeMasks 9).length = 2 := by rfl
    exact (e9 ⟨typeIndex, by omega⟩).unsat

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalEmptyCubeCheckedProvider_of_binarySplitLratChecks
#print axioms Erdos85.SevenHighT0CanonicalEmptyCubeLratEvidence.unsat
#print axioms Erdos85.sevenHighT0CanonicalEmptyCubeCheckedProvider_of_lratEvidence
#print axioms Erdos85.sevenHighT0CanonicalEmptyCubeCheckedProvider_of_evidenceVectors
