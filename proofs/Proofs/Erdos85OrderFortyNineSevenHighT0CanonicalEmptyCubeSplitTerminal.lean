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

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalEmptyCubeCheckedProvider_of_binarySplitLratChecks
