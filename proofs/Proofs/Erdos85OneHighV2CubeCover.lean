import Proofs.Erdos85CnfCubeCover
import Proofs.Erdos85OneHighV2Exclusion

/-!
# Exhaustive CUBE25 certificates for exact-v2 one-high formulas

The operational solver branches on DIMACS edge variables `301..305` and
`456..460`.  `Std.Sat.CNF` uses zero-based identifiers, hence the arrays below.
For each base formula, two checked negative cover formulas establish that a
satisfying assignment selects one variable from each array; the 25 checked
positive two-unit cubes then exclude every selection.
-/

namespace Erdos85

open Std Sat
open Std.Tactic.BVDecide

def oneHighV2CubeLeftVariables : Array Nat := #[300, 301, 302, 303, 304]

def oneHighV2CubeRightVariables : Array Nat := #[455, 456, 457, 458, 459]

def oneHighFamilyV2LeftCoverCnf (profile : Nat) (table : OneHighMissTable) :
    CNF Nat :=
  cnfWithUnits (oneHighFamilyV2SatCnf profile table)
    (negativeUnits oneHighV2CubeLeftVariables)

def oneHighFamilyV2RightCoverCnf (profile : Nat) (table : OneHighMissTable) :
    CNF Nat :=
  cnfWithUnits (oneHighFamilyV2SatCnf profile table)
    (negativeUnits oneHighV2CubeRightVariables)

def oneHighFamilyV2PositiveCubeCnf
    (profile : Nat) (table : OneHighMissTable) (left right : Nat) : CNF Nat :=
  cnfWithUnits (oneHighFamilyV2SatCnf profile table)
    (positiveTwoCube left right)

/-- Certificate-facing package for one complete 5-by-5 cube cover. -/
structure OneHighFamilyV2CheckedCubeCover
    (profile : Nat) (table : OneHighMissTable) : Prop where
  nonzero : ∀ clause ∈ (oneHighFamilyV2Clauses profile table).clauses,
    DimacsClauseNonzero clause
  leftCover : (oneHighFamilyV2LeftCoverCnf profile table).Unsat
  rightCover : (oneHighFamilyV2RightCoverCnf profile table).Unsat
  cubes : ∀ left ∈ oneHighV2CubeLeftVariables,
    ∀ right ∈ oneHighV2CubeRightVariables,
      (oneHighFamilyV2PositiveCubeCnf profile table left right).Unsat

theorem cnfUnsat_of_lrat
    {cnf : CNF Nat} (proof : Array LRAT.IntAction)
    (hcheck : LRAT.check proof cnf) : cnf.Unsat :=
  LRAT.check_sound proof cnf hcheck

/-- A complete checked CUBE25 package is interchangeable with a monolithic
checked certificate at the graph-exclusion boundary. -/
theorem oneHighFamilyV2CheckedUnsat_of_cubeCover
    {profile : Nat} {table : OneHighMissTable}
    (hcover : OneHighFamilyV2CheckedCubeCover profile table) :
    OneHighFamilyV2CheckedUnsat profile table where
  nonzero := hcover.nonzero
  unsat := by
    have hunsat : (oneHighFamilyV2SatCnf profile table).Unsat :=
      cnf_unsat_of_exhaustive_twoCubes
        (oneHighFamilyV2SatCnf profile table)
        oneHighV2CubeLeftVariables oneHighV2CubeRightVariables
        hcover.leftCover hcover.rightCover hcover.cubes
    intro assignment hsat
    rw [CNF.sat_def] at hsat
    have hfalse := hunsat assignment
    rw [hsat] at hfalse
    contradiction

end Erdos85
