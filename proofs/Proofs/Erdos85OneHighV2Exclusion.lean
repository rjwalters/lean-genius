import Proofs.Erdos85OneHighV2F3bRawLedger
import Proofs.Erdos85OrderFortyNineStrataCapstone

/-! # Certificate-facing exclusion for the exact v2 one-high formula -/

namespace Erdos85

open Std.Tactic.BVDecide
open SimpleGraph

structure OneHighFamilyV2CheckedUnsat
    (profile : Nat) (table : OneHighMissTable) : Prop where
  nonzero : ∀ clause ∈ (oneHighFamilyV2Clauses profile table).clauses,
    DimacsClauseNonzero clause
  unsat : ∀ assignment : Nat → Bool,
    ¬(oneHighFamilyV2SatCnf profile table).Sat assignment

theorem oneHighFamilyV2CheckedUnsat_of_lrat
    {profile : Nat} {table : OneHighMissTable}
    (hnz : ∀ clause ∈ (oneHighFamilyV2Clauses profile table).clauses,
      DimacsClauseNonzero clause)
    (proof : Array LRAT.IntAction)
    (hcheck : LRAT.check proof (oneHighFamilyV2SatCnf profile table)) :
    OneHighFamilyV2CheckedUnsat profile table where
  nonzero := hnz
  unsat := by
    intro assignment hsat
    rw [Std.Sat.CNF.sat_def] at hsat
    have hu := LRAT.check_sound proof
      (oneHighFamilyV2SatCnf profile table) hcheck assignment
    rw [hsat] at hu
    contradiction

theorem oneHighFamilyV2DimacsUnsat_of_checked
    {profile : Nat} {table : OneHighMissTable}
    (hchecked : OneHighFamilyV2CheckedUnsat profile table) :
    OneHighFamilyV2DimacsUnsat profile table := by
  intro val hval
  apply hchecked.unsat (satAssignmentOfDimacs val)
  simpa [oneHighFamilyV2SatCnf] using
    satCnf_of_dimacsFormulaSatisfied hchecked.nonzero hval

theorem false_of_rawOneHigh_v2Checked
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (hunique : ∀ {w : V}, G.degree w = 8 → w = v)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hmateInv : Function.Involutive mate)
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1)
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (hbranchMate : ∀ s,
      branchLabel (mate s) = oneHighStandardMate (branchLabel s))
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (profile : Nat)
    (hc : OneHighPureFamilyCnfConstraints profile
      (oneHighRelabeledLeafGraph G v
        (oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel)))
    (hchecked : OneHighFamilyV2CheckedUnsat profile
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel))
        profile)) : False := by
  let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
  let R := oneHighRelabeledLeafGraph G v E
  have f₁ := oneHighFamilyV2F1Ledger_of_constraints profile R hc
  have f₂ := oneHighFamilyV2F2Ledger_of_constraints profile R hc
  have f₃a := oneHighFamilyV2F3aLedger_of_constraints profile R hc
  have f₃b := oneHighFamilyV2F3bLedger_of_rawGraph
    G hfree hmin hcard hv hunique hexternal houterDegree
      mate hmateInv hmateAdj branchLabel hbranchMate leafLabel profile hc
  exact oneHighFamilyV2_constraints_false_of_dimacsUnsat
    R profile (oneHighFamilyGraphTable R profile) hc rfl
      f₁ f₂ f₃a f₃b
      (oneHighFamilyV2DimacsUnsat_of_checked hchecked)

end Erdos85
