import Proofs.Erdos85LratRuntime
import Proofs.Erdos85OneHighV2Exclusion

/-!
# Exact-v2 certificates with LRAT extension variables

Kissat may introduce fresh variables through bounded variable addition.  The
runtime preparation in `Erdos85LratRuntime` enlarges the checker's variable
universe by appending a tautological clause.  This module proves that a
successful ordinary `LRAT.check` on that padded CNF still yields the checked
UNSAT proposition for the original exact-v2 formula.
-/

namespace Erdos85

open Std Sat
open Std.Tactic.BVDecide

theorem clauseEval_extensionTautology (assignment : Nat → Bool) (extensionVar : Nat) :
    CNF.Clause.eval assignment [(extensionVar, true), (extensionVar, false)] = true := by
  cases h : assignment extensionVar <;> simp [CNF.Clause.eval, h]

theorem cnf_unsat_of_push_extensionTautology_unsat (cnf : CNF Nat) (extensionVar : Nat)
    (hunsat : (cnf.add [(extensionVar, true), (extensionVar, false)]).Unsat) :
    cnf.Unsat := by
  intro assignment
  have hpadded := hunsat assignment
  rw [CNF.eval_add, clauseEval_extensionTautology] at hpadded
  exact hpadded

theorem cnf_unsat_of_padCnfForProof_unsat (cnf : CNF Nat)
    (rawProof : Array LRAT.IntAction)
    (hunsat : (LratExtensionVariables.padCnfForProof cnf rawProof).Unsat) :
    cnf.Unsat := by
  rw [LratExtensionVariables.padCnfForProof] at hunsat
  split at hunsat
  · apply cnf_unsat_of_push_extensionTautology_unsat cnf _
    simpa [CNF.add] using hunsat
  · exact hunsat

/-- A kernel-checked LRAT proof for the padded variable universe certifies the
original exact-v2 instance.  `preparedProof` should normally be the result of
renumbering and `LratAmbiguousRat.restore`, but soundness relies only on the
final standard `LRAT.check` hypothesis. -/
theorem oneHighFamilyV2CheckedUnsat_of_extension_lrat
    {profile : Nat} {table : OneHighMissTable}
    (hnz : ∀ clause ∈ (oneHighFamilyV2Clauses profile table).clauses,
      DimacsClauseNonzero clause)
    (rawProof preparedProof : Array LRAT.IntAction)
    (hcheck : LRAT.check preparedProof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf profile table) rawProof)) :
    OneHighFamilyV2CheckedUnsat profile table where
  nonzero := hnz
  unsat := by
    intro assignment hsat
    rw [CNF.sat_def] at hsat
    have hpadded := LRAT.check_sound preparedProof
      (LratExtensionVariables.padCnfForProof
        (oneHighFamilyV2SatCnf profile table) rawProof) hcheck
    have horiginal := cnf_unsat_of_padCnfForProof_unsat
      (oneHighFamilyV2SatCnf profile table) rawProof hpadded
    have hu := horiginal assignment
    rw [hsat] at hu
    contradiction

end Erdos85
