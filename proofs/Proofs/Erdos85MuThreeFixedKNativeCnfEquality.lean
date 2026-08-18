import Proofs.Erdos85MuThreeFixedKNativeData
import Proofs.Erdos85MuThreeFixedKNativeCertificates
import Proofs.Erdos85MuThreeAllTfNativeCertificates

/-!
# Equality of the fixed-K native generators and checked DIMACS inputs

This is the external-artifact boundary.  It proves by executable comparison
that the DIMACS formula accepted by each LRAT certificate is exactly the SAT
CNF emitted inside Lean from the corresponding ordered fixed grid.
-/

namespace Erdos85

open Std Sat
open Std.Tactic.BVDecide

private theorem fixedK_clauseEval_extensionTautology
    (assignment : Nat → Bool) (extensionVar : Nat) :
    CNF.Clause.eval assignment [(extensionVar, true), (extensionVar, false)] = true := by
  cases h : assignment extensionVar <;> simp [CNF.Clause.eval, h]

private theorem fixedK_unsat_of_push_extensionTautology_unsat
    (cnf : CNF Nat) (extensionVar : Nat)
    (hunsat : (cnf.add [(extensionVar, true), (extensionVar, false)]).Unsat) :
    cnf.Unsat := by
  intro assignment
  have hpadded := hunsat assignment
  rw [CNF.eval_add, fixedK_clauseEval_extensionTautology] at hpadded
  exact hpadded

private theorem fixedK_unsat_of_padCnfForProof_unsat (cnf : CNF Nat)
    (rawProof : Array LRAT.IntAction)
    (hunsat : (LratExtensionVariables.padCnfForProof cnf rawProof).Unsat) :
    cnf.Unsat := by
  rw [LratExtensionVariables.padCnfForProof] at hunsat
  split at hunsat
  · apply fixedK_unsat_of_push_extensionTautology_unsat cnf _
    simpa [CNF.add] using hunsat
  · exact hunsat

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- Every checked fixed-K DIMACS input has exactly the clauses emitted by the
corresponding Lean-native generator.  We state this at the clause-array level
because `Std.Sat.CNF` does not expose a decidable equality instance. -/
theorem mu3FixedKCnf_clauses_eq_native (i : Fin 19) :
    (mu3FixedKCnf i).clauses =
      (mu3GridNativeSatCnf (mu3FixedKGrid (mu3FixedKOldIndex i))).clauses := by
  fin_cases i <;> native_decide

/-- Structure-level form of the executable clause comparison. -/
theorem mu3FixedKCnf_eq_native (i : Fin 19) :
    mu3FixedKCnf i =
      mu3GridNativeSatCnf (mu3FixedKGrid (mu3FixedKOldIndex i)) := by
  have hclauses := mu3FixedKCnf_clauses_eq_native i
  cases hparsed : mu3FixedKCnf i
  cases hnative : mu3GridNativeSatCnf
    (mu3FixedKGrid (mu3FixedKOldIndex i))
  rw [hparsed, hnative] at hclauses
  congr

/-- Removing the logically inert LRAT extension-variable padding recovers
UNSAT of the exact DIMACS formula. -/
theorem mu3FixedKCnf_unsat (i : Fin 19) :
    (mu3FixedKCnf i).Unsat := by
  have hpadded := mu3FixedKPaddedCnf_unsat i
  unfold mu3FixedKPaddedCnf at hpadded
  exact fixedK_unsat_of_padCnfForProof_unsat _ _ hpadded

/-- The Lean-native generator itself is unsatisfiable for every one of the
nineteen fixed-K survivors. -/
theorem mu3FixedKOldNativeCnf_unsat (i : Fin 19) :
    (mu3GridNativeSatCnf
      (mu3FixedKGrid (mu3FixedKOldIndex i))).Unsat := by
  rw [← mu3FixedKCnf_eq_native i]
  exact mu3FixedKCnf_unsat i

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- The uniform twenty-two-slot native manifest is UNSAT.  The first
nineteen entries use the new fixed-K LRAT records; the final three reuse the
already-checked all-TF certificates through the definitionally identical
grid generator. -/
theorem mu3FixedKNativeCnf_unsat (i : Fin 22) :
    (mu3GridNativeSatCnf (mu3FixedKGrid i)).Unsat := by
  by_cases h : i.val < 19
  · let j : Fin 19 := ⟨i.val, h⟩
    have hij : mu3FixedKOldIndex j = i := Fin.ext rfl
    rw [← hij]
    exact mu3FixedKOldNativeCnf_unsat j
  · have hi : i.val = 19 ∨ i.val = 20 ∨ i.val = 21 := by omega
    rcases hi with hi | hi | hi
    · have : i = (19 : Fin 22) := Fin.ext hi
      subst i
      change (mu3GridNativeSatCnf (.ofAllTfShape .c16)).Unsat
      rw [mu3GridNativeSatCnf_ofAllTfShape]
      exact mu3AllTfNativeC16_unsat
    · have : i = (20 : Fin 22) := Fin.ext hi
      subst i
      change (mu3GridNativeSatCnf (.ofAllTfShape .c8c8)).Unsat
      rw [mu3GridNativeSatCnf_ofAllTfShape]
      exact mu3AllTfNativeC8C8_unsat
    · have : i = (21 : Fin 22) := Fin.ext hi
      subst i
      change (mu3GridNativeSatCnf (.ofAllTfShape .c10c6)).Unsat
      rw [mu3GridNativeSatCnf_ofAllTfShape]
      exact mu3AllTfNativeC10C6_unsat

/-- Consequently, the checked padded formula is unsatisfiable for the exact
native generator input, up to the logically inert LRAT extension padding. -/
theorem mu3FixedKNativePadded_unsat (i : Fin 19) :
    (mu3FixedKPaddedCnf i).Unsat :=
  mu3FixedKPaddedCnf_unsat i

end Erdos85

#print axioms Erdos85.mu3FixedKCnf_clauses_eq_native
#print axioms Erdos85.mu3FixedKCnf_eq_native
#print axioms Erdos85.mu3FixedKCnf_unsat
#print axioms Erdos85.mu3FixedKNativeCnf_unsat
#print axioms Erdos85.mu3FixedKNativePadded_unsat
