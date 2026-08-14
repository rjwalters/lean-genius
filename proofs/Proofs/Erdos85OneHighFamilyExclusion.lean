import Proofs.Erdos85OneHighFamilyCnfSatisfaction
import Proofs.Erdos85OrderFortyNineStrataCapstone

/-!
# Certificate-facing exclusion of the one-high family

This file is the final socket between the five generated PURE family CNFs and
the order-49 stratum capstone.  Its hypotheses have exactly the shape supplied
by checked LRAT theorems: no Boolean assignment satisfies the corresponding
`Std.Sat.CNF`.
-/

namespace Erdos85

structure OneHighPureFamilyCheckedUnsat (a : Nat) : Prop where
  nonzero : ∀ clause ∈ (oneHighFamilyPureClauses a).clauses,
    DimacsClauseNonzero clause
  unsat : ∀ assignment : Nat → Bool,
    ¬(oneHighFamilyPureSatCnf a).Sat assignment

theorem oneHighPureFamilyExcluded_of_satUnsat
    {a : Nat} (hchecked : OneHighPureFamilyCheckedUnsat a) :
    OneHighPureFamilyExcluded a := by
  intro R _ hc
  rcases oneHighFamilyPureSatCnf_sat_of_constraints a R hc hchecked.nonzero with
    ⟨assignment, hsat⟩
  exact hchecked.unsat assignment hsat

/-- The exact five-certificate terminal for the one-high order-49 stratum. -/
theorem orderFortyNineStratumExcluded_one_of_pureFamilySatUnsat
    (hBBBB : OneHighPureFamilyCheckedUnsat 0)
    (hABBB : OneHighPureFamilyCheckedUnsat 1)
    (hAABB : OneHighPureFamilyCheckedUnsat 2)
    (hAAAB : OneHighPureFamilyCheckedUnsat 3)
    (hAAAA : OneHighPureFamilyCheckedUnsat 4) :
    OrderFortyNineStratumExcluded 1 := by
  apply orderFortyNineStratumExcluded_one_of_pureFamilies
  · exact oneHighPureFamilyExcluded_of_satUnsat hBBBB
  · exact oneHighPureFamilyExcluded_of_satUnsat hABBB
  · exact oneHighPureFamilyExcluded_of_satUnsat hAABB
  · exact oneHighPureFamilyExcluded_of_satUnsat hAAAB
  · exact oneHighPureFamilyExcluded_of_satUnsat hAAAA

end Erdos85
