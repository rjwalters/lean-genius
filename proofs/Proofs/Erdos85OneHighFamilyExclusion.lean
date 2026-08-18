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

open Std.Tactic.BVDecide

structure OneHighPureFamilyCheckedUnsat (a : Nat) : Prop where
  nonzero : ∀ clause ∈ (oneHighFamilyPureClauses a).clauses,
    DimacsClauseNonzero clause
  unsat : ∀ assignment : Nat → Bool,
    ¬(oneHighFamilyPureSatCnf a).Sat assignment

theorem oneHighPureFamilyCheckedUnsat_of_lrat
    {a : Nat}
    (hnz : ∀ clause ∈ (oneHighFamilyPureClauses a).clauses,
      DimacsClauseNonzero clause)
    (proof : Array LRAT.IntAction)
    (hcheck : LRAT.check proof (oneHighFamilyPureSatCnf a)) :
    OneHighPureFamilyCheckedUnsat a where
  nonzero := hnz
  unsat := by
    intro assignment hsat
    rw [Std.Sat.CNF.sat_def] at hsat
    have hu := LRAT.check_sound proof (oneHighFamilyPureSatCnf a) hcheck
      assignment
    rw [hsat] at hu
    contradiction

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

/-- Direct five-LRAT entry point.  Certificate modules need only supply the
embedded proofs, positive checker results, and their independently checked
nonzero DIMACS profiles. -/
theorem orderFortyNineStratumExcluded_one_of_pureFamilyLratChecks
    (hnz0 : ∀ clause ∈ (oneHighFamilyPureClauses 0).clauses,
      DimacsClauseNonzero clause)
    (hnz1 : ∀ clause ∈ (oneHighFamilyPureClauses 1).clauses,
      DimacsClauseNonzero clause)
    (hnz2 : ∀ clause ∈ (oneHighFamilyPureClauses 2).clauses,
      DimacsClauseNonzero clause)
    (hnz3 : ∀ clause ∈ (oneHighFamilyPureClauses 3).clauses,
      DimacsClauseNonzero clause)
    (hnz4 : ∀ clause ∈ (oneHighFamilyPureClauses 4).clauses,
      DimacsClauseNonzero clause)
    (proof0 proof1 proof2 proof3 proof4 : Array LRAT.IntAction)
    (hcheck0 : LRAT.check proof0 (oneHighFamilyPureSatCnf 0))
    (hcheck1 : LRAT.check proof1 (oneHighFamilyPureSatCnf 1))
    (hcheck2 : LRAT.check proof2 (oneHighFamilyPureSatCnf 2))
    (hcheck3 : LRAT.check proof3 (oneHighFamilyPureSatCnf 3))
    (hcheck4 : LRAT.check proof4 (oneHighFamilyPureSatCnf 4)) :
    OrderFortyNineStratumExcluded 1 := by
  apply orderFortyNineStratumExcluded_one_of_pureFamilySatUnsat
  · exact oneHighPureFamilyCheckedUnsat_of_lrat hnz0 proof0 hcheck0
  · exact oneHighPureFamilyCheckedUnsat_of_lrat hnz1 proof1 hcheck1
  · exact oneHighPureFamilyCheckedUnsat_of_lrat hnz2 proof2 hcheck2
  · exact oneHighPureFamilyCheckedUnsat_of_lrat hnz3 proof3 hcheck3
  · exact oneHighPureFamilyCheckedUnsat_of_lrat hnz4 proof4 hcheck4

end Erdos85
