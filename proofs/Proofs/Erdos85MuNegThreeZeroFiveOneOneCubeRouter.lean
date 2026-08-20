import Proofs.Erdos85MuNegThreeZeroFiveOneOneCubeCertificate

/-! # Semantic routing into the corrected h305 one/one-shore cubes -/

namespace Erdos85

open Std Sat

theorem oneone_bool_four_count_three_cases (a b c d : Bool)
    (h : [a, b, c, d].count true = 3) :
    (a = false ∧ b = true ∧ c = true ∧ d = true) ∨
    (a = true ∧ b = false ∧ c = true ∧ d = true) ∨
    (a = true ∧ b = true ∧ c = false ∧ d = true) ∨
    (a = true ∧ b = true ∧ c = true ∧ d = false) := by
  revert a b c d
  decide

private theorem false_of_sat_and_unsat {cnf : CNF Nat}
    {assignment : Nat → Bool} (hsat : cnf.Sat assignment)
    (hunsat : cnf.Unsat) : False := by
  rw [CNF.unsat_def] at hunsat
  have hf := hunsat assignment
  rw [CNF.sat_def] at hsat
  rw [hsat] at hf
  contradiction

theorem muNegThreeZeroFiveCorrectOneOneS0_false_of_formula_exactOpp
    (val : DimacsValuation)
    (hnz : ∀ clause ∈
      muNegThreeZeroFiveOwnerDimacsClauses true true false,
      DimacsClauseNonzero clause)
    (hsat : dimacsFormulaSatisfied val
      (muNegThreeZeroFiveOwnerDimacsClauses true true false))
    (hcount : [val 2, val 4, val 6, val 8].count true = 3) : False := by
  have hbase : (muNegThreeZeroFiveOwnerSatCnf true true false).Sat
      (satAssignmentOfDimacs val) := by
    simpa [muNegThreeZeroFiveOwnerSatCnf] using
      satCnf_of_dimacsFormulaSatisfied hnz hsat
  rcases oneone_bool_four_count_three_cases _ _ _ _ hcount with h0 | h1 | h2 | h3
  · rcases h0 with ⟨ha, hb, hc, hd⟩
    apply false_of_sat_and_unsat
      (hunsat := muNegThreeZeroFiveCorrectOneOneS0OppCube_unsat ⟨0, by omega⟩)
    apply (sat_cnfWithUnits_iff _ _ _).2
    refine ⟨hbase, ?_⟩
    intro i hi
    have hi4 : i < 4 := by
      simpa [muNegThreeZeroFiveCorrectOneOneS0OppUnits] using hi
    interval_cases i <;> simp [satAssignmentOfDimacs,
      muNegThreeZeroFiveCorrectOneOneS0OppUnits, ha, hb, hc, hd]
  · rcases h1 with ⟨ha, hb, hc, hd⟩
    apply false_of_sat_and_unsat
      (hunsat := muNegThreeZeroFiveCorrectOneOneS0OppCube_unsat ⟨1, by omega⟩)
    apply (sat_cnfWithUnits_iff _ _ _).2
    refine ⟨hbase, ?_⟩
    intro i hi
    have hi4 : i < 4 := by
      simpa [muNegThreeZeroFiveCorrectOneOneS0OppUnits] using hi
    interval_cases i <;> simp [satAssignmentOfDimacs,
      muNegThreeZeroFiveCorrectOneOneS0OppUnits, ha, hb, hc, hd]
  · rcases h2 with ⟨ha, hb, hc, hd⟩
    apply false_of_sat_and_unsat
      (hunsat := muNegThreeZeroFiveCorrectOneOneS0OppCube_unsat ⟨2, by omega⟩)
    apply (sat_cnfWithUnits_iff _ _ _).2
    refine ⟨hbase, ?_⟩
    intro i hi
    have hi4 : i < 4 := by
      simpa [muNegThreeZeroFiveCorrectOneOneS0OppUnits] using hi
    interval_cases i <;> simp [satAssignmentOfDimacs,
      muNegThreeZeroFiveCorrectOneOneS0OppUnits, ha, hb, hc, hd]
  · rcases h3 with ⟨ha, hb, hc, hd⟩
    apply false_of_sat_and_unsat
      (hunsat := muNegThreeZeroFiveCorrectOneOneS0OppCube_unsat ⟨3, by omega⟩)
    apply (sat_cnfWithUnits_iff _ _ _).2
    refine ⟨hbase, ?_⟩
    intro i hi
    have hi4 : i < 4 := by
      simpa [muNegThreeZeroFiveCorrectOneOneS0OppUnits] using hi
    interval_cases i <;> simp [satAssignmentOfDimacs,
      muNegThreeZeroFiveCorrectOneOneS0OppUnits, ha, hb, hc, hd]

theorem muNegThreeZeroFiveCorrectOneOneS1_false_of_formula_exactOpp
    (val : DimacsValuation)
    (hnz : ∀ clause ∈
      muNegThreeZeroFiveOwnerDimacsClauses true true true,
      DimacsClauseNonzero clause)
    (hsat : dimacsFormulaSatisfied val
      (muNegThreeZeroFiveOwnerDimacsClauses true true true))
    (hcount : [val 1, val 3, val 5, val 7].count true = 3) : False := by
  have hbase : (muNegThreeZeroFiveOwnerSatCnf true true true).Sat
      (satAssignmentOfDimacs val) := by
    simpa [muNegThreeZeroFiveOwnerSatCnf] using
      satCnf_of_dimacsFormulaSatisfied hnz hsat
  rcases oneone_bool_four_count_three_cases _ _ _ _ hcount with h0 | h1 | h2 | h3
  · rcases h0 with ⟨ha, hb, hc, hd⟩
    apply false_of_sat_and_unsat
      (hunsat := muNegThreeZeroFiveCorrectOneOneS1OppCube_unsat ⟨0, by omega⟩)
    apply (sat_cnfWithUnits_iff _ _ _).2
    refine ⟨hbase, ?_⟩
    intro i hi
    have hi4 : i < 4 := by
      simpa [muNegThreeZeroFiveCorrectOneOneS1OppUnits] using hi
    interval_cases i <;> simp [satAssignmentOfDimacs,
      muNegThreeZeroFiveCorrectOneOneS1OppUnits, ha, hb, hc, hd]
  · rcases h1 with ⟨ha, hb, hc, hd⟩
    apply false_of_sat_and_unsat
      (hunsat := muNegThreeZeroFiveCorrectOneOneS1OppCube_unsat ⟨1, by omega⟩)
    apply (sat_cnfWithUnits_iff _ _ _).2
    refine ⟨hbase, ?_⟩
    intro i hi
    have hi4 : i < 4 := by
      simpa [muNegThreeZeroFiveCorrectOneOneS1OppUnits] using hi
    interval_cases i <;> simp [satAssignmentOfDimacs,
      muNegThreeZeroFiveCorrectOneOneS1OppUnits, ha, hb, hc, hd]
  · rcases h2 with ⟨ha, hb, hc, hd⟩
    apply false_of_sat_and_unsat
      (hunsat := muNegThreeZeroFiveCorrectOneOneS1OppCube_unsat ⟨2, by omega⟩)
    apply (sat_cnfWithUnits_iff _ _ _).2
    refine ⟨hbase, ?_⟩
    intro i hi
    have hi4 : i < 4 := by
      simpa [muNegThreeZeroFiveCorrectOneOneS1OppUnits] using hi
    interval_cases i <;> simp [satAssignmentOfDimacs,
      muNegThreeZeroFiveCorrectOneOneS1OppUnits, ha, hb, hc, hd]
  · rcases h3 with ⟨ha, hb, hc, hd⟩
    apply false_of_sat_and_unsat
      (hunsat := muNegThreeZeroFiveCorrectOneOneS1OppCube_unsat ⟨3, by omega⟩)
    apply (sat_cnfWithUnits_iff _ _ _).2
    refine ⟨hbase, ?_⟩
    intro i hi
    have hi4 : i < 4 := by
      simpa [muNegThreeZeroFiveCorrectOneOneS1OppUnits] using hi
    interval_cases i <;> simp [satAssignmentOfDimacs,
      muNegThreeZeroFiveCorrectOneOneS1OppUnits, ha, hb, hc, hd]

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrectOneOneS0_false_of_formula_exactOpp
#print axioms Erdos85.muNegThreeZeroFiveCorrectOneOneS1_false_of_formula_exactOpp


