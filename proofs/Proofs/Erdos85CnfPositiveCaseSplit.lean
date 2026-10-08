import Std.Sat.CNF.Basic

/-! A positive-unit case and its negative blocking clause are Boolean
complements. An UNSAT cover plus UNSAT of every listed case suffices without
an additional partition hypothesis. Empty and repeated cases are allowed. -/

namespace Erdos85
open Std Sat

/-- Require every variable in a leaf to be true. -/
def cnfPositiveUnits (variables : List α) : CNF α :=
  ⟨(variables.map fun v => [(v, true)]).toArray⟩

/-- For each leaf, forbid all its positive variables from being true at once. -/
def cnfNegativeCaseCover (cases : List (List α)) : CNF α :=
  ⟨(cases.map fun variables => variables.map fun v => (v, false)).toArray⟩

theorem cnfPositiveUnits_eval (variables : List α) (assignment : α → Bool) :
    (cnfPositiveUnits variables).eval assignment = variables.all assignment := by
  simp [cnfPositiveUnits, CNF.eval, CNF.Clause.eval, List.all_map]

private theorem negativeClause_eval (variables : List α) (assignment : α → Bool) :
    CNF.Clause.eval assignment (variables.map fun v => (v, false)) =
      !variables.all assignment := by
  simp only [CNF.Clause.eval, List.any_map]
  simpa using (List.not_all_eq_any_not (l := variables) (p := assignment)).symm

theorem cnfNegativeCaseCover_eval (cases : List (List α)) (assignment : α → Bool) :
    (cnfNegativeCaseCover cases).eval assignment =
      cases.all (fun variables => !variables.all assignment) := by
  simp [cnfNegativeCaseCover, CNF.eval, List.all_map, negativeClause_eval]

/-- Every valuation satisfies the cover or at least one positive-unit case. -/
theorem cnfPositiveCases_cover_or_case
    (cases : List (List α)) (assignment : α → Bool) :
    (cnfNegativeCaseCover cases).eval assignment = true ∨
      ∃ variables ∈ cases, (cnfPositiveUnits variables).eval assignment = true := by
  by_cases h : cases.any (fun variables => variables.all assignment) = true
  · right
    obtain ⟨variables, hmem, hsat⟩ := List.any_eq_true.mp h
    exact ⟨variables, hmem, by rw [cnfPositiveUnits_eval]; exact hsat⟩
  · left
    have hfalse : cases.any (fun variables => variables.all assignment) = false := by
      simpa using h
    rw [cnfNegativeCaseCover_eval, List.all_eq_true]
    intro variables hmem
    have hnot := List.any_eq_false.mp hfalse variables hmem
    simpa using hnot

/-- Conditional cube-and-conquer: the cover blocks precisely the listed
positive-unit leaves. No independent coverage/partition premise is required. -/
theorem cnf_unsat_of_positive_cases
    (formula : CNF α) (cases : List (List α))
    (hcases : ∀ variables ∈ cases, (formula ++ cnfPositiveUnits variables).Unsat)
    (hcover : (formula ++ cnfNegativeCaseCover cases).Unsat) :
    formula.Unsat := by
  intro assignment
  cases hf : formula.eval assignment with
  | false => rfl
  | true =>
    rcases cnfPositiveCases_cover_or_case cases assignment with hcov | ⟨variables, hv, hs⟩
    · have h := hcover assignment
      simp [CNF.eval_append, hf, hcov] at h
    · have h := hcases variables hv assignment
      simp [CNF.eval_append, hf, hs] at h

end Erdos85

#print axioms Erdos85.cnfPositiveUnits_eval
#print axioms Erdos85.cnfNegativeCaseCover_eval
#print axioms Erdos85.cnfPositiveCases_cover_or_case
#print axioms Erdos85.cnf_unsat_of_positive_cases
