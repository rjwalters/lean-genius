import Mathlib.Tactic
import Std.Tactic.BVDecide.LRAT

/-!
# Checked exhaustive cube covers

This file turns independently checked cube-and-conquer leaves into an
unsatisfiability theorem for their base CNF.  Two additional checked formulas
certify that a satisfying assignment must select a variable on each side;
the checked positive two-unit cubes then exhaust every possible selection.

The bridge is generic over the variable type and does not trust solver tags,
cube numbering, or external composition metadata.
-/

open Std Sat

namespace Erdos85

def cnfUnitClauses (units : Array (Literal α)) : CNF α where
  clauses := units.map fun lit => [lit]

def cnfWithUnits (base : CNF α) (units : Array (Literal α)) : CNF α :=
  base ++ cnfUnitClauses units

@[simp] theorem eval_cnfUnitClauses
    (units : Array (Literal α)) (assignment : α → Bool) :
    CNF.eval assignment (cnfUnitClauses units) =
      units.all fun lit => assignment lit.1 == lit.2 := by
  simp [CNF.eval, cnfUnitClauses, CNF.Clause.eval]

theorem sat_cnfWithUnits_iff (base : CNF α) (units : Array (Literal α))
    (assignment : α → Bool) :
    (cnfWithUnits base units).Sat assignment ↔
      base.Sat assignment ∧
        (∀ i, (hi : i < units.size) →
          (assignment units[i].1 == units[i].2) = true) := by
  rw [CNF.sat_def, cnfWithUnits, CNF.eval_append,
    eval_cnfUnitClauses]
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨hbase, hunits⟩
    refine ⟨hbase, ?_⟩
    simpa only [Array.all_eq_true] using hunits
  · rintro ⟨hbase, hunits⟩
    refine ⟨hbase, ?_⟩
    simpa only [Array.all_eq_true] using hunits

def negativeUnits (vars : Array α) : Array (Literal α) :=
  vars.map fun v => (v, false)

theorem exists_true_of_negativeUnits_unsat
    (base : CNF α) (vars : Array α)
    (hcover : (cnfWithUnits base (negativeUnits vars)).Unsat)
    {assignment : α → Bool} (hbase : base.Sat assignment) :
    ∃ v ∈ vars, assignment v = true := by
  by_contra hnone
  have hallFalse : ∀ v ∈ vars, assignment v = false := by
    intro v hv
    apply Bool.eq_false_of_not_eq_true
    intro hvTrue
    exact hnone ⟨v, hv, hvTrue⟩
  have hsat : (cnfWithUnits base (negativeUnits vars)).Sat assignment := by
    apply (sat_cnfWithUnits_iff base (negativeUnits vars) assignment).2
    refine ⟨hbase, ?_⟩
    intro i hi
    simp only [negativeUnits, Array.size_map] at hi
    simp [negativeUnits, hallFalse vars[i] (Array.getElem_mem hi)]
  rw [CNF.unsat_def] at hcover
  have := hcover assignment
  rw [CNF.sat_def] at hsat
  rw [hsat] at this
  contradiction

def positiveTwoCube (left right : α) : Array (Literal α) :=
  #[(left, true), (right, true)]

theorem cnf_unsat_of_exhaustive_twoCubes
    (base : CNF α) (left right : Array α)
    (hleft : (cnfWithUnits base (negativeUnits left)).Unsat)
    (hright : (cnfWithUnits base (negativeUnits right)).Unsat)
    (hcubes : ∀ l ∈ left, ∀ r ∈ right,
      (cnfWithUnits base (positiveTwoCube l r)).Unsat) :
    base.Unsat := by
  rw [CNF.unsat_def]
  intro assignment
  by_contra hnotFalse
  have hbaseEval : CNF.eval assignment base = true :=
    Bool.eq_true_of_not_eq_false hnotFalse
  have hbase : base.Sat assignment := hbaseEval
  obtain ⟨l, hl, hlTrue⟩ :=
    exists_true_of_negativeUnits_unsat base left hleft hbase
  obtain ⟨r, hr, hrTrue⟩ :=
    exists_true_of_negativeUnits_unsat base right hright hbase
  have hcubeSat :
      (cnfWithUnits base (positiveTwoCube l r)).Sat assignment := by
    apply (sat_cnfWithUnits_iff base (positiveTwoCube l r) assignment).2
    refine ⟨hbase, ?_⟩
    intro i hi
    have hi2 : i < 2 := by simpa [positiveTwoCube] using hi
    have hiCases : i = 0 ∨ i = 1 := by omega
    rcases hiCases with rfl | rfl <;>
      simp [positiveTwoCube, hlTrue, hrTrue]
  have hcubeUnsat := hcubes l hl r hr
  rw [CNF.unsat_def] at hcubeUnsat
  have hcubeFalse := hcubeUnsat assignment
  rw [CNF.sat_def] at hcubeSat
  rw [hcubeSat] at hcubeFalse
  contradiction

end Erdos85
