import Proofs.Erdos85CnfCubeCover

/-! # A checked binary split for CNF certificates -/

open Std Sat

namespace Erdos85

/-- Append the unit clause fixing `variable` to `value`. -/
def cnfWithSignedUnit (base : CNF α) (v : α) (value : Bool) : CNF α :=
  cnfWithUnits base #[(v, value)]

/-- Unsatisfiability of both Boolean branches proves the base CNF unsatisfiable.

This is the proof-producing socket for ordinary binary DPLL trees: certificate
generators may recursively use it at every internal node, while LRAT replay is
needed only at the leaves. -/
theorem cnf_unsat_of_binaryUnitSplit
    (base : CNF α) (v : α)
    (hfalse : (cnfWithSignedUnit base v false).Unsat)
    (htrue : (cnfWithSignedUnit base v true).Unsat) :
    base.Unsat := by
  rw [CNF.unsat_def]
  intro assignment
  by_contra hnotFalse
  have hbaseEval : CNF.eval assignment base = true :=
    Bool.eq_true_of_not_eq_false hnotFalse
  have hbase : base.Sat assignment := hbaseEval
  cases hvalue : assignment v with
  | false =>
      have hbranch :
          (cnfWithSignedUnit base v false).Sat assignment := by
        apply (sat_cnfWithUnits_iff base #[(v, false)] assignment).2
        refine ⟨hbase, ?_⟩
        intro i hi
        have hiOne : i < 1 := by simpa using hi
        have hiZero : i = 0 := by omega
        subst i
        simp [hvalue]
      rw [CNF.unsat_def] at hfalse
      have := hfalse assignment
      rw [CNF.sat_def] at hbranch
      rw [hbranch] at this
      contradiction
  | true =>
      have hbranch :
          (cnfWithSignedUnit base v true).Sat assignment := by
        apply (sat_cnfWithUnits_iff base #[(v, true)] assignment).2
        refine ⟨hbase, ?_⟩
        intro i hi
        have hiOne : i < 1 := by simpa using hi
        have hiZero : i = 0 := by omega
        subst i
        simp [hvalue]
      rw [CNF.unsat_def] at htrue
      have := htrue assignment
      rw [CNF.sat_def] at hbranch
      rw [hbranch] at this
      contradiction

/-- A proof-grade binary cube-and-conquer tree.  Internal nodes record the
actual CNF variable being split; leaves carry checked unsatisfiability proofs
for the CNF accumulated along their path. -/
inductive CnfBinaryCheckedTree : CNF α → Prop where
  | leaf {base : CNF α} (checked : base.Unsat) : CnfBinaryCheckedTree base
  | split {base : CNF α} (v : α)
      (falseBranch : CnfBinaryCheckedTree (cnfWithSignedUnit base v false))
      (trueBranch : CnfBinaryCheckedTree (cnfWithSignedUnit base v true)) :
      CnfBinaryCheckedTree base

/-- Soundness of a recursively checked binary tree. -/
theorem CnfBinaryCheckedTree.unsat {base : CNF α}
    (tree : CnfBinaryCheckedTree base) : base.Unsat := by
  induction tree with
  | leaf checked => exact checked
  | split v falseBranch trueBranch hfalse htrue =>
      exact cnf_unsat_of_binaryUnitSplit _ v hfalse htrue

end Erdos85

#print axioms Erdos85.cnf_unsat_of_binaryUnitSplit
#print axioms Erdos85.CnfBinaryCheckedTree.unsat
