import Proofs.Erdos85OrderSixtyFourTenSixLrat

/-! # Unpadded UNSAT theorems for the `[10,6]` outside-C certificates -/

namespace Erdos85

open Std Sat

theorem cnf_eq_of_clauses_eq {a b : CNF Nat} (h : a.clauses = b.clauses) :
    a = b := congrArg CNF.mk h

theorem cnf_unsat_of_add_bool_tautology_unsat
    (cnf : CNF Nat) (v : Nat)
    (h : (cnf.add [(v, true), (v, false)]).Unsat) : cnf.Unsat := by
  intro val
  have hu := h val
  rw [CNF.eval_add] at hu
  have ht : CNF.Clause.eval val [(v, true), (v, false)] = true := by
    cases hv : val v <;> simp [CNF.Clause.eval, hv]
  rw [ht] at hu
  exact hu

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem tenSixC001Padded_eq_add_tautology :
    tenSixC001PaddedCnf =
      tenSixC001Cnf.add [(915, true), (915, false)] := by
  apply cnf_eq_of_clauses_eq
  native_decide

theorem tenSixC001Cnf_unsat : tenSixC001Cnf.Unsat := by
  apply cnf_unsat_of_add_bool_tautology_unsat tenSixC001Cnf 915
  rw [← tenSixC001Padded_eq_add_tautology]
  exact tenSixC001PaddedCnf_unsat

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem tenSixC002Padded_eq_add_tautology :
    tenSixC002PaddedCnf =
      tenSixC002Cnf.add [(932, true), (932, false)] := by
  apply cnf_eq_of_clauses_eq
  native_decide

theorem tenSixC002Cnf_unsat : tenSixC002Cnf.Unsat := by
  apply cnf_unsat_of_add_bool_tautology_unsat tenSixC002Cnf 932
  rw [← tenSixC002Padded_eq_add_tautology]
  exact tenSixC002PaddedCnf_unsat

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem tenSixC003Padded_eq_add_tautology :
    tenSixC003PaddedCnf =
      tenSixC003Cnf.add [(932, true), (932, false)] := by
  apply cnf_eq_of_clauses_eq
  native_decide

theorem tenSixC003Cnf_unsat : tenSixC003Cnf.Unsat := by
  apply cnf_unsat_of_add_bool_tautology_unsat tenSixC003Cnf 932
  rw [← tenSixC003Padded_eq_add_tautology]
  exact tenSixC003PaddedCnf_unsat

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem tenSixC004Padded_eq_add_tautology :
    tenSixC004PaddedCnf =
      tenSixC004Cnf.add [(913, true), (913, false)] := by
  apply cnf_eq_of_clauses_eq
  native_decide

theorem tenSixC004Cnf_unsat : tenSixC004Cnf.Unsat := by
  apply cnf_unsat_of_add_bool_tautology_unsat tenSixC004Cnf 913
  rw [← tenSixC004Padded_eq_add_tautology]
  exact tenSixC004PaddedCnf_unsat

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem tenSixC005Padded_eq_original :
    tenSixC005PaddedCnf = tenSixC005Cnf := by
  apply cnf_eq_of_clauses_eq
  native_decide

theorem tenSixC005Cnf_unsat : tenSixC005Cnf.Unsat := by
  rw [← tenSixC005Padded_eq_original]
  exact tenSixC005PaddedCnf_unsat

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem tenSixC006Padded_eq_original :
    tenSixC006PaddedCnf = tenSixC006Cnf := by
  apply cnf_eq_of_clauses_eq
  native_decide

theorem tenSixC006Cnf_unsat : tenSixC006Cnf.Unsat := by
  rw [← tenSixC006Padded_eq_original]
  exact tenSixC006PaddedCnf_unsat

end Erdos85
