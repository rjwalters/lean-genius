import Proofs.Erdos85MuNegThreeOneTwoOwnerCnfSemantics

/-!
# Nonzero-literal census for the `mu=-3`, `(k,r)=(1,2)` owner CNFs

The checked certificate socket carries the routine DIMACS side condition
that no generated clause contains literal zero.  We discharge it once for
the eight certified orientation/phase formulas and expose a hypothesis-free
semantic contradiction for the graph-facing bridge.

Node: outline F.3, canonical negative switch endpoint `(-3,1,2)`.
-/

namespace Erdos85

open Std Sat

set_option maxHeartbeats 0 in
theorem muNegThreeOneTwoOwnerDimacsClauses_all_ne_zero_c0 :
    ∀ fwd : Bool,
      ((muNegThreeOneTwoOwnerDimacsClauses fwd 0).all fun clause =>
        clause.all fun lit => lit != 0) = true := by
  native_decide

set_option maxHeartbeats 0 in
theorem muNegThreeOneTwoOwnerDimacsClauses_all_ne_zero_c2 :
    ∀ fwd : Bool,
      ((muNegThreeOneTwoOwnerDimacsClauses fwd 2).all fun clause =>
        clause.all fun lit => lit != 0) = true := by
  native_decide

set_option maxHeartbeats 0 in
theorem muNegThreeOneTwoOwnerDimacsClauses_all_ne_zero_c4 :
    ∀ fwd : Bool,
      ((muNegThreeOneTwoOwnerDimacsClauses fwd 4).all fun clause =>
        clause.all fun lit => lit != 0) = true := by
  native_decide

set_option maxHeartbeats 0 in
theorem muNegThreeOneTwoOwnerDimacsClauses_all_ne_zero_c6 :
    ∀ fwd : Bool,
      ((muNegThreeOneTwoOwnerDimacsClauses fwd 6).all fun clause =>
        clause.all fun lit => lit != 0) = true := by
  native_decide

theorem muNegThreeOneTwoOwnerDimacsClauses_all_ne_zero
    (fwd : Bool) (c : Nat) (hc : c = 0 ∨ c = 2 ∨ c = 4 ∨ c = 6) :
    ((muNegThreeOneTwoOwnerDimacsClauses fwd c).all fun clause =>
      clause.all fun lit => lit != 0) = true := by
  rcases hc with rfl | rfl | rfl | rfl
  · exact muNegThreeOneTwoOwnerDimacsClauses_all_ne_zero_c0 fwd
  · exact muNegThreeOneTwoOwnerDimacsClauses_all_ne_zero_c2 fwd
  · exact muNegThreeOneTwoOwnerDimacsClauses_all_ne_zero_c4 fwd
  · exact muNegThreeOneTwoOwnerDimacsClauses_all_ne_zero_c6 fwd

theorem muNegThreeOneTwoOwnerDimacsClauses_nonzero_of_mem
    (fwd : Bool) (c : Nat) (hc : c = 0 ∨ c = 2 ∨ c = 4 ∨ c = 6) :
    ∀ clause ∈ muNegThreeOneTwoOwnerDimacsClauses fwd c,
      DimacsClauseNonzero clause := by
  have hcheck :=
    muNegThreeOneTwoOwnerDimacsClauses_all_ne_zero fwd c hc
  simp only [Array.all_eq_true] at hcheck
  intro clause hclause lit hlit
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hclause
  have hclauseCheck := hcheck i hi
  simp only [List.all_eq_true] at hclauseCheck
  have hlitCheck := hclauseCheck lit hlit
  simpa using hlitCheck

/-- A valuation satisfying the seven semantic families of any certified
`(-3,1,2)` orientation/phase formula is impossible. -/
theorem muNegThreeOneTwoOwnerConstraintSemantics_false'
    {fwd : Bool} {c : Nat} {val : DimacsValuation}
    (hc : c = 0 ∨ c = 2 ∨ c = 4 ∨ c = 6)
    (h : MuNegThreeOneTwoOwnerConstraintSemantics fwd c val) : False :=
  muNegThreeOneTwoOwnerConstraintSemantics_false hc
    (muNegThreeOneTwoOwnerDimacsClauses_nonzero_of_mem fwd c hc) h

end Erdos85

#print axioms Erdos85.muNegThreeOneTwoOwnerConstraintSemantics_false'
