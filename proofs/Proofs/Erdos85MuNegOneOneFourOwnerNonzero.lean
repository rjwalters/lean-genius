import Proofs.Erdos85MuNegOneOneFourOwnerCnfSemantics

/-!
# Nonzero-literal census and hypothesis-free socket for the μ=-1 `(1,4)` CNFs

Node: outline F.3 (μ=-1 lane; graph→valuation bridge, increment 2 of
the plan in squad msgs 13943/13945).

`muNegOneOneFourOwnerConstraintSemantics_false` carries the DIMACS
sanity obligation `hnz` (no clause mentions literal `0`).  As in the
banked six-ten chain this is a size census over the generated clause
stream, discharged once by `native_decide` (named-axiom rule: the
census theorem below depends on `Lean.ofReduceBool`) and packaged so
that the graph-facing embedding layers never see the obligation.
-/

namespace Erdos85

open Std Sat

set_option maxHeartbeats 0 in
theorem muNegOneOneFourOwnerDimacsClauses_all_ne_zero_TFTF :
    ∀ σ : Bool,
      ((muNegOneOneFourOwnerDimacsClauses false false σ).all fun clause =>
        clause.all fun lit => lit != 0) = true := by
  native_decide

set_option maxHeartbeats 0 in
theorem muNegOneOneFourOwnerDimacsClauses_all_ne_zero_TFtri :
    ∀ σ : Bool,
      ((muNegOneOneFourOwnerDimacsClauses false true σ).all fun clause =>
        clause.all fun lit => lit != 0) = true := by
  native_decide

set_option maxHeartbeats 0 in
theorem muNegOneOneFourOwnerDimacsClauses_all_ne_zero_tritri :
    ∀ σ : Bool,
      ((muNegOneOneFourOwnerDimacsClauses true true σ).all fun clause =>
        clause.all fun lit => lit != 0) = true := by
  native_decide

theorem muNegOneOneFourOwnerDimacsClauses_all_ne_zero
    (uTri vTri σ : Bool)
    (hcanon : (uTri = false ∧ vTri = false) ∨
      (uTri = false ∧ vTri = true) ∨ (uTri = true ∧ vTri = true)) :
    ((muNegOneOneFourOwnerDimacsClauses uTri vTri σ).all fun clause =>
      clause.all fun lit => lit != 0) = true := by
  rcases hcanon with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact muNegOneOneFourOwnerDimacsClauses_all_ne_zero_TFTF σ
  · exact muNegOneOneFourOwnerDimacsClauses_all_ne_zero_TFtri σ
  · exact muNegOneOneFourOwnerDimacsClauses_all_ne_zero_tritri σ

theorem muNegOneOneFourOwnerDimacsClauses_nonzero_of_mem
    (uTri vTri σ : Bool)
    (hcanon : (uTri = false ∧ vTri = false) ∨
      (uTri = false ∧ vTri = true) ∨ (uTri = true ∧ vTri = true)) :
    ∀ clause ∈ muNegOneOneFourOwnerDimacsClauses uTri vTri σ,
      DimacsClauseNonzero clause := by
  have hcheck :=
    muNegOneOneFourOwnerDimacsClauses_all_ne_zero uTri vTri σ hcanon
  simp only [Array.all_eq_true] at hcheck
  intro clause hclause lit hlit
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hclause
  have hclauseCheck := hcheck i hi
  simp only [List.all_eq_true] at hclauseCheck
  have hlitCheck := hclauseCheck lit hlit
  simpa using hlitCheck

/-- Hypothesis-free contradiction socket: a valuation satisfying the
six clause families of any canonical `(−1,1,4)` sector pair is
impossible. -/
theorem muNegOneOneFourOwnerConstraintSemantics_false'
    {uTri vTri σ : Bool} {val : DimacsValuation}
    (hcanon : (uTri = false ∧ vTri = false) ∨
      (uTri = false ∧ vTri = true) ∨ (uTri = true ∧ vTri = true))
    (h : MuNegOneOneFourOwnerConstraintSemantics uTri vTri σ val) :
    False :=
  muNegOneOneFourOwnerConstraintSemantics_false hcanon
    (muNegOneOneFourOwnerDimacsClauses_nonzero_of_mem uTri vTri σ hcanon) h

end Erdos85

#print axioms Erdos85.muNegOneOneFourOwnerConstraintSemantics_false'
