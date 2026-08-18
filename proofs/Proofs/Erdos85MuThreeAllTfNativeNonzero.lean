import Proofs.Erdos85MuThreeAllTfNativeCnf

/-! # Nonzero-literal audit for the native `mu = 3` CNFs

This finite audit is deliberately isolated from the structural semantic
bridge.  It runs once over the three certificate CNFs and proves that their
one-based DIMACS literals never contain zero, which is the sole side
condition of the DIMACS-to-`Std.Sat.CNF` conversion.
-/

namespace Erdos85

def mu3AllTfNativeShapes : List Mu3AllTfShape :=
  [.c16, .c10c6, .c8c8]

def mu3NativeFinalStatesNonzeroCheck : Bool :=
  mu3AllTfNativeShapes.all fun shape =>
    (mu3NativeFinalState shape).clauses.all fun clause =>
      clause.all fun lit => lit != 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem mu3NativeFinalStatesNonzeroCheck_eq_true :
    mu3NativeFinalStatesNonzeroCheck = true := by
  native_decide

theorem mu3NativeFinalState_clauses_nonzero (shape : Mu3AllTfShape) :
    ∀ clause ∈ (mu3NativeFinalState shape).clauses,
      DimacsClauseNonzero clause := by
  have hshape : shape ∈ mu3AllTfNativeShapes := by
    cases shape <;> simp [mu3AllTfNativeShapes]
  have hcheck := mu3NativeFinalStatesNonzeroCheck_eq_true
  simp only [mu3NativeFinalStatesNonzeroCheck, List.all_eq_true] at hcheck
  have hs := hcheck shape hshape
  simp only [Array.all_eq_true] at hs
  intro clause hclause lit hlit
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hclause
  have hc := hs i hi
  simp only [List.all_eq_true] at hc
  simpa using hc lit hlit

end Erdos85
