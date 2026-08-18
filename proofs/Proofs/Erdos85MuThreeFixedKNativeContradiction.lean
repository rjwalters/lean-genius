import Proofs.Erdos85MuThreeFixedKNativeCnfEquality

/-!
# Certificate-facing contradiction for the nineteen fixed-K grids

This module removes the remaining encoding bookkeeping from the graph-facing
interface.  A caller supplies only the exact row/column hit counts and the
static common-neighbour bound for its base-edge valuation.
-/

namespace Erdos85

open Std Sat

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- The fixed hit rows use only nonzero base literals in the allocated base-ID
range. -/
theorem mu3FixedKGrid_hit_ids_valid (i : Fin 22) :
    (∀ spec ∈ mu3GridHitSpecs (mu3FixedKGrid i),
      ∀ lit ∈ spec.1, lit ≠ 0) ∧
    (∀ spec ∈ mu3GridHitSpecs (mu3FixedKGrid i),
      ∀ lit ∈ spec.1, lit.natAbs ≤ 1128) := by
  have hcheck : (mu3GridHitSpecs (mu3FixedKGrid i)).all fun spec =>
      spec.1.all fun lit => decide (lit ≠ 0 ∧ lit.natAbs ≤ 1128) := by
    fin_cases i <;> native_decide
  simp only [List.all_eq_true] at hcheck
  constructor
  · intro spec hspec lit hlit
    have hsarr := hcheck spec hspec
    simp only [Array.all_eq_true] at hsarr
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hlit
    have hs := hsarr j hj
    have hp : spec.1[j] ≠ 0 ∧ spec.1[j].natAbs ≤ 1128 := by
      simpa only [decide_eq_true_eq] using hs
    exact hp.1
  · intro spec hspec lit hlit
    have hsarr := hcheck spec hspec
    simp only [Array.all_eq_true] at hsarr
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hlit
    have hs := hsarr j hj
    have hp : spec.1[j] ≠ 0 ∧ spec.1[j].natAbs ≤ 1128 := by
      simpa only [decide_eq_true_eq] using hs
    exact hp.2

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- Every clause emitted for a concrete fixed grid contains only nonzero
DIMACS literals, as required by the DIMACS-to-`Std.Sat` bridge. -/
theorem mu3FixedKGrid_clauses_nonzero (i : Fin 22) :
    ∀ clause ∈ (mu3GridFinalState (mu3FixedKGrid i)).clauses,
      DimacsClauseNonzero clause := by
  have hcheck : (mu3GridFinalState (mu3FixedKGrid i)).clauses.toList.all
      (fun clause => clause.all (fun lit => lit != 0)) = true := by
    fin_cases i <;> native_decide
  intro clause hclause lit hlit
  have hc : clause.all (fun entry => entry != 0) = true :=
    (List.all_eq_true.mp hcheck) clause
      (Array.mem_toList_iff.mpr hclause)
  have hl := (List.all_eq_true.mp hc) lit hlit
  simpa using hl

/-- Graph-facing fixed-K contradiction endpoint.  The two hypotheses are
exactly the Boolean consequences supplied by a C4-free exterior graph with
the prescribed row and column hit laws. -/
theorem false_of_mu3FixedKNativeStaticConstraints
    (i : Fin 22) (edgeVal : DimacsValuation)
    (hhitCounts : ∀ spec ∈ mu3GridHitSpecs (mu3FixedKGrid i),
      seqPrefixTrue (mu3NativeVarsRow edgeVal spec.1) spec.1.size = spec.2)
    (hbaseC4 : Mu3NativeBaseC4 edgeVal) : False := by
  obtain ⟨hhitNonzero, hhitBound⟩ := mu3FixedKGrid_hit_ids_valid i
  obtain ⟨val, hformula⟩ := mu3GridFinalSpecState_formulaSatisfiable
    (mu3FixedKGrid i) edgeVal hhitNonzero hhitBound hhitCounts hbaseC4
  rw [mu3FixedKGrid_spec_eq_generator i] at hformula
  have hsat : (mu3GridNativeSatCnf (mu3FixedKGrid i)).Sat
      (satAssignmentOfDimacs val) :=
    satCnf_of_dimacsFormulaSatisfied hformula
      (mu3FixedKGrid_clauses_nonzero i)
  have hfalse := mu3FixedKNativeCnf_unsat i (satAssignmentOfDimacs val)
  rw [CNF.sat_def] at hsat
  rw [hsat] at hfalse
  contradiction

end Erdos85

#print axioms Erdos85.mu3FixedKGrid_hit_ids_valid
#print axioms Erdos85.mu3FixedKGrid_clauses_nonzero
#print axioms Erdos85.false_of_mu3FixedKNativeStaticConstraints
