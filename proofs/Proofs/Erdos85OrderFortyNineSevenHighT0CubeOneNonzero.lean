import Proofs.Erdos85OrderFortyNineSevenHighT0CubeCnf

namespace Erdos85

open Std Sat
open Std.Tactic.BVDecide

set_option maxHeartbeats 0 in
theorem sevenHighT0CubeOneFinalState_clauses_nonzero :
    ∀ clause ∈ (sevenHighT0CubeFinalState 1).clauses,
      DimacsClauseNonzero clause := by
  have hall : (sevenHighT0CubeFinalState 1).clauses.toList.all
      (fun clause => clause.all (fun lit => lit != 0)) = true := by native_decide
  intro clause hclause lit hlit
  have hc := (List.all_eq_true.mp hall) clause
    (Array.mem_toList_iff.mpr hclause)
  have hl := (List.all_eq_true.mp hc) lit hlit
  simpa using hl

end Erdos85
