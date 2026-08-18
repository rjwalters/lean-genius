import Proofs.Erdos85OrderSixtyFourTenSixOutsideC4Satisfaction

/-! # Satisfaction and contradiction for generated `[10,6]` outside CNFs -/

namespace Erdos85

open Std Sat

/-- The graph-induced valuation satisfies the complete generated formula. -/
theorem tenSixOutsideGeneratedCnf_sat
    (i : Fin 6) (C : SimpleGraph (Fin 48)) [DecidableRel C.Adj]
    (hs : OutsideCClauseSemantics C
      (fun u e ↦ tenSixIncidence i u e = true) (tenSixOutsideTarget i)) :
    (tenSixOutsideGeneratedCnf i).Sat
      (tenSixOutsideDimacsValuation i C) := by
  rw [CNF.sat_def, CNF.eval, Array.all_eq_true]
  intro j hj
  have hmemArray := Array.getElem_mem
    (xs := (tenSixOutsideGeneratedCnf i).clauses) hj
  have hmemList :
      (tenSixOutsideGeneratedCnf i).clauses[j] ∈
        tenSixOutsideServiceClauses i ++ tenSixOutsideC4Clauses i := by
    simpa only [tenSixOutsideGeneratedCnf, List.mem_toArray] using hmemArray
  have hcases := List.mem_append.mp hmemList
  rcases hcases with hservice | hc4
  · exact tenSixOutside_serviceClause_eval i C hs hservice
  · exact tenSixOutsideC4Clause_eval i C hs hc4

end Erdos85
