import Proofs.Erdos85DegreeSixColorSectorSplit
import Proofs.Erdos85RamseyPlateau

/-!
# Degree-six boundary package

This file exports the graph-facing degree-six exact-boundary contradiction in
the threshold and plateau-core forms used by the global Erdős--85 assembly.
-/

namespace Erdos85

open SimpleGraph

/-- The order-33 forcing threshold is at most six. -/
theorem minDegreeForC4_thirtyThree_le_six :
    minDegreeForC4 33 ≤ 6 := by
  by_contra hnot
  have hlt : 6 < minDegreeForC4 33 := by omega
  obtain ⟨G, hdec, hmin, hfree⟩ :=
    (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 (by norm_num)).2 hlt
  letI : DecidableRel G.Adj := hdec
  exact hfree (containsC4_of_degreeSix_exact_boundary G hmin (by simp))

/-- A degree-six plateau core cannot occur at its exact second-order
boundary order. -/
theorem not_C4PlateauCore_thirtyThree_six :
    ¬ C4PlateauCore 33 6 := by
  rintro ⟨G, hdec, hmin, hfree, _hcover, _hnext⟩
  letI : DecidableRel G.Adj := hdec
  exact hfree (containsC4_of_degreeSix_exact_boundary G hmin.ge (by simp))

/-- Complete assembly interface for the degree-six exact boundary. -/
theorem degreeSix_secondOrder_boundary_package :
    minDegreeForC4 33 ≤ 6 ∧ ¬ C4PlateauCore 33 6 :=
  ⟨minDegreeForC4_thirtyThree_le_six,
    not_C4PlateauCore_thirtyThree_six⟩

end Erdos85
