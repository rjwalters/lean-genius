import Proofs.Erdos85ThreeHighLowDegreePair
import Proofs.Erdos85ThreeHighFarEdgeConflict

namespace Erdos85
attribute [local irreducible] threeHighCrossDomain

/-- A low adjacent pair is impossible when the two far labels are adjacent. -/
theorem threeHighCrossDomain_far_edge_no_low_adjacent
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (h67 : R 6 7 = true) (h76 : R 7 6 = true)
    (x y : Fin 15) (hx : encodedRowDegree (U x) ≤ 1)
    (hy : encodedRowDegree (U y) ≤ 2) (hxy : U x y = true) : False := by
  obtain ⟨j,hj,hyj⟩ := threeHighCrossDomain_low_degree_far U R cross hc y hy
  have hx6 := threeHighCrossDomain_degree_one_all_far U R cross hc x hx 6 (by decide)
  have hx7 := threeHighCrossDomain_degree_one_all_far U R cross hc x hx 7 (by decide)
  have hC4 := ((mem_threeHighCrossDomain_iff U R cross).mp hc).1
  have h6 := threeHighEmptyAdj_adjacent_same_far U R cross hC4 h67 h76
    x y 6 j hxy (by decide) hj hx6 hyj
  have h7 := threeHighEmptyAdj_adjacent_same_far U R cross hC4 h67 h76
    x y 7 j hxy (by decide) hj hx7 hyj
  have h : (6 : Fin 8) = 7 := h6.trans h7.symm
  exact (by decide : (6 : Fin 8) ≠ 7) h

end Erdos85
#print axioms Erdos85.threeHighCrossDomain_far_edge_no_low_adjacent
