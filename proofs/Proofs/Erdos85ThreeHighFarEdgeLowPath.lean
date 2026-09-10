import Proofs.Erdos85ThreeHighFarEdgeConflict
import Proofs.Erdos85ThreeHighFarWitness

namespace Erdos85
attribute [local irreducible] threeHighCrossDomain

/-- With the far edge present, a path of low-degree U vertices contradicts
its endpoints sharing the middle U neighbor. -/
theorem threeHighCrossDomain_far_edge_no_low_path
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (h67 : R 6 7 = true) (h76 : R 7 6 = true)
    (x y z : Fin 15) (hxz : x ≠ z)
    (hx : encodedRowDegree (U x) ≤ 2) (hy : encodedRowDegree (U y) ≤ 2)
    (hz : encodedRowDegree (U z) ≤ 2)
    (hxy : U x y = true) (hyz : U y z = true) (hzy : U z y = true) : False := by
  obtain ⟨a,ha,hxa⟩ := threeHighCrossDomain_low_degree_far U R cross hc x hx
  obtain ⟨b,hb,hyb⟩ := threeHighCrossDomain_low_degree_far U R cross hc y hy
  obtain ⟨c,hc6,hzc⟩ := threeHighCrossDomain_low_degree_far U R cross hc z hz
  have hC4 := ((mem_threeHighCrossDomain_iff U R cross).mp hc).1
  have hab := threeHighEmptyAdj_adjacent_same_far U R cross hC4 h67 h76 x y a b hxy ha hb hxa hyb
  have hbc := threeHighEmptyAdj_adjacent_same_far U R cross hC4 h67 h76 y z b c hyz hb hc6 hyb hzc
  have hac := hab.trans hbc
  have hza : cross z a = true := by
    rw [hac]
    exact hzc
  exact threeHighEmptyAdj_common_U_not_cross U R cross hC4 x z y hxz hxy hzy a hxa hza

end Erdos85
#print axioms Erdos85.threeHighCrossDomain_far_edge_no_low_path
