import Proofs.Erdos85ThreeHighFarWitness
import Proofs.Erdos85ThreeHighFarConflict

namespace Erdos85

attribute [local irreducible] threeHighCrossDomain

/-- Three low-U-degree vertices cannot pairwise share U neighbors: they would
require three distinct far labels, but only labels6 and7 are available. -/
theorem threeHighCrossDomain_no_low_degree_triangle
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain UAdj RAdj)
    (x y z : Fin 15) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : encodedRowDegree (UAdj x) ≤ 2) (hy : encodedRowDegree (UAdj y) ≤ 2)
    (hz : encodedRowDegree (UAdj z) ≤ 2)
    (hXY : ∃ s, UAdj x s = true ∧ UAdj y s = true)
    (hXZ : ∃ s, UAdj x s = true ∧ UAdj z s = true)
    (hYZ : ∃ s, UAdj y s = true ∧ UAdj z s = true) : False := by
  obtain ⟨a,ha,hxa⟩ := threeHighCrossDomain_low_degree_far UAdj RAdj cross hc x hx
  obtain ⟨b,hb,hyb⟩ := threeHighCrossDomain_low_degree_far UAdj RAdj cross hc y hy
  obtain ⟨c,hc',hzc⟩ := threeHighCrossDomain_low_degree_far UAdj RAdj cross hc z hz
  have hC4 := ((mem_threeHighCrossDomain_iff UAdj RAdj cross).mp hc).1
  have different (i j : Fin 15) (hij : i ≠ j)
      (hcommon : ∃ s, UAdj i s = true ∧ UAdj j s = true)
      (u v : Fin 8) (hiu : cross i u = true) (hjv : cross j v = true) : u ≠ v := by
    intro he
    subst v
    obtain ⟨s,his,hjs⟩ := hcommon
    exact threeHighEmptyAdj_common_U_not_cross UAdj RAdj cross hC4 i j s hij his hjs u hiu hjv
  have hab := different x y hxy hXY a b hxa hyb
  have hac := different x z hxz hXZ a c hxa hzc
  have hbc := different y z hyz hYZ b c hyb hzc
  have habv : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hacv : a.val ≠ c.val := fun h => hac (Fin.ext h)
  have hbcv : b.val ≠ c.val := fun h => hbc (Fin.ext h)
  have ha8 := a.isLt
  have hb8 := b.isLt
  have hc8 := c.isLt
  omega

end Erdos85
#print axioms Erdos85.threeHighCrossDomain_no_low_degree_triangle
