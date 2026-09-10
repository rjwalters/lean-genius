import Proofs.Erdos85ThreeHighFarEdgeConflict
import Proofs.Erdos85ThreeHighFarWitness

namespace Erdos85
attribute [local irreducible] threeHighCrossDomain

/-- Low-degree U vertices admit two labels: U edges enforce equality, while
sharing a U neighbor enforces inequality, when the far pair is an edge. -/
theorem threeHighCrossDomain_far_edge_coloring
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (h67 : R 6 7 = true) (h76 : R 7 6 = true) :
    ∃ c : Fin 15 → Fin 2,
      (∀ x y, encodedRowDegree (U x) ≤ 2 → encodedRowDegree (U y) ≤ 2 →
        U x y = true → c x = c y) ∧
      (∀ x y, encodedRowDegree (U x) ≤ 2 → encodedRowDegree (U y) ≤ 2 →
        x ≠ y → (∃ s, U x s = true ∧ U y s = true) → c x ≠ c y) := by
  classical
  have hw : ∀ x, ∃ a : Fin 8, 6 ≤ a.val ∧
      (encodedRowDegree (U x) ≤ 2 → cross x a = true) := by
    intro x
    by_cases hx : encodedRowDegree (U x) ≤ 2
    · obtain ⟨a,ha,hxa⟩ := threeHighCrossDomain_low_degree_far U R cross hc x hx
      exact ⟨a,ha,fun _ => hxa⟩
    · exact ⟨6,by decide,fun h => False.elim (hx h)⟩
  choose f hfar hcross using hw
  let c : Fin 15 → Fin 2 := fun x => ⟨(f x).val - 6,by
    have := (f x).isLt
    have := hfar x
    omega⟩
  have hinj {x y : Fin 15} (he : c x = c y) : f x = f y := by
    apply Fin.ext
    have hv := congrArg Fin.val he
    change (f x).val - 6 = (f y).val - 6 at hv
    have := hfar x
    have := hfar y
    omega
  have hC4 := ((mem_threeHighCrossDomain_iff U R cross).mp hc).1
  refine ⟨c,?_,?_⟩
  · intro x y hx hy hxy
    have he := threeHighEmptyAdj_adjacent_same_far U R cross hC4 h67 h76
      x y (f x) (f y) hxy (hfar x) (hfar y) (hcross x hx) (hcross y hy)
    apply Fin.ext
    change (f x).val - 6 = (f y).val - 6
    rw [he]
  · intro x y hx hy hxy hcommon he
    obtain ⟨s,hxs,hys⟩ := hcommon
    have hf := hinj he
    have hyf : cross y (f x) = true := by rw [hf]; exact hcross y hy
    exact threeHighEmptyAdj_common_U_not_cross U R cross hC4 x y s hxy hxs hys
      (f x) (hcross x hx) hyf

end Erdos85
#print axioms Erdos85.threeHighCrossDomain_far_edge_coloring
