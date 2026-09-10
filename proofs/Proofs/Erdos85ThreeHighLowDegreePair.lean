import Proofs.Erdos85ThreeHighFarWitness
import Proofs.Erdos85ThreeHighFarConflict

namespace Erdos85

/-- A large root-admissible row contains every far label. -/
theorem threeHighRootRowGate_all_far (S : Finset (Fin 8))
    (hS : threeHighRootRowGate S = true) (hs : 3 ≤ S.card)
    (j : Fin 8) (hj : 6 ≤ j.val) : j ∈ S := by
  by_contra hn
  obtain ⟨a,ha,ha6⟩ := threeHighRootRowGate_far_witness S hS (by omega)
  have haj : a.val ≠ j.val := fun h => hn (Fin.ext h ▸ ha)
  have hsub : S ⊆ (S.filter fun x => x.val < 6) ∪ {a} := by
    intro x hx
    by_cases hx6 : x.val < 6
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx,hx6⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_singleton.mpr
      apply Fin.ext
      have hxj : x.val ≠ j.val := fun h => hn (Fin.ext h ▸ hx)
      have ha8 := a.isLt
      have hj8 := j.isLt
      have hx8 := x.isLt
      omega
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le (S.filter fun x => x.val < 6) {a}
  unfold threeHighRootRowGate at hS
  simp only [decide_eq_true_eq] at hS
  simp only [Finset.card_singleton] at hu
  omega

attribute [local irreducible] threeHighCrossDomain

theorem threeHighCrossDomain_degree_one_all_far
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (x : Fin 15) (hx : encodedRowDegree (U x) ≤ 1)
    (j : Fin 8) (hj : 6 ≤ j.val) : cross x j = true := by
  have hC4 := ((mem_threeHighCrossDomain_iff U R cross).mp hc).1
  have hr := threeHighRootRowGate_of_c4 U R cross hC4 x
  have hm := (threeHighCrossDomain_margins U R cross hc).1 x
  have hs : 3 ≤ (threeHighCrossRows cross x).card := by
    change 3 ≤ encodedRowDegree (cross x)
    omega
  have h := threeHighRootRowGate_all_far _ hr hs j hj
  simpa [threeHighCrossRows] using h

/-- A degree-at-most-one and a degree-at-most-two U vertex cannot share a U neighbor. -/
theorem threeHighCrossDomain_no_low_degree_pair
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (x y s : Fin 15) (hxy : x ≠ y)
    (hx : encodedRowDegree (U x) ≤ 1) (hy : encodedRowDegree (U y) ≤ 2)
    (hxs : U x s = true) (hys : U y s = true) : False := by
  obtain ⟨j,hj,hyj⟩ := threeHighCrossDomain_low_degree_far U R cross hc y hy
  have hxj := threeHighCrossDomain_degree_one_all_far U R cross hc x hx j hj
  exact threeHighEmptyAdj_common_U_not_cross U R cross
    ((mem_threeHighCrossDomain_iff U R cross).mp hc).1 x y s hxy hxs hys j hxj hyj

end Erdos85
#print axioms Erdos85.threeHighRootRowGate_all_far
#print axioms Erdos85.threeHighCrossDomain_degree_one_all_far
#print axioms Erdos85.threeHighCrossDomain_no_low_degree_pair
