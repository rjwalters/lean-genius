import Proofs.Erdos85ThreeHighLowDegreeTriangle

namespace Erdos85

/-- Test ordered triples only among U vertices of degree at most two. -/
def threeHighLowDegreeTriangleGate (U : Fin 15 → Fin 15 → Bool) : Bool :=
  let low := (List.finRange 15).filter (fun x => decide (encodedRowDegree (U x) ≤ 2))
  low.all fun x => low.all fun y => low.all fun z => decide (¬
    (x < y ∧ y < z ∧
      (∃ s, U x s = true ∧ U y s = true) ∧
      (∃ s, U x s = true ∧ U z s = true) ∧
      (∃ s, U y s = true ∧ U z s = true)))

attribute [local irreducible] threeHighCrossDomain

theorem threeHighLowDegreeTriangleGate_of_cross
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R) :
    threeHighLowDegreeTriangleGate U = true := by
  apply List.all_eq_true.mpr
  intro x hx
  apply List.all_eq_true.mpr
  intro y hy
  apply List.all_eq_true.mpr
  intro z hz
  apply decide_eq_true_iff.mpr
  rintro ⟨hxy,hyz,hXY,hXZ,hYZ⟩
  exact threeHighCrossDomain_no_low_degree_triangle U R cross hc x y z
    (ne_of_lt hxy) (ne_of_lt (lt_trans hxy hyz)) (ne_of_lt hyz)
    (of_decide_eq_true (List.mem_filter.mp hx).2)
    (of_decide_eq_true (List.mem_filter.mp hy).2)
    (of_decide_eq_true (List.mem_filter.mp hz).2) hXY hXZ hYZ

end Erdos85
#print axioms Erdos85.threeHighLowDegreeTriangleGate_of_cross
