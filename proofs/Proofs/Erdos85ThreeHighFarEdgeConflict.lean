import Proofs.Erdos85ThreeHighFarConflict

namespace Erdos85

/-- A U edge and an R edge cannot be joined by the two cross edges of a C4. -/
theorem threeHighEmptyAdj_U_edge_cross_R_edge
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : encodedC4Free (threeHighEmptyAdj U R cross) = true)
    (x y : Fin 15) (a b : Fin 8)
    (hxy : U x y = true) (hxa : cross x a = true)
    (hyb : cross y b = true) (hba : R b a = true) : False := by
  unfold encodedC4Free at hc
  simp only [decide_eq_true_eq] at hc
  have hne : threeHighEmptyUIndex x ≠ threeHighEmptyRIndex b := by
    intro he
    have hv := congrArg Fin.val he
    change x.val = 15 + b.val at hv
    have := x.isLt
    omega
  have h := hc (threeHighEmptyUIndex x) (threeHighEmptyRIndex b) hne
  have hy : threeHighEmptyUIndex y ∈ Finset.univ.filter (fun q =>
      threeHighEmptyAdj U R cross (threeHighEmptyUIndex x) q &&
      threeHighEmptyAdj U R cross (threeHighEmptyRIndex b) q) := by
    simp [threeHighEmptyAdj,hxy,hyb]
  have ha : threeHighEmptyRIndex a ∈ Finset.univ.filter (fun q =>
      threeHighEmptyAdj U R cross (threeHighEmptyUIndex x) q &&
      threeHighEmptyAdj U R cross (threeHighEmptyRIndex b) q) := by
    simp [threeHighEmptyAdj,hxa,hba]
  have he := Finset.card_le_one.mp h _ hy _ ha
  have hv := congrArg Fin.val he
  change y.val = 15 + a.val at hv
  have := y.isLt
  omega

/-- If the far pair is an edge, adjacent U vertices must use the same far label. -/
theorem threeHighEmptyAdj_adjacent_same_far
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : encodedC4Free (threeHighEmptyAdj U R cross) = true)
    (h67 : R 6 7 = true) (h76 : R 7 6 = true)
    (x y : Fin 15) (a b : Fin 8)
    (hxy : U x y = true) (ha : 6 ≤ a.val) (hb : 6 ≤ b.val)
    (hxa : cross x a = true) (hyb : cross y b = true) : a = b := by
  by_contra hab
  have ac : a = 6 ∨ a = 7 := by
    have := a.isLt
    have h : a.val = 6 ∨ a.val = 7 := by omega
    exact h.imp Fin.ext Fin.ext
  have bc : b = 6 ∨ b = 7 := by
    have := b.isLt
    have h : b.val = 6 ∨ b.val = 7 := by omega
    exact h.imp Fin.ext Fin.ext
  have hba : R b a = true := by
    rcases ac with rfl | rfl <;> rcases bc with rfl | rfl <;> simp_all
  exact threeHighEmptyAdj_U_edge_cross_R_edge U R cross hc x y a b hxy hxa hyb hba

end Erdos85
#print axioms Erdos85.threeHighEmptyAdj_U_edge_cross_R_edge
#print axioms Erdos85.threeHighEmptyAdj_adjacent_same_far
