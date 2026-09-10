import Proofs.Erdos85ThreeHighRootRowPruning

namespace Erdos85

/-- Two rows of size at least three, each using at most one near vertex,
share at least two vertices because there are only two far vertices. -/
theorem threeHighRootRowGate_large_inter (S T : Finset (Fin 8))
    (hS : threeHighRootRowGate S = true) (hT : threeHighRootRowGate T = true)
    (hs : 3 ≤ S.card) (ht : 3 ≤ T.card) : 2 ≤ (S ∩ T).card := by
  unfold threeHighRootRowGate at hS hT
  simp only [decide_eq_true_eq] at hS hT
  have hsub : S ∪ T ⊆ ((S.filter fun j => j.val < 6) ∪
      (T.filter fun j => j.val < 6)) ∪ {6,7} := by
    intro j hj
    by_cases hn : j.val < 6
    · apply Finset.mem_union_left
      rcases Finset.mem_union.mp hj with hj | hj
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hj,hn⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hj,hn⟩)
    · apply Finset.mem_union_right
      have hj8 := j.isLt
      have he : j = 6 ∨ j = 7 := by
        have hv : j.val = 6 ∨ j.val = 7 := by omega
        exact hv.imp Fin.ext Fin.ext
      simpa using he
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le (S.filter fun j => j.val < 6)
    (T.filter fun j => j.val < 6)
  have hv := Finset.card_union_le
    ((S.filter fun j => j.val < 6) ∪ (T.filter fun j => j.val < 6)) ({6,7} : Finset (Fin 8))
  have hf : ({6,7} : Finset (Fin 8)).card = 2 := by decide
  have hi := Finset.card_union_add_card_inter S T
  omega

theorem threeHighCrossRows_inter_le_one
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hC4 : encodedC4Free (threeHighEmptyAdj U R cross) = true)
    (i j : Fin 15) (hij : i ≠ j) :
    (threeHighCrossRows cross i ∩ threeHighCrossRows cross j).card ≤ 1 := by
  unfold encodedC4Free at hC4
  simp only [decide_eq_true_eq] at hC4
  have hne : threeHighEmptyUIndex i ≠ threeHighEmptyUIndex j := by
    intro he
    apply hij
    apply Fin.ext
    have hv := congrArg Fin.val he
    simpa [threeHighEmptyUIndex] using hv
  have hc := hC4 _ _ hne
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have hmem (x : Fin 8)
      (hx : x ∈ threeHighCrossRows cross i ∩ threeHighCrossRows cross j) :
      threeHighEmptyRIndex x ∈ Finset.univ.filter (fun y =>
        threeHighEmptyAdj U R cross (threeHighEmptyUIndex i) y &&
        threeHighEmptyAdj U R cross (threeHighEmptyUIndex j) y) := by
    have hxi : cross i x = true := by simpa [threeHighCrossRows] using (Finset.mem_inter.mp hx).1
    have hxj : cross j x = true := by simpa [threeHighCrossRows] using (Finset.mem_inter.mp hx).2
    simp [threeHighEmptyAdj,hxi,hxj]
  have he := Finset.card_le_one.mp hc _ (hmem a ha) _ (hmem b hb)
  apply Fin.ext
  have hv := congrArg Fin.val he
  simpa [threeHighEmptyRIndex] using hv

theorem threeHighCrossRows_large_unique
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hC4 : encodedC4Free (threeHighEmptyAdj U R cross) = true) :
    (Finset.univ.filter fun i => 3 ≤ (threeHighCrossRows cross i).card).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hij
  have h := threeHighRootRowGate_large_inter _ _
    (threeHighRootRowGate_of_c4 U R cross hC4 i)
    (threeHighRootRowGate_of_c4 U R cross hC4 j)
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have hc := threeHighCrossRows_inter_le_one U R cross hC4 i j hij
  omega

attribute [local irreducible] threeHighCrossDomain

/-- At most one U vertex can require three or more cross neighbors. -/
theorem threeHighCrossDomain_low_union_degree_unique
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R) :
    (Finset.univ.filter fun i => encodedRowDegree (U i) ≤ 1).card ≤ 1 := by
  have h := threeHighCrossRows_large_unique U R cross
    ((mem_threeHighCrossDomain_iff U R cross).mp hc).1
  apply le_trans (Finset.card_le_card ?_) h
  intro i hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hd := (threeHighCrossDomain_margins U R cross hc).1 i
  have hl := (Finset.mem_filter.mp hi).2
  change 3 ≤ encodedRowDegree (cross i)
  omega

end Erdos85
#print axioms Erdos85.threeHighRootRowGate_large_inter
#print axioms Erdos85.threeHighCrossRows_inter_le_one
#print axioms Erdos85.threeHighCrossRows_large_unique
#print axioms Erdos85.threeHighCrossDomain_low_union_degree_unique
