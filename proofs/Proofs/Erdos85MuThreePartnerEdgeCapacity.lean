import Proofs.Erdos85MuThreeAllTrianglePartnerGraph

/-!
# Capacity between two partner edges

For two vertex-disjoint edges of the partner graph `C ∩ Rowcol`, at most one
of the four possible exterior edges can run between their endpoint pairs.
Two edges sharing an endpoint violate the rook law; two disjoint cross edges
form a four-cycle together with the two partner edges.
-/

open SimpleGraph

namespace Erdos85

/-- Candidate exterior edges between two unordered vertex pairs. -/
def mixedGridPartnerCrossEdges
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {K : X → Y → Prop} [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (a b c d : muThreeMixedCell K) :
    Finset (muThreeMixedCell K × muThreeMixedCell K) :=
  (({a, b} : Finset (muThreeMixedCell K)) ×ˢ
    ({c, d} : Finset (muThreeMixedCell K))).filter fun p => C.Adj p.1 p.2

/-- **Partner-edge capacity one.**  Between two disjoint partner edges there
is at most one exterior edge. -/
theorem MuThreeMixedGridCode.partnerCrossEdges_card_le_one
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {a b c d : muThreeMixedCell K}
    (hab : (mixedGridPartnerGraph K C).Adj a b)
    (hcd : (mixedGridPartnerGraph K C).Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (mixedGridPartnerCrossEdges C a b c d).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  rintro ⟨x, y⟩ hp ⟨x', y'⟩ hq
  have hp' := Finset.mem_filter.mp hp
  have hq' := Finset.mem_filter.mp hq
  have hx : x = a ∨ x = b := by simpa using (Finset.mem_product.mp hp'.1).1
  have hy : y = c ∨ y = d := by simpa using (Finset.mem_product.mp hp'.1).2
  have hx' : x' = a ∨ x' = b := by simpa using (Finset.mem_product.mp hq'.1).1
  have hy' : y' = c ∨ y' = d := by simpa using (Finset.mem_product.mp hq'.1).2
  have hxy : C.Adj x y := hp'.2
  have hx'y' : C.Adj x' y' := hq'.2
  by_cases hxx' : x = x'
  · subst x'
    by_cases hyy' : y = y'
    · subst y'
      rfl
    · have hPartner : (mixedGridRowColumnGraph K).Adj y y' := by
        rcases hy with rfl | rfl <;> rcases hy' with rfl | rfl
        · exact (hyy' rfl).elim
        · exact hcd.2
        · exact (mixedGridRowColumnGraph K).adj_symm hcd.2
        · exact (hyy' rfl).elim
      have hsep := code.rook x y y' hxy hx'y' hyy'
      exact (hPartner.2.elim hsep.1 hsep.2).elim
  · by_cases hyy' : y = y'
    · subst y'
      have hPartner : (mixedGridRowColumnGraph K).Adj x x' := by
        rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl
        · exact (hxx' rfl).elim
        · exact hab.2
        · exact (mixedGridRowColumnGraph K).adj_symm hab.2
        · exact (hxx' rfl).elim
      have hsep := code.rook y x x' hxy.symm hx'y'.symm hxx'
      exact (hPartner.2.elim hsep.1 hsep.2).elim
    · have hLeft : (mixedGridPartnerGraph K C).Adj x x' := by
        rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl
        · exact (hxx' rfl).elim
        · exact hab
        · exact (mixedGridPartnerGraph K C).adj_symm hab
        · exact (hxx' rfl).elim
      have hRight : (mixedGridPartnerGraph K C).Adj y y' := by
        rcases hy with rfl | rfl <;> rcases hy' with rfl | rfl
        · exact (hyy' rfl).elim
        · exact hcd
        · exact (mixedGridPartnerGraph K C).adj_symm hcd
        · exact (hyy' rfl).elim
      have hxy' : x ≠ y' := by
        rcases hx with rfl | rfl <;> rcases hy' with rfl | rfl
        · exact hac
        · exact had
        · exact hbc
        · exact hbd
      have hyx' : y ≠ x' := by
        rcases hy with rfl | rfl <;> rcases hx' with rfl | rfl
        · exact hac.symm
        · exact hbc.symm
        · exact had.symm
        · exact hbd.symm
      have hle := code.common_neighbor_card_le_one H K C x y' hxy'
      have hyMem : y ∈ C.neighborFinset x ∩ C.neighborFinset y' := by
        apply Finset.mem_inter.mpr
        exact ⟨(C.mem_neighborFinset x y).mpr hxy,
          (C.mem_neighborFinset y' y).mpr hRight.1.symm⟩
      have hx'Mem : x' ∈ C.neighborFinset x ∩ C.neighborFinset y' := by
        apply Finset.mem_inter.mpr
        exact ⟨(C.mem_neighborFinset x x').mpr hLeft.1,
          (C.mem_neighborFinset y' x').mpr hx'y'.symm⟩
      exact (hyx' (Finset.card_le_one.mp hle y hyMem x' hx'Mem)).elim

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.partnerCrossEdges_card_le_one
