import Proofs.Erdos85MuThreeMixedGridTwoByTwoCompatibility

/-!
# Existential two-by-two compatibility

This packages the local overlap equation using only the invariant statement
that the relevant component has two cells in every row and column.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A residual-confined predicate with two cells in the selected row and
column supplies witnesses satisfying the two-by-two overlap equation. -/
theorem MuThreeMixedGridCode.exists_twoByTwo_overlap_compatibility
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (P : muThreeMixedCell K → Prop) [DecidablePred P]
    (h : X) (y : Y)
    (hconf : ∀ {a b}, P a →
      (mixedGridSquareResidualGraph K C).Adj a b → P b)
    (hrowTwo : (mixedGridPredicateRowFiber P h).card = 2)
    (hcolTwo : (mixedGridPredicateColumnFiber P y).card = 2)
    (hhole : K h y) :
    ∃ u u' v v' : muThreeMixedCell K,
      u ≠ u' ∧ v ≠ v' ∧
      P u ∧ P u' ∧ P v ∧ P v' ∧
      u.1.2 = y ∧ u'.1.2 = y ∧
      v.1.1 = h ∧ v'.1.1 = h ∧
      (mixedGridHCommonColumns H u.1.1 h).card +
          (mixedGridHCommonColumns H u'.1.1 h).card =
        (mixedGridHCommonRows H v.1.2 y).card +
          (mixedGridHCommonRows H v'.1.2 y).card := by
  obtain ⟨v, v', hvv', hrowPair⟩ := Finset.card_eq_two.mp hrowTwo
  obtain ⟨u, u', huu', hcolPair⟩ := Finset.card_eq_two.mp hcolTwo
  have huMem : u ∈ mixedGridPredicateColumnFiber P y := by
    rw [hcolPair]
    simp
  have hu'Mem : u' ∈ mixedGridPredicateColumnFiber P y := by
    rw [hcolPair]
    simp
  have hvMem : v ∈ mixedGridPredicateRowFiber P h := by
    rw [hrowPair]
    simp
  have hv'Mem : v' ∈ mixedGridPredicateRowFiber P h := by
    rw [hrowPair]
    simp
  have huData := (Finset.mem_filter.mp huMem).2
  have hu'Data := (Finset.mem_filter.mp hu'Mem).2
  have hvData := (Finset.mem_filter.mp hvMem).2
  have hv'Data := (Finset.mem_filter.mp hv'Mem).2
  have hhu : h ≠ u.1.1 := by
    intro heq
    exact u.2 (by simpa [heq, huData.2] using hhole)
  have hhu' : h ≠ u'.1.1 := by
    intro heq
    exact u'.2 (by simpa [heq, hu'Data.2] using hhole)
  have hyv : y ≠ v.1.2 := by
    intro heq
    exact v.2 (by simpa [hvData.2, heq] using hhole)
  have hyv' : y ≠ v'.1.2 := by
    intro heq
    exact v'.2 (by simpa [hv'Data.2, heq] using hhole)
  refine ⟨u, u', v, v', huu', hvv', huData.1, hu'Data.1,
    hvData.1, hv'Data.1, huData.2, hu'Data.2,
    hvData.2, hv'Data.2, ?_⟩
  exact code.twoByTwo_overlap_compatibility H K C P u u' v v' h y
    huu' hvv' huData.1 hu'Data.1 hvData.1 hv'Data.1 hconf
    hrowPair hcolPair huData.2 hu'Data.2 hvData.2 hv'Data.2
    hhu hhu' hyv hyv' hhole

end

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.exists_twoByTwo_overlap_compatibility
