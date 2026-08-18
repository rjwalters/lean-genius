import Proofs.Erdos85MuThreeMixedGridTwoByTwoCompatibility

/-!
# Component overlap equation

The two-by-two compatibility law is recorded intrinsically as equality of
two fiber sums, with no choice of names for the two cells in either fiber.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Sum of row-overlaps contributed by the component cells in column `y`. -/
def mixedGridComponentColumnOverlapLoad
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (P : muThreeMixedCell K → Prop) [DecidablePred P]
    (h : X) (y : Y) : ℕ :=
  ∑ u ∈ mixedGridPredicateColumnFiber P y,
    (mixedGridHCommonColumns H u.1.1 h).card

/-- Sum of column-overlaps contributed by the component cells in row `h`. -/
def mixedGridComponentRowOverlapLoad
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (P : muThreeMixedCell K → Prop) [DecidablePred P]
    (h : X) (y : Y) : ℕ :=
  ∑ v ∈ mixedGridPredicateRowFiber P h,
    (mixedGridHCommonRows H v.1.2 y).card

/-- On every forbidden coordinate, a residual-confined two-by-two component
has equal intrinsic row- and column-overlap loads. -/
theorem MuThreeMixedGridCode.componentOverlapLoad_eq
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
    mixedGridComponentColumnOverlapLoad H K P h y =
      mixedGridComponentRowOverlapLoad H K P h y := by
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
  have heq := code.twoByTwo_overlap_compatibility H K C P
    u u' v v' h y huu' hvv' huData.1 hu'Data.1 hvData.1 hv'Data.1
    hconf hrowPair hcolPair huData.2 hu'Data.2 hvData.2 hv'Data.2
    hhu hhu' hyv hyv' hhole
  simpa [mixedGridComponentColumnOverlapLoad,
    mixedGridComponentRowOverlapLoad, hrowPair, hcolPair, huu', hvv'] using heq

end

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.componentOverlapLoad_eq
