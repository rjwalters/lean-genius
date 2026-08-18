import Proofs.Erdos85MuThreeMixedGridResidualComponentOverlap
import Proofs.Erdos85ThreeFiberSaturation

/-! # Residual-component saturation in a three-cell row fiber -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In a residual component with three cells in the target row, a cell's
two residual mates in that row are exactly the component fiber minus any
known excluded cell. -/
theorem residualMatesInRow_eq_componentFiber_erase_of_three
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (K : X → Y → Prop) [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    [DecidableEq (mixedGridSquareResidualGraph K C).ConnectedComponent]
    (c : (mixedGridSquareResidualGraph K C).ConnectedComponent)
    (u : muThreeMixedCell K) (x : X) (z : muThreeMixedCell K)
    (hu : mixedGridResidualComponentPredicate K C c u)
    (hmates : (mixedGridGraphMatesInRow
      (mixedGridSquareResidualGraph K C) u x).card = 2)
    (hfiber : (mixedGridPredicateRowFiber
      (mixedGridResidualComponentPredicate K C c) x).card = 3)
    (hzfiber : z ∈ mixedGridPredicateRowFiber
      (mixedGridResidualComponentPredicate K C c) x)
    (hznot : z ∉ mixedGridGraphMatesInRow
      (mixedGridSquareResidualGraph K C) u x) :
    mixedGridGraphMatesInRow (mixedGridSquareResidualGraph K C) u x =
      (mixedGridPredicateRowFiber
        (mixedGridResidualComponentPredicate K C c) x).erase z := by
  apply two_subset_three_eq_erase_of_not_mem
  · intro v hv
    have hv' := Finset.mem_filter.mp hv
    have huv := ((mixedGridSquareResidualGraph K C).mem_neighborFinset u v).mp hv'.1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ v,
      mixedGridResidualComponentPredicate_closed K C c hu huv, hv'.2⟩
  · exact hmates
  · exact hfiber
  · exact hzfiber
  · exact hznot

/-- Column-dual saturation statement. -/
theorem residualMatesInColumn_eq_componentFiber_erase_of_three
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (K : X → Y → Prop) [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    [DecidableEq (mixedGridSquareResidualGraph K C).ConnectedComponent]
    (c : (mixedGridSquareResidualGraph K C).ConnectedComponent)
    (u : muThreeMixedCell K) (y : Y) (z : muThreeMixedCell K)
    (hu : mixedGridResidualComponentPredicate K C c u)
    (hmates : (mixedGridGraphMatesInColumn
      (mixedGridSquareResidualGraph K C) u y).card = 2)
    (hfiber : (mixedGridPredicateColumnFiber
      (mixedGridResidualComponentPredicate K C c) y).card = 3)
    (hzfiber : z ∈ mixedGridPredicateColumnFiber
      (mixedGridResidualComponentPredicate K C c) y)
    (hznot : z ∉ mixedGridGraphMatesInColumn
      (mixedGridSquareResidualGraph K C) u y) :
    mixedGridGraphMatesInColumn (mixedGridSquareResidualGraph K C) u y =
      (mixedGridPredicateColumnFiber
        (mixedGridResidualComponentPredicate K C c) y).erase z := by
  apply two_subset_three_eq_erase_of_not_mem
  · intro v hv
    have hv' := Finset.mem_filter.mp hv
    have huv := ((mixedGridSquareResidualGraph K C).mem_neighborFinset u v).mp hv'.1
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ v,
      mixedGridResidualComponentPredicate_closed K C c hu huv, hv'.2⟩
  · exact hmates
  · exact hfiber
  · exact hzfiber
  · exact hznot

end

end Erdos85

#print axioms Erdos85.residualMatesInRow_eq_componentFiber_erase_of_three
#print axioms Erdos85.residualMatesInColumn_eq_componentFiber_erase_of_three
