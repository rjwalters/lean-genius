import Proofs.Erdos85MuThreeMixedGridComponentOverlapEquation

/-!
# Residual-component overlap equation

This specializes the intrinsic two-by-two equation to a connected component
of the residual graph, discharging the confinement hypothesis automatically.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

def mixedGridResidualComponentPredicate
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (K : X → Y → Prop) [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    [DecidableEq (mixedGridSquareResidualGraph K C).ConnectedComponent]
    (c : (mixedGridSquareResidualGraph K C).ConnectedComponent)
    (u : muThreeMixedCell K) : Prop :=
  (mixedGridSquareResidualGraph K C).connectedComponentMk u = c

instance mixedGridResidualComponentPredicate_decidable
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (K : X → Y → Prop) [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    [DecidableEq (mixedGridSquareResidualGraph K C).ConnectedComponent]
    (c : (mixedGridSquareResidualGraph K C).ConnectedComponent) :
    DecidablePred (mixedGridResidualComponentPredicate K C c) :=
  fun u => show Decidable
    ((mixedGridSquareResidualGraph K C).connectedComponentMk u = c) from
      inferInstance

theorem mixedGridResidualComponentPredicate_closed
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (K : X → Y → Prop) [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    [DecidableEq (mixedGridSquareResidualGraph K C).ConnectedComponent]
    (c : (mixedGridSquareResidualGraph K C).ConnectedComponent)
    {a b : muThreeMixedCell K}
    (ha : mixedGridResidualComponentPredicate K C c a)
    (hab : (mixedGridSquareResidualGraph K C).Adj a b) :
    mixedGridResidualComponentPredicate K C c b := by
  exact (ConnectedComponent.connectedComponentMk_eq_of_adj hab).symm.trans ha

/-- The overlap-load equation for an actual residual connected component.
Only the two fiber-cardinality facts remain as external inputs. -/
theorem MuThreeMixedGridCode.residualComponentOverlapLoad_eq
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    [DecidableEq (mixedGridSquareResidualGraph K C).ConnectedComponent]
    (c : (mixedGridSquareResidualGraph K C).ConnectedComponent)
    (h : X) (y : Y)
    (hrowTwo : (mixedGridPredicateRowFiber
      (mixedGridResidualComponentPredicate K C c) h).card = 2)
    (hcolTwo : (mixedGridPredicateColumnFiber
      (mixedGridResidualComponentPredicate K C c) y).card = 2)
    (hhole : K h y) :
    mixedGridComponentColumnOverlapLoad H K
        (mixedGridResidualComponentPredicate K C c) h y =
      mixedGridComponentRowOverlapLoad H K
        (mixedGridResidualComponentPredicate K C c) h y := by
  apply code.componentOverlapLoad_eq H K C
    (mixedGridResidualComponentPredicate K C c) h y
  · intro a b ha hab
    exact mixedGridResidualComponentPredicate_closed K C c ha hab
  · exact hrowTwo
  · exact hcolTwo
  · exact hhole

end


end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.residualComponentOverlapLoad_eq
