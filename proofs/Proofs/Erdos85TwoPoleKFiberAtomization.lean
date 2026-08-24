import Proofs.Erdos85TwoPoleMinimumSplitPairDichotomy
import Proofs.Erdos85OrdinaryResidualNuMuDecomposition

/-!
# Atomization of the minimum two-pole K-fiber

This is `(73rnz_bw)`: away from the adjacent endpoint, a residual K-edge
from an empty pole is the sum of the ordinary-type bit and the cubic
cross-neighborhood matching bit.
-/

open SimpleGraph

namespace Erdos85

/-- The common-neighbor bit of an exceptional pole is exactly the ordinary
type bit when defect adjacency is the complementary exceptional census. -/
theorem commonNeighbor_card_cast_eq_ordinaryIndicator
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    [DecidableRel (antipodalGraph A).Adj]
    [DecidableRel (triangleFreeEdgeGraph A).Adj]
    (hfree : ¬ containsC4 V A)
    (ordinary : Finset V) (pole z : V) (hne : pole ≠ z)
    (hordinary : z ∈ ordinary ↔
      z ∉ (secondOrderDefectGraph A).neighborFinset pole) :
    ((((A.neighborFinset pole ∩ A.neighborFinset z).card : ℕ) : ZMod 2)) =
      if z ∈ ordinary then 1 else 0 := by
  rw [card_common_eq_if_secondOrderDefect A hfree pole z hne]
  by_cases hzO : z ∈ ordinary
  · have hzD : z ∉ (secondOrderDefectGraph A).neighborFinset pole :=
      hordinary.mp hzO
    rw [if_neg hzD, if_pos hzO]
    norm_num
  · have hzD : z ∈ (secondOrderDefectGraph A).neighborFinset pole := by
      by_contra hnD
      exact hzO (hordinary.mpr hnD)
    rw [if_pos hzD, if_neg hzO]
    norm_num

/-- **K-fiber atomization (`73rnz_bw`).** -/
theorem graphEdgeIndicator_residual_eq_ordinaryIndicator_add_cube
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    [DecidableRel (antipodalGraph A).Adj]
    [DecidableRel (triangleFreeEdgeGraph A).Adj]
    (hfree : ¬ containsC4 V A)
    {q : ℕ} (hq : Even q) (hreg : ∀ v, A.degree v = q)
    (ordinary : Finset V) (pole z : V) (hne : pole ≠ z)
    (hnotA : ¬ A.Adj pole z)
    (hordinary : z ∈ ordinary ↔
      z ∉ (secondOrderDefectGraph A).neighborFinset pole) :
    graphEdgeIndicator (binaryTransportResidualGraph A hq hreg) pole z =
      (if z ∈ ordinary then 1 else 0) +
        (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) *
          A.adjMatrix (ZMod 2)) pole z := by
  rw [graphEdgeIndicator_binaryTransportResidual_eq_nu_add_mu_of_not_adj
    A hq hreg hnotA]
  rw [commonNeighbor_card_cast_eq_ordinaryIndicator
    A hfree ordinary pole z hne hordinary]

end Erdos85

#print axioms Erdos85.commonNeighbor_card_cast_eq_ordinaryIndicator
#print axioms Erdos85.graphEdgeIndicator_residual_eq_ordinaryIndicator_add_cube
