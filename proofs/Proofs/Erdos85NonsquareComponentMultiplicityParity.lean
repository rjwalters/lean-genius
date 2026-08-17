import Proofs.Erdos85QuadraticDimensionField
import Proofs.Erdos85ConnectedComponentEigenspaceDecomposition

/-!
# Component multiplicity parity in the nonsquare branch

Combining nonsquare evenness of the global defect eigenspace with its exact
connected-component decomposition shows that the sum of the corresponding
component multiplicities is even.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Case B component multiplicity parity.** -/
theorem graph_even_sum_component_multiplicities_of_regular_excess_field
    {K : Type*} [Field K] [CharZero K]
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d e : ℕ}
    (hreg : ∀ x, G.degree x = d)
    (hregD : ∀ x, (secondOrderDefectGraph G).degree x = e + 2)
    {μ : K} (hμ : μ ≠ (e + 2 : ℕ))
    (hnonsquare : ¬ IsSquare ((d : K) - 1 - μ)) :
    Even (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      Module.finrank K
        (defectEigenspace
          (((secondOrderDefectGraph G).induce c.supp).adjMatrix K) μ)) := by
  have heven := graph_even_finrank_defectEigenspace_of_regular_excess_field
    G hfree hreg hregD hμ hnonsquare
  rw [finrank_defectEigenspace_eq_sum_components] at heven
  exact heven

end

end Erdos85
