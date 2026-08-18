import Proofs.Erdos85MinimumLayerSaturatedExterior
import Proofs.Erdos85AntipodalCycleReservoir

/-!
# The cyclic reservoir in the saturated residual exterior

The exceptional saturated descent produces a `123`-regular `C₄`-free graph
on `15120 = 123 * 122 + 3 + 111` vertices.  Existing positive-excess
identities therefore make its combined second-order defect graph
`113`-regular.  Since both the degree and the excess are odd, its antipodal
subgraph has positive even degree at every vertex and contains a cycle.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Named exterior graph, used to keep the positive-excess interfaces and
their decidability instances stable. -/
def saturatedExteriorGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent) :
    SimpleGraph (minimumLayerExteriorVertex (secondOrderDefectGraph G) c₀) :=
  G.comap Subtype.val

/-- Every `C₄`-free `123`-regular graph on `15120` vertices has a
`113`-regular combined defect graph and a cyclic antipodal reservoir.  The
saturated residual exterior supplied by
`minimumLayer_saturated_124_exterior_profile` is exactly such a graph. -/
theorem degree_123_order_15120_reservoir
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (R : SimpleGraph X) [DecidableRel R.Adj]
    [DecidableRel (antipodalGraph R).Adj]
    [DecidableRel (triangleFreeEdgeGraph R).Adj]
    (hfree : ¬containsC4 X R)
    (hreg : ∀ x, R.degree x = 123)
    (hcard : Fintype.card X = 15120) :
    (∀ x, (secondOrderDefectGraph R).degree x = 113) ∧
      (∀ x, Even ((antipodalGraph R).degree x) ∧
        2 ≤ (antipodalGraph R).degree x) ∧
      ¬(antipodalGraph R).IsAcyclic := by
  have hcardExcess : Fintype.card X = 123 * (123 - 1) + 3 + 111 := by
    norm_num at hcard ⊢
    exact hcard
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simpa using secondOrderDefectGraph_degree_eq_excess_add_two
      R hfree (d := 123) (e := 111) hreg hcardExcess x
  · intro x
    exact antipodalGraph_degree_even_and_two_le_of_odd
      R hfree (d := 123) (e := 111)
        (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hreg hcardExcess x
  · exact antipodalGraph_not_isAcyclic_of_odd
      R hfree (d := 123) (e := 111)
        (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hreg hcardExcess

end

end Erdos85
