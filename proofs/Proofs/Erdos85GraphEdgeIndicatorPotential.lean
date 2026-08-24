import Proofs.Erdos85F2WalkWeightPotential

/-!
# Graph-edge prices: odd holonomy or endpoint potential

Specialize the abstract walk-weight dichotomy to the indicator of an honest
price graph `K`, evaluated along the edges of a routing graph `P`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Binary indicator that an ordered endpoint pair is an edge of `K`. -/
def graphEdgeIndicator {V : Type*} (K : SimpleGraph V) (u v : V) : ZMod 2 :=
  by
    classical
    exact if K.Adj u v then 1 else 0

theorem graphEdgeIndicator_symm {V : Type*} (K : SimpleGraph V) (u v : V) :
    graphEdgeIndicator K u v = graphEdgeIndicator K v u := by
  simp only [graphEdgeIndicator]
  by_cases h : K.Adj u v
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

theorem graphEdgeIndicator_eq_one_iff {V : Type*} (K : SimpleGraph V)
    {u v : V} : graphEdgeIndicator K u v = 1 ↔ K.Adj u v := by
  simp [graphEdgeIndicator]

/-- **Graph-level K-price dichotomy.**  On a connected routing graph `P`,
either a closed `P`-walk has odd total `K`-edge indicator, or the K-indicator
on every P-edge is the sum of endpoint potentials. -/
theorem exists_closedWalk_odd_graphEdgeIndicator_or_exists_vertexPotential
    {V : Type*} (P K : SimpleGraph V)
    (root : V) (hconn : ∀ v, Nonempty (P.Walk root v)) :
    (∃ (u : V) (p : P.Walk u u),
      f2WalkWeight (graphEdgeIndicator K) p = 1) ∨
      ∃ lam : V → ZMod 2, ∀ {u v}, P.Adj u v →
        graphEdgeIndicator K u v = lam u + lam v := by
  exact exists_closedWalk_weight_one_or_exists_vertexPotential
    (graphEdgeIndicator K) (graphEdgeIndicator_symm K) root hconn

/-- In the additive branch, a routing edge lies in `K` exactly when its
endpoint potentials differ. -/
theorem graphEdgeIndicator_adj_iff_potential_sum_eq_one
    {V : Type*} {P K : SimpleGraph V} {lam : V → ZMod 2}
    (hpotential : ∀ {u v}, P.Adj u v →
      graphEdgeIndicator K u v = lam u + lam v)
    {u v : V} (huv : P.Adj u v) :
    K.Adj u v ↔ lam u + lam v = 1 := by
  rw [← graphEdgeIndicator_eq_one_iff]
  rw [hpotential huv]

end

end Erdos85

#print axioms Erdos85.exists_closedWalk_odd_graphEdgeIndicator_or_exists_vertexPotential
#print axioms Erdos85.graphEdgeIndicator_adj_iff_potential_sum_eq_one
