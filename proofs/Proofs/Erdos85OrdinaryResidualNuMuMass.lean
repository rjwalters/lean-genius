import Proofs.Erdos85OrdinaryResidualNuMuDecomposition

/-!
# Aggregate ordinary residual nu/mu mass

Summing the pointwise ordinary residual decomposition over a finite ordinary
set gives the graph-derived right side of `(73rnz_aw)`.
-/

open SimpleGraph

namespace Erdos85

/-- The corrected ordinary atom mass at a center: common-neighbor atoms
`nu` plus cubic cross-neighborhood atoms `mu`. -/
def ordinaryResidualNuMuMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (center : V) (ordinary : Finset V) : ZMod 2 :=
  ∑ z ∈ ordinary,
    ((((A.neighborFinset center ∩ A.neighborFinset z).card : ℕ) : ZMod 2) +
      (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) *
        A.adjMatrix (ZMod 2)) center z)

/-- A graph-indicator sum is the parity of the corresponding finite
neighbor incidence. -/
theorem sum_graphEdgeIndicator_eq_neighbor_inter_card_cast
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (center : V) (S : Finset V) :
    (∑ z ∈ S, graphEdgeIndicator K center z) =
      (((K.neighborFinset center ∩ S).card : ℕ) : ZMod 2) := by
  classical
  have hsum :
      (∑ z ∈ S.filter fun z => K.Adj center z, (1 : ZMod 2)) =
        ∑ z ∈ S, graphEdgeIndicator K center z := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    simp [graphEdgeIndicator]
  have hfilter : S.filter (fun z => K.Adj center z) =
      K.neighborFinset center ∩ S := by
    ext z
    simp [and_comm]
  calc
    (∑ z ∈ S, graphEdgeIndicator K center z) =
        ∑ z ∈ S.filter (fun z => K.Adj center z), (1 : ZMod 2) := hsum.symm
    _ = (((S.filter fun z => K.Adj center z).card : ℕ) : ZMod 2) := by simp
    _ = (((K.neighborFinset center ∩ S).card : ℕ) : ZMod 2) := by rw [hfilter]

/-- **Aggregate ordinary residual decomposition (`73rnz_aw`, right-hand
side).**  Total residual-`K` incidence into a non-ambient ordinary set is
exactly its summed `nu+mu` atom mass. -/
theorem sum_residualIndicator_eq_ordinaryResidualNuMuMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, A.degree v = q)
    (center : V) (ordinary : Finset V)
    (hordinary : ∀ z ∈ ordinary, ¬ A.Adj center z) :
    (∑ z ∈ ordinary,
      graphEdgeIndicator (binaryTransportResidualGraph A hq hreg) center z) =
      ordinaryResidualNuMuMass A center ordinary := by
  unfold ordinaryResidualNuMuMass
  apply Finset.sum_congr rfl
  intro z hz
  exact graphEdgeIndicator_binaryTransportResidual_eq_nu_add_mu_of_not_adj
    A hq hreg (hordinary z hz)

/-- Neighbor-incidence form of the same aggregate identity. -/
theorem residual_neighbor_inter_card_cast_eq_ordinaryResidualNuMuMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, A.degree v = q)
    (center : V) (ordinary : Finset V)
    (hordinary : ∀ z ∈ ordinary, ¬ A.Adj center z) :
    ((((binaryTransportResidualGraph A hq hreg).neighborFinset center ∩
      ordinary).card : ℕ) : ZMod 2) =
      ordinaryResidualNuMuMass A center ordinary := by
  rw [← sum_graphEdgeIndicator_eq_neighbor_inter_card_cast]
  exact sum_residualIndicator_eq_ordinaryResidualNuMuMass
    A hq hreg center ordinary hordinary

end Erdos85

#print axioms Erdos85.sum_graphEdgeIndicator_eq_neighbor_inter_card_cast
#print axioms Erdos85.sum_residualIndicator_eq_ordinaryResidualNuMuMass
#print axioms Erdos85.residual_neighbor_inter_card_cast_eq_ordinaryResidualNuMuMass
