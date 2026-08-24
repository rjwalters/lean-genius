import Proofs.Erdos85OrdinaryResidualNuMuMass

/-!
# Residual-center K-incidence balance

This is the graph-native shore/partition step in `(73rnz_as)`.  If the
`K`-incidence of a residual center into a shore is even, and that shore is
the disjoint union of two exceptional centers and the ordinary vertices,
then the two exceptional indicators equal the ordinary incidence mass.

The final theorem also substitutes the exact exceptional decompositions
`1[EᵢG ∈ K] = cᵢ + rhoᵢ`.  In particular, neither the shore parity nor its
partition is hidden inside an owner-transport assumption.
-/

open SimpleGraph

namespace Erdos85

/-- The two-exception partition form of the residual-center shore balance. -/
theorem exceptional_indicator_sum_eq_ordinary_indicator_sum_of_even_shore
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (center E₁ E₂ : V) (ordinary shore : Finset V)
    (hshore : shore = insert E₁ (insert E₂ ordinary))
    (h₁₂ : E₁ ≠ E₂) (h₁ : E₁ ∉ ordinary) (h₂ : E₂ ∉ ordinary)
    (heven : Even ((K.neighborFinset center ∩ shore).card)) :
    graphEdgeIndicator K center E₁ + graphEdgeIndicator K center E₂ =
      ∑ z ∈ ordinary, graphEdgeIndicator K center z := by
  have hzero :
      ((((K.neighborFinset center ∩ shore).card : ℕ) : ZMod 2)) = 0 := by
    rcases heven with ⟨n, hn⟩
    rw [hn]
    push_cast
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  rw [← sum_graphEdgeIndicator_eq_neighbor_inter_card_cast] at hzero
  rw [hshore] at hzero
  simp [h₁₂, h₁, h₂] at hzero
  have habs :
      (graphEdgeIndicator K center E₁ + graphEdgeIndicator K center E₂) +
          (∑ z ∈ ordinary, graphEdgeIndicator K center z) = 0 := by
    simpa [add_assoc] using hzero
  have hneg (x : ZMod 2) : -x = x := by
    have hx : x + x = 0 := by
      rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
    exact (eq_neg_of_add_eq_zero_left hx).symm
  exact (eq_neg_of_add_eq_zero_left habs).trans (hneg _)

/-- **Residual-center balance (`73rnz_as`).**  After exposing the two
exceptional `K` indicators as their switch cell `c` plus unused matching
cell `rho`, their total equals the ordinary `K` incidence mass. -/
theorem switch_add_residualMatching_sum_eq_ordinary_indicator_sum_of_even_shore
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (center E₁ E₂ : V) (ordinary shore : Finset V)
    (c₁ rho₁ c₂ rho₂ : ZMod 2)
    (hshore : shore = insert E₁ (insert E₂ ordinary))
    (h₁₂ : E₁ ≠ E₂) (h₁ : E₁ ∉ ordinary) (h₂ : E₂ ∉ ordinary)
    (heven : Even ((K.neighborFinset center ∩ shore).card))
    (hdecomp₁ : graphEdgeIndicator K center E₁ = c₁ + rho₁)
    (hdecomp₂ : graphEdgeIndicator K center E₂ = c₂ + rho₂) :
    (c₁ + rho₁) + (c₂ + rho₂) =
      ∑ z ∈ ordinary, graphEdgeIndicator K center z := by
  rw [← hdecomp₁, ← hdecomp₂]
  exact exceptional_indicator_sum_eq_ordinary_indicator_sum_of_even_shore
    K center E₁ E₂ ordinary shore hshore h₁₂ h₁ h₂ heven

/-- **Fully incidence-resolved centerwise law (`73rnz_aw`).**  For the
binary residual graph, the graph-native shore balance and the ordinary
`nu+mu` decomposition compose without an auxiliary `K`-edge ledger. -/
theorem switch_add_residualMatching_sum_eq_ordinaryResidualNuMuMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ v, A.degree v = q)
    (center E₁ E₂ : V) (ordinary shore : Finset V)
    (c₁ rho₁ c₂ rho₂ : ZMod 2)
    (hshore : shore = insert E₁ (insert E₂ ordinary))
    (h₁₂ : E₁ ≠ E₂) (h₁ : E₁ ∉ ordinary) (h₂ : E₂ ∉ ordinary)
    (heven : Even (((binaryTransportResidualGraph A hq hreg).neighborFinset
      center ∩ shore).card))
    (hdecomp₁ : graphEdgeIndicator (binaryTransportResidualGraph A hq hreg)
      center E₁ = c₁ + rho₁)
    (hdecomp₂ : graphEdgeIndicator (binaryTransportResidualGraph A hq hreg)
      center E₂ = c₂ + rho₂)
    (hordinary : ∀ z ∈ ordinary, ¬ A.Adj center z) :
    (c₁ + rho₁) + (c₂ + rho₂) =
      ordinaryResidualNuMuMass A center ordinary := by
  calc
    (c₁ + rho₁) + (c₂ + rho₂) =
        ∑ z ∈ ordinary,
          graphEdgeIndicator (binaryTransportResidualGraph A hq hreg) center z :=
      switch_add_residualMatching_sum_eq_ordinary_indicator_sum_of_even_shore
        (binaryTransportResidualGraph A hq hreg) center E₁ E₂ ordinary shore
        c₁ rho₁ c₂ rho₂ hshore h₁₂ h₁ h₂ heven hdecomp₁ hdecomp₂
    _ = ordinaryResidualNuMuMass A center ordinary :=
      sum_residualIndicator_eq_ordinaryResidualNuMuMass
        A hq hreg center ordinary hordinary

end Erdos85

#print axioms Erdos85.exceptional_indicator_sum_eq_ordinary_indicator_sum_of_even_shore
#print axioms Erdos85.switch_add_residualMatching_sum_eq_ordinary_indicator_sum_of_even_shore
#print axioms Erdos85.switch_add_residualMatching_sum_eq_ordinaryResidualNuMuMass
