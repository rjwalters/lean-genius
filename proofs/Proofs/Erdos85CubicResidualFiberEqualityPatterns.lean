import Proofs.Erdos85CubicResidualFiberMinima

/-! # Graph-facing equality patterns for cubic residual fibers -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

theorem cubicResidualFiberHistogram_eq_pattern_24
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hRreg : ∀ u, R.degree u = 6)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (u : V) (a : R.edgeFinset)
    (hmass : incidentServiceCubicWalkMass R Cedge u a = 24)
    (hnbr : (incidentServiceNeighborFiber R Cedge u a).card = 0)
    (hsq : (∑ b ∈ cubicResidualFiber R Cedge u a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2) ≤ 96) :
    let c := cubicResidualFiberHistogram R Cedge u a
    c 0 = 0 ∧ c 1 = 0 ∧ c 2 = 0 ∧ c 3 = 0 ∧
      c 4 = 6 ∧ c 5 = 0 ∧ c 6 = 0 := by
  dsimp only
  let c := cubicResidualFiberHistogram R Cedge u a
  obtain ⟨hc, hs, hq⟩ := cubicResidualFiberHistogram_ledger
    R Cedge hfree hCreg u a
  have hcard := cubicResidualFiber_card_add_neighbor_card R Cedge u a
  rw [hRreg, hnbr] at hcard
  change (∑ t ∈ Finset.range 7, c t) = _ at hc
  change (∑ t ∈ Finset.range 7, t * c t) = _ at hs
  rw [hmass, hnbr] at hs
  norm_num at hs
  apply six_cubicValues_sum_twentyFour_eq_minimum c (by omega) hs
  rw [hq]
  exact hsq

theorem cubicResidualFiberHistogram_eq_pattern_25
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hRreg : ∀ u, R.degree u = 6)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (u : V) (a : R.edgeFinset)
    (hmass : incidentServiceCubicWalkMass R Cedge u a = 25)
    (hnbr : (incidentServiceNeighborFiber R Cedge u a).card = 0)
    (hsq : (∑ b ∈ cubicResidualFiber R Cedge u a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2) ≤ 105) :
    let c := cubicResidualFiberHistogram R Cedge u a
    c 0 = 0 ∧ c 1 = 0 ∧ c 2 = 0 ∧ c 3 = 0 ∧
      c 4 = 5 ∧ c 5 = 1 ∧ c 6 = 0 := by
  dsimp only
  let c := cubicResidualFiberHistogram R Cedge u a
  obtain ⟨hc, hs, hq⟩ := cubicResidualFiberHistogram_ledger
    R Cedge hfree hCreg u a
  have hcard := cubicResidualFiber_card_add_neighbor_card R Cedge u a
  rw [hRreg, hnbr] at hcard
  change (∑ t ∈ Finset.range 7, c t) = _ at hc
  change (∑ t ∈ Finset.range 7, t * c t) = _ at hs
  rw [hmass, hnbr] at hs
  norm_num at hs
  apply six_cubicValues_sum_twentyFive_eq_minimum c (by omega) hs
  rw [hq]
  exact hsq

theorem cubicResidualFiberHistogram_eq_pattern_16
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hRreg : ∀ u, R.degree u = 6)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (u : V) (a : R.edgeFinset)
    (hmass : incidentServiceCubicWalkMass R Cedge u a = 27)
    (hnbr : (incidentServiceNeighborFiber R Cedge u a).card = 1)
    (hsq : (∑ b ∈ cubicResidualFiber R Cedge u a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2) ≤ 52) :
    let c := cubicResidualFiberHistogram R Cedge u a
    c 0 = 0 ∧ c 1 = 0 ∧ c 2 = 0 ∧ c 3 = 4 ∧
      c 4 = 1 ∧ c 5 = 0 ∧ c 6 = 0 := by
  dsimp only
  let c := cubicResidualFiberHistogram R Cedge u a
  obtain ⟨hc, hs, hq⟩ := cubicResidualFiberHistogram_ledger
    R Cedge hfree hCreg u a
  have hcard := cubicResidualFiber_card_add_neighbor_card R Cedge u a
  rw [hRreg, hnbr] at hcard
  change (∑ t ∈ Finset.range 7, c t) = _ at hc
  change (∑ t ∈ Finset.range 7, t * c t) = _ at hs
  rw [hmass, hnbr] at hs
  norm_num at hs
  apply five_cubicValues_sum_sixteen_eq_minimum c (by omega) (by omega)
  rw [hq]
  exact hsq

theorem cubicResidualFiberHistogram_eq_pattern_17
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hRreg : ∀ u, R.degree u = 6)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (u : V) (a : R.edgeFinset)
    (hmass : incidentServiceCubicWalkMass R Cedge u a = 28)
    (hnbr : (incidentServiceNeighborFiber R Cedge u a).card = 1)
    (hsq : (∑ b ∈ cubicResidualFiber R Cedge u a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2) ≤ 59) :
    let c := cubicResidualFiberHistogram R Cedge u a
    c 0 = 0 ∧ c 1 = 0 ∧ c 2 = 0 ∧ c 3 = 3 ∧
      c 4 = 2 ∧ c 5 = 0 ∧ c 6 = 0 := by
  dsimp only
  let c := cubicResidualFiberHistogram R Cedge u a
  obtain ⟨hc, hs, hq⟩ := cubicResidualFiberHistogram_ledger
    R Cedge hfree hCreg u a
  have hcard := cubicResidualFiber_card_add_neighbor_card R Cedge u a
  rw [hRreg, hnbr] at hcard
  change (∑ t ∈ Finset.range 7, c t) = _ at hc
  change (∑ t ∈ Finset.range 7, t * c t) = _ at hs
  rw [hmass, hnbr] at hs
  norm_num at hs
  apply five_cubicValues_sum_seventeen_eq_minimum c (by omega) (by omega)
  rw [hq]
  exact hsq

end

end Erdos85

#print axioms Erdos85.cubicResidualFiberHistogram_eq_pattern_24
#print axioms Erdos85.cubicResidualFiberHistogram_eq_pattern_25
#print axioms Erdos85.cubicResidualFiberHistogram_eq_pattern_16
#print axioms Erdos85.cubicResidualFiberHistogram_eq_pattern_17
