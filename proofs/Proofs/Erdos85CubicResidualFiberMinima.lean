import Proofs.Erdos85CubicResidualFiberHistogram
import Proofs.Erdos85CubicFiberHistogramMinima

/-! # Graph-facing sharp minima for cubic residual fibers -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

theorem cubicResidualFiber_squareMass_ge_96_of_budget24
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hRreg : ∀ u, R.degree u = 6)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (u : V) (a : R.edgeFinset)
    (hmass : incidentServiceCubicWalkMass R Cedge u a = 24)
    (hnbr : (incidentServiceNeighborFiber R Cedge u a).card = 0) :
    96 ≤ ∑ b ∈ cubicResidualFiber R Cedge u a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2 := by
  let c := cubicResidualFiberHistogram R Cedge u a
  obtain ⟨hc, hs, hq⟩ := cubicResidualFiberHistogram_ledger
    R Cedge hfree hCreg u a
  have hcard := cubicResidualFiber_card_add_neighbor_card R Cedge u a
  rw [hRreg, hnbr] at hcard
  change (∑ t ∈ Finset.range 7, c t) = _ at hc
  change (∑ t ∈ Finset.range 7, t * c t) = _ at hs
  rw [hmass, hnbr] at hs
  norm_num at hs
  have hmin := six_cubicValues_sum_twentyFour_minimum c (by omega) hs
  rw [hq] at hmin
  exact hmin

theorem cubicResidualFiber_squareMass_ge_105_of_budget25
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hRreg : ∀ u, R.degree u = 6)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (u : V) (a : R.edgeFinset)
    (hmass : incidentServiceCubicWalkMass R Cedge u a = 25)
    (hnbr : (incidentServiceNeighborFiber R Cedge u a).card = 0) :
    105 ≤ ∑ b ∈ cubicResidualFiber R Cedge u a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2 := by
  let c := cubicResidualFiberHistogram R Cedge u a
  obtain ⟨hc, hs, hq⟩ := cubicResidualFiberHistogram_ledger
    R Cedge hfree hCreg u a
  have hcard := cubicResidualFiber_card_add_neighbor_card R Cedge u a
  rw [hRreg, hnbr] at hcard
  change (∑ t ∈ Finset.range 7, c t) = _ at hc
  change (∑ t ∈ Finset.range 7, t * c t) = _ at hs
  rw [hmass, hnbr] at hs
  norm_num at hs
  have hmin := six_cubicValues_sum_twentyFive_minimum c (by omega) hs
  rw [hq] at hmin
  exact hmin

theorem cubicResidualFiber_squareMass_ge_52_of_budget27_neighborOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hRreg : ∀ u, R.degree u = 6)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (u : V) (a : R.edgeFinset)
    (hmass : incidentServiceCubicWalkMass R Cedge u a = 27)
    (hnbr : (incidentServiceNeighborFiber R Cedge u a).card = 1) :
    52 ≤ ∑ b ∈ cubicResidualFiber R Cedge u a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2 := by
  let c := cubicResidualFiberHistogram R Cedge u a
  obtain ⟨hc, hs, hq⟩ := cubicResidualFiberHistogram_ledger
    R Cedge hfree hCreg u a
  have hcard := cubicResidualFiber_card_add_neighbor_card R Cedge u a
  rw [hRreg, hnbr] at hcard
  change (∑ t ∈ Finset.range 7, c t) = _ at hc
  change (∑ t ∈ Finset.range 7, t * c t) = _ at hs
  rw [hmass, hnbr] at hs
  norm_num at hs
  have hmin := five_cubicValues_sum_sixteen_minimum c (by omega) (by omega)
  rw [hq] at hmin
  exact hmin

theorem cubicResidualFiber_squareMass_ge_59_of_budget28_neighborOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hRreg : ∀ u, R.degree u = 6)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (u : V) (a : R.edgeFinset)
    (hmass : incidentServiceCubicWalkMass R Cedge u a = 28)
    (hnbr : (incidentServiceNeighborFiber R Cedge u a).card = 1) :
    59 ≤ ∑ b ∈ cubicResidualFiber R Cedge u a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2 := by
  let c := cubicResidualFiberHistogram R Cedge u a
  obtain ⟨hc, hs, hq⟩ := cubicResidualFiberHistogram_ledger
    R Cedge hfree hCreg u a
  have hcard := cubicResidualFiber_card_add_neighbor_card R Cedge u a
  rw [hRreg, hnbr] at hcard
  change (∑ t ∈ Finset.range 7, c t) = _ at hc
  change (∑ t ∈ Finset.range 7, t * c t) = _ at hs
  rw [hmass, hnbr] at hs
  norm_num at hs
  have hmin := five_cubicValues_sum_seventeen_minimum c (by omega) (by omega)
  rw [hq] at hmin
  exact hmin

end

end Erdos85

#print axioms Erdos85.cubicResidualFiber_squareMass_ge_96_of_budget24
#print axioms Erdos85.cubicResidualFiber_squareMass_ge_105_of_budget25
#print axioms
  Erdos85.cubicResidualFiber_squareMass_ge_52_of_budget27_neighborOne
#print axioms
  Erdos85.cubicResidualFiber_squareMass_ge_59_of_budget28_neighborOne
