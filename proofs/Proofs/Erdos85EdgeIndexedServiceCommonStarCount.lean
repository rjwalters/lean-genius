import Proofs.Erdos85EdgeIndexedServiceTwoWalkCensus

/-! # Boolean common-neighbor count on an exterior-edge star -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Exterior edges incident to `u` that share a service neighbor with `a`. -/
def incidentServiceCommonEdgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (u : V) (a : R.edgeFinset) : Finset R.edgeFinset :=
  Finset.univ.filter fun b ↦
    u ∈ b.1.toFinset ∧
      (Cedge.neighborFinset b ∩ Cedge.neighborFinset a).Nonempty

theorem incidentServiceTwoWalkMass_eq_commonEdge_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (u : V) (a : R.edgeFinset) (hua : u ∉ a.1.toFinset) :
    incidentServiceTwoWalkMass R Cedge u a =
      (incidentServiceCommonEdgeFinset R Cedge u a).card := by
  classical
  unfold incidentServiceTwoWalkMass
  calc
    (∑ b : R.edgeFinset, if u ∈ b.1.toFinset then
        (Cedge.neighborFinset b ∩ Cedge.neighborFinset a).card else 0) =
        ∑ b : R.edgeFinset, if u ∈ b.1.toFinset ∧
          (Cedge.neighborFinset b ∩ Cedge.neighborFinset a).Nonempty
          then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hub : u ∈ b.1.toFinset
      · have hba : b ≠ a := by
          intro h
          exact hua (h ▸ hub)
        have hle := common_le_one_of_not_containsC4 hfree b a hba
        by_cases hn :
            (Cedge.neighborFinset b ∩ Cedge.neighborFinset a).Nonempty
        · have hpos : 0 <
              (Cedge.neighborFinset b ∩ Cedge.neighborFinset a).card :=
            Finset.card_pos.mpr hn
          have hcard :
              (Cedge.neighborFinset b ∩ Cedge.neighborFinset a).card = 1 := by
            omega
          simp [hub, hn, hcard]
        · have hempty :
              Cedge.neighborFinset b ∩ Cedge.neighborFinset a = ∅ :=
            Finset.not_nonempty_iff_eq_empty.mp hn
          simp [hub, hempty]
      · simp [hub]
    _ = (incidentServiceCommonEdgeFinset R Cedge u a).card := by
      rw [Finset.sum_boole]
      rfl

/-- In a `C₄`-free 2-by-6 service model, exactly `4` plus the internal
two-walk endpoint mass many edges through `u` share a service neighbor with
`a`, provided `u` is not itself an endpoint of `a`. -/
theorem edgeIndexedService_commonStarCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hCreg : ∀ a, Cedge.degree a = 6)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (u : V) (a : R.edgeFinset) (hua : u ∉ a.1.toFinset) :
    (incidentServiceCommonEdgeFinset R Cedge u a).card =
      internalEndpointTwoWalkMass H R u a + 4 := by
  rw [← incidentServiceTwoWalkMass_eq_commonEdge_card R Cedge hfree u a hua]
  exact edgeIndexedService_twoWalkCensus
    H R Cedge hservice hHreg hCreg u a

end

end Erdos85

#print axioms Erdos85.edgeIndexedService_commonStarCount
