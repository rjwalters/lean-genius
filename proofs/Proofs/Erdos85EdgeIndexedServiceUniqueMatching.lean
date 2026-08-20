import Proofs.Erdos85EdgeIndexedServiceMatchingLaw

/-! # Unique matching law for edge-indexed service neighborhoods -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- A support vertex belongs to exactly one neighboring service edge precisely
when it is adjacent in `H` to neither endpoint of the central exterior edge. -/
theorem edgeIndexedService_existsUnique_incidentNeighbor_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (u : V) (a : R.edgeFinset) :
    (∃! b : R.edgeFinset, Cedge.Adj a b ∧ u ∈ b.1.toFinset) ↔
      (internalEndpointNeighborFinset H R u a).card = 0 := by
  classical
  constructor
  · rintro ⟨b, hb, _⟩
    exact (edgeIndexedService_exists_incidentNeighbor_iff
      H R Cedge hservice u a).mp ⟨b, hb⟩
  · intro hzero
    obtain ⟨b, hb⟩ := (edgeIndexedService_exists_incidentNeighbor_iff
      H R Cedge hservice u a).mpr hzero
    refine ⟨b, hb, ?_⟩
    intro d hd
    by_contra hdb
    have hdisj := edgeIndexedService_neighborEdges_pairwiseDisjoint
      H R Cedge hservice a b d hb.1 hd.1 (Ne.symm hdb)
    rw [Finset.disjoint_left] at hdisj
    exact hdisj hb.2 hd.2

/-- The local service equation canonically matches every vertex avoiding both
endpoint neighborhoods with the unique neighboring exterior edge containing it. -/
theorem edgeIndexedService_unique_incidentNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (u : V) (a : R.edgeFinset)
    (hzero : (internalEndpointNeighborFinset H R u a).card = 0) :
    ∃! b : R.edgeFinset, Cedge.Adj a b ∧ u ∈ b.1.toFinset :=
  (edgeIndexedService_existsUnique_incidentNeighbor_iff
    H R Cedge hservice u a).mpr hzero

end

end Erdos85

#print axioms Erdos85.edgeIndexedService_existsUnique_incidentNeighbor_iff
