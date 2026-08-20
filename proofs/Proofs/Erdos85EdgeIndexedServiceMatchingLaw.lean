import Proofs.Erdos85EdgeIndexedServiceLocalLaw

/-! # Matching law for neighboring service edges -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

theorem edgeIndexedService_localDichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (u : V) (a : R.edgeFinset) :
    (internalEndpointNeighborFinset H R u a).card ≤ 1 ∧
      ((incidentServiceNeighborFinset R Cedge u a).card = 1 ↔
        (internalEndpointNeighborFinset H R u a).card = 0) ∧
      ((incidentServiceNeighborFinset R Cedge u a).card = 0 ↔
        (internalEndpointNeighborFinset H R u a).card = 1) := by
  have h := edgeIndexedService_localLaw H R Cedge hservice u a
  omega

/-- A support vertex occurs in a neighboring service edge exactly when it is
adjacent in `H` to neither endpoint of the central exterior edge. -/
theorem edgeIndexedService_exists_incidentNeighbor_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (u : V) (a : R.edgeFinset) :
    (∃ b : R.edgeFinset, Cedge.Adj a b ∧ u ∈ b.1.toFinset) ↔
      (internalEndpointNeighborFinset H R u a).card = 0 := by
  classical
  rw [← (edgeIndexedService_localDichotomy H R Cedge hservice u a).2.1]
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    ext d
    simp only [incidentServiceNeighborFinset, Finset.mem_filter,
      SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨hda, hud⟩
      have hdb : d = b := by
        by_contra hne
        have hbmem : b ∈ incidentServiceNeighborFinset R Cedge u a := by
          exact Finset.mem_filter.mpr ⟨(Cedge.mem_neighborFinset a b).mpr hb.1, hb.2⟩
        have hdmem : d ∈ incidentServiceNeighborFinset R Cedge u a := by
          exact Finset.mem_filter.mpr ⟨(Cedge.mem_neighborFinset a d).mpr hda, hud⟩
        have htwo : 2 ≤ (incidentServiceNeighborFinset R Cedge u a).card := by
          have hsub : ({b, d} : Finset R.edgeFinset) ⊆
              incidentServiceNeighborFinset R Cedge u a := by
            intro q hq
            simp only [Finset.mem_insert, Finset.mem_singleton] at hq
            rcases hq with rfl | rfl
            · exact hbmem
            · exact hdmem
          have hle := Finset.card_le_card hsub
          simpa [hne, Ne.symm hne] using hle
        have hone := edgeIndexedService_localLaw H R Cedge hservice u a
        omega
      exact hdb
    · rintro rfl
      exact ⟨hb.1, hb.2⟩
  · rintro ⟨b, hb⟩
    have hbmem : b ∈ incidentServiceNeighborFinset R Cedge u a := by
      rw [hb]
      simp
    exact ⟨b, (Finset.mem_filter.mp hbmem).1 |> (Cedge.mem_neighborFinset a b).mp,
      (Finset.mem_filter.mp hbmem).2⟩

/-- Distinct neighbors of one service edge have disjoint endpoint pairs. -/
theorem edgeIndexedService_neighborEdges_pairwiseDisjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (a b d : R.edgeFinset)
    (hb : Cedge.Adj a b) (hd : Cedge.Adj a d) (hbd : b ≠ d) :
    Disjoint b.1.toFinset d.1.toFinset := by
  classical
  rw [Finset.disjoint_left]
  intro u hub hud
  have hbmem : b ∈ incidentServiceNeighborFinset R Cedge u a := by
    exact Finset.mem_filter.mpr ⟨(Cedge.mem_neighborFinset a b).mpr hb, hub⟩
  have hdmem : d ∈ incidentServiceNeighborFinset R Cedge u a := by
    exact Finset.mem_filter.mpr ⟨(Cedge.mem_neighborFinset a d).mpr hd, hud⟩
  have htwo : 2 ≤ (incidentServiceNeighborFinset R Cedge u a).card := by
    have hsub : ({b, d} : Finset R.edgeFinset) ⊆
        incidentServiceNeighborFinset R Cedge u a := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact hbmem
      · exact hdmem
    have hle := Finset.card_le_card hsub
    simpa [hbd, Ne.symm hbd] using hle
  have hone := edgeIndexedService_localLaw H R Cedge hservice u a
  omega

end

end Erdos85

#print axioms Erdos85.edgeIndexedService_neighborEdges_pairwiseDisjoint
