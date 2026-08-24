import Proofs.Erdos85PureEndpointFinalLayerPrivateMatching

/-!
# Canonical private points at the pure endpoint

The endpoint private matching has `q` distinct values, while the exact
replication census has exactly `q` replication-one shore points.  Hence the
matching exhausts that class and identifies it bijectively with the full
centers.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Full centers biject with all replication-one shore points. -/
theorem c4Free_binarySquare_pureEndpoint_privatePoint_bijection
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    ∃ p : {i // i ∈ fullLineCenters G S q} → V,
      Function.Injective p ∧
      (∀ i, p i ∈ S ∧ G.Adj i.1 (p i) ∧
        G.neighborFinset (p i) ∩ fullLineCenters G S q = {i.1}) ∧
      ∀ z, z ∈ S →
        (G.neighborFinset z ∩ fullLineCenters G S q).card = 1 →
        ∃ i, p i = z := by
  classical
  let F := fullLineCenters G S q
  let R₁ := S.filter fun z => (G.neighborFinset z ∩ F).card = 1
  obtain ⟨_hsupport, hR₁card, _hR₂card, _hDindependent, _hcap,
      p, hpInj, hp⟩ :=
    c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hpS : ∀ i, p i ∈ S := by
    intro i
    have hiFull := (mem_fullLineCenters G S q i.1).mp i.2
    have hiNeighbors : G.neighborFinset i.1 ∩ S = G.neighborFinset i.1 := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      rw [hiFull, G.card_neighborFinset_eq_degree, hreg]
    have hpN : p i ∈ G.neighborFinset i.1 := by
      simpa [SimpleGraph.mem_neighborFinset] using (hp i).1
    have : p i ∈ G.neighborFinset i.1 ∩ S := by
      rw [hiNeighbors]
      exact hpN
    exact (Finset.mem_inter.mp this).2
  have hRangeSub : Finset.univ.image p ⊆ R₁ := by
    intro z hz
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hz
    apply Finset.mem_filter.mpr
    rw [(hp i).2]
    exact ⟨hpS i, by simp⟩
  have hindexCard : Fintype.card {i // i ∈ F} = q := by
    change Fintype.card ↥F = q
    rw [Fintype.card_coe]
    simpa [F] using hCcard
  have hRangeCard : (Finset.univ.image p).card = q := by
    rw [Finset.card_image_of_injective _ hpInj, Finset.card_univ, hindexCard]
  have hR₁card' : R₁.card = q := by simpa [R₁, F] using hR₁card
  have hRangeEq : Finset.univ.image p = R₁ := by
    apply Finset.eq_of_subset_of_card_le hRangeSub
    rw [hRangeCard, hR₁card']
  refine ⟨p, hpInj, ?_, ?_⟩
  · intro i
    exact ⟨hpS i, (hp i).1, (hp i).2⟩
  · intro z hzS hzOne
    have hzR₁ : z ∈ R₁ := Finset.mem_filter.mpr ⟨hzS, by
      simpa [F] using hzOne⟩
    rw [← hRangeEq] at hzR₁
    obtain ⟨i, _hi, hiEq⟩ := Finset.mem_image.mp hzR₁
    exact ⟨i, hiEq⟩

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_privatePoint_bijection
