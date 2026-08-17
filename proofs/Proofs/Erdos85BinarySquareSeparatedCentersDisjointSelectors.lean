import Proofs.Erdos85BinarySquareMixedOwnerNoRainbowAmbientExhaustion

/-! # Separated common-neighbor centers have disjoint remote selectors -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Distinct vertices which already share a common neighbor outside a target
defect component cannot share another neighbor inside that component. -/
theorem componentNeighborFinset_disjoint_of_distinct_sharedNeighbor_outside
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : SimpleGraph V) [DecidableEq D.ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (target : D.ConnectedComponent) {u₁ u₂ x : V}
    (hu : u₁ ≠ u₂) (h₁ : G.Adj u₁ x) (h₂ : G.Adj u₂ x)
    (hx : D.connectedComponentMk x ≠ target) :
    Disjoint (componentNeighborFinset G D target u₁)
      (componentNeighborFinset G D target u₂) := by
  classical
  rw [Finset.disjoint_left]
  intro v hv₁ hv₂
  have hv₁' := Finset.mem_filter.mp hv₁
  have hv₂' := Finset.mem_filter.mp hv₂
  have hv₁adj : G.Adj u₁ v := (G.mem_neighborFinset u₁ v).mp hv₁'.1
  have hv₂adj : G.Adj u₂ v := (G.mem_neighborFinset u₂ v).mp hv₂'.1
  have hxmem : x ∈ G.neighborFinset u₁ ∩ G.neighborFinset u₂ := by
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset u₁ x).mpr h₁,
        (G.mem_neighborFinset u₂ x).mpr h₂⟩
  have hvmem : v ∈ G.neighborFinset u₁ ∩ G.neighborFinset u₂ := by
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset u₁ v).mpr hv₁adj,
        (G.mem_neighborFinset u₂ v).mpr hv₂adj⟩
  have hle := card_inter_neighborFinset_le_one hfree hu
  have hxv : x = v := Finset.card_le_one.mp hle x hxmem v hvmem
  apply hx
  rw [hxv]
  exact hv₁'.2

end

end Erdos85
