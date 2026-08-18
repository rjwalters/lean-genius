import Proofs.Erdos85BinarySquareMixedOwnerNoRainbowFork

/-! # Ambient common-neighbor separation in the forced owner fork -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem exists_commonNeighbor_in_owner_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : SimpleGraph V) [DecidableEq D.ConnectedComponent]
    (owner : D.ConnectedComponent) {s t : V}
    (h : (componentOwnerGraph G D owner).Adj s t) :
    ∃ u : V, G.Adj s u ∧ G.Adj t u ∧ D.connectedComponentMk u = owner := by
  rw [componentOwnerGraph_adj] at h
  obtain ⟨_hst, u, hu⟩ := h
  have hu' := Finset.mem_inter.mp hu
  have hus := Finset.mem_filter.mp hu'.1
  have hut := Finset.mem_filter.mp hu'.2
  exact ⟨u, (G.mem_neighborFinset s u).mp hus.1,
    (G.mem_neighborFinset t u).mp hut.1, hus.2⟩

/-- Two distinct closing vertices in an owner-`b`/owner-`c` fork cannot use
the same ambient common neighbor on both sides.  Otherwise the two closing
vertices would have two distinct common neighbors, producing a four-cycle. -/
theorem ownerFork_commonNeighbor_separation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : SimpleGraph V) [DecidableEq D.ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (b c : D.ConnectedComponent) (hbc : b ≠ c)
    {x y z₁ z₂ : V} (hz : z₁ ≠ z₂)
    (hby₁ : (componentOwnerGraph G D b).Adj y z₁)
    (hby₂ : (componentOwnerGraph G D b).Adj y z₂)
    (hcx₁ : (componentOwnerGraph G D c).Adj z₁ x)
    (hcx₂ : (componentOwnerGraph G D c).Adj z₂ x) :
    ∃ ub₁ ub₂ uc₁ uc₂ : V,
      G.Adj y ub₁ ∧ G.Adj z₁ ub₁ ∧
      G.Adj y ub₂ ∧ G.Adj z₂ ub₂ ∧
      G.Adj z₁ uc₁ ∧ G.Adj x uc₁ ∧
      G.Adj z₂ uc₂ ∧ G.Adj x uc₂ ∧
      D.connectedComponentMk ub₁ = b ∧
      D.connectedComponentMk ub₂ = b ∧
      D.connectedComponentMk uc₁ = c ∧
      D.connectedComponentMk uc₂ = c ∧
      (ub₁ ≠ ub₂ ∨ uc₁ ≠ uc₂) := by
  classical
  obtain ⟨ub₁, hyb₁, hz₁b₁, hub₁⟩ :=
    exists_commonNeighbor_in_owner_of_adj G D b hby₁
  obtain ⟨ub₂, hyb₂, hz₂b₂, hub₂⟩ :=
    exists_commonNeighbor_in_owner_of_adj G D b hby₂
  obtain ⟨uc₁, hz₁c₁, hxc₁, huc₁⟩ :=
    exists_commonNeighbor_in_owner_of_adj G D c hcx₁
  obtain ⟨uc₂, hz₂c₂, hxc₂, huc₂⟩ :=
    exists_commonNeighbor_in_owner_of_adj G D c hcx₂
  refine ⟨ub₁, ub₂, uc₁, uc₂, hyb₁, hz₁b₁, hyb₂, hz₂b₂,
    hz₁c₁, hxc₁, hz₂c₂, hxc₂, hub₁, hub₂, huc₁, huc₂, ?_⟩
  by_contra hsame
  push Not at hsame
  have hz₂b₁ : G.Adj z₂ ub₁ := hsame.1 ▸ hz₂b₂
  have hz₂c₁ : G.Adj z₂ uc₁ := hsame.2 ▸ hz₂c₂
  have hubc : ub₁ ≠ uc₁ := by
    intro h
    apply hbc
    calc
      b = D.connectedComponentMk ub₁ := hub₁.symm
      _ = D.connectedComponentMk uc₁ := congrArg D.connectedComponentMk h
      _ = c := huc₁
  have hubMem : ub₁ ∈ G.neighborFinset z₁ ∩ G.neighborFinset z₂ := by
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z₁ ub₁).mpr hz₁b₁,
        (G.mem_neighborFinset z₂ ub₁).mpr hz₂b₁⟩
  have hucMem : uc₁ ∈ G.neighborFinset z₁ ∩ G.neighborFinset z₂ := by
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z₁ uc₁).mpr hz₁c₁,
        (G.mem_neighborFinset z₂ uc₁).mpr hz₂c₁⟩
  have hle := card_inter_neighborFinset_le_one hfree hz
  exact hubc (Finset.card_le_one.mp hle ub₁ hubMem uc₁ hucMem)

end

end Erdos85
