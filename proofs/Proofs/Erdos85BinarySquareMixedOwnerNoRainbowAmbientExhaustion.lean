import Proofs.Erdos85BinarySquareMixedOwnerNoRainbowAmbientFork

/-! # Selector exhaustion forced by a separated ambient owner fork -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- When the relevant component selectors have size two, ambient separation
on either side of an owner fork makes the two corresponding centers exhaust
that entire component selector. -/
theorem ownerFork_commonNeighbor_selector_exhaustion
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : SimpleGraph V) [DecidableEq D.ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (b c : D.ConnectedComponent) (hbc : b ≠ c)
    {x y z₁ z₂ : V} (hz : z₁ ≠ z₂)
    (hby₁ : (componentOwnerGraph G D b).Adj y z₁)
    (hby₂ : (componentOwnerGraph G D b).Adj y z₂)
    (hcx₁ : (componentOwnerGraph G D c).Adj z₁ x)
    (hcx₂ : (componentOwnerGraph G D c).Adj z₂ x)
    (hbcard : (componentNeighborFinset G D b y).card = 2)
    (hccard : (componentNeighborFinset G D c x).card = 2) :
    ∃ ub₁ ub₂ uc₁ uc₂ : V,
      G.Adj y ub₁ ∧ G.Adj z₁ ub₁ ∧
      G.Adj y ub₂ ∧ G.Adj z₂ ub₂ ∧
      G.Adj z₁ uc₁ ∧ G.Adj x uc₁ ∧
      G.Adj z₂ uc₂ ∧ G.Adj x uc₂ ∧
      D.connectedComponentMk ub₁ = b ∧
      D.connectedComponentMk ub₂ = b ∧
      D.connectedComponentMk uc₁ = c ∧
      D.connectedComponentMk uc₂ = c ∧
      ((ub₁ ≠ ub₂ ∧ componentNeighborFinset G D b y = {ub₁, ub₂}) ∨
        (uc₁ ≠ uc₂ ∧ componentNeighborFinset G D c x = {uc₁, uc₂})) := by
  classical
  obtain ⟨ub₁, ub₂, uc₁, uc₂, hyb₁, hz₁b₁, hyb₂, hz₂b₂,
      hz₁c₁, hxc₁, hz₂c₂, hxc₂, hub₁, hub₂, huc₁, huc₂, hsep⟩ :=
    ownerFork_commonNeighbor_separation G D hfree b c hbc hz
      hby₁ hby₂ hcx₁ hcx₂
  refine ⟨ub₁, ub₂, uc₁, uc₂, hyb₁, hz₁b₁, hyb₂, hz₂b₂,
    hz₁c₁, hxc₁, hz₂c₂, hxc₂, hub₁, hub₂, huc₁, huc₂, ?_⟩
  rcases hsep with hubne | hucne
  · left
    refine ⟨hubne, ?_⟩
    have hub₁mem : ub₁ ∈ componentNeighborFinset G D b y := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset y ub₁).mpr hyb₁, hub₁⟩
    have hub₂mem : ub₂ ∈ componentNeighborFinset G D b y := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset y ub₂).mpr hyb₂, hub₂⟩
    have hsub : {ub₁, ub₂} ⊆ componentNeighborFinset G D b y := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hub₁mem
      · exact hub₂mem
    symm
    apply Finset.eq_of_subset_of_card_le hsub
    simp [hbcard, hubne]
  · right
    refine ⟨hucne, ?_⟩
    have huc₁mem : uc₁ ∈ componentNeighborFinset G D c x := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset x uc₁).mpr hxc₁, huc₁⟩
    have huc₂mem : uc₂ ∈ componentNeighborFinset G D c x := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset x uc₂).mpr hxc₂, huc₂⟩
    have hsub : {uc₁, uc₂} ⊆ componentNeighborFinset G D c x := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact huc₁mem
      · exact huc₂mem
    symm
    apply Finset.eq_of_subset_of_card_le hsub
    simp [hccard, hucne]

end

end Erdos85
