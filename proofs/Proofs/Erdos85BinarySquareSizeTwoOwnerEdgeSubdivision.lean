import Proofs.Erdos85BinarySquareSizeTwoCrossBipartiteComponentBalance

/-! # Owner-factor edges as uniquely subdivided cross paths -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A restricted owner-factor edge is exactly a distinct pair of source
vertices joined by a length-two cross-block path; C4-freeness makes the
intermediate target vertex unique. -/
theorem restrictedOwner_adj_iff_existsUnique_cross_twoPath
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (x y : source.supp) :
    (restrictedComponentOwnerGraph G source target).Adj x y ↔
      x ≠ y ∧ ∃! z : target.supp,
        (componentCrossBipartiteGraph G source target).Adj
            (Sum.inl x) (Sum.inr z) ∧
          (componentCrossBipartiteGraph G source target).Adj
            (Sum.inr z) (Sum.inl y) := by
  constructor
  · intro hxy
    obtain ⟨hxyne, hinter⟩ :=
      (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
        G source target x y).mp hxy
    obtain ⟨z, hz⟩ := hinter
    refine ⟨hxyne, z, ?_, ?_⟩
    · have hz' := Finset.mem_inter.mp hz
      exact ⟨(Finset.mem_filter.mp hz'.1).2,
        (Finset.mem_filter.mp hz'.2).2⟩
    · intro w hw
      have hwmem : w ∈ componentCrossNeighborFinset G target x ∩
          componentCrossNeighborFinset G target y := by
        apply Finset.mem_inter.mpr
        constructor
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw.1⟩
        · have hwy : G.Adj y.1 w.1 := hw.2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwy⟩
      exact (Finset.card_le_one.mp
        (card_crossNeighborFinset_inter_le_one G hfree target x y hxyne)
          z hz w hwmem).symm
  · rintro ⟨hxy, z, hz, _hunique⟩
    apply (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
      G source target x y).mpr
    refine ⟨hxy, ⟨z, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz.1⟩
    · have hyz : G.Adj y.1 z.1 := hz.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyz⟩

/-- The same unique-subdivision statement with source and target reversed. -/
theorem restrictedOwner_reverse_adj_iff_existsUnique_cross_twoPath
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (z w : target.supp) :
    (restrictedComponentOwnerGraph G target source).Adj z w ↔
      z ≠ w ∧ ∃! x : source.supp,
        (componentCrossBipartiteGraph G source target).Adj
            (Sum.inr z) (Sum.inl x) ∧
          (componentCrossBipartiteGraph G source target).Adj
            (Sum.inl x) (Sum.inr w) := by
  simpa [adj_comm] using
    (restrictedOwner_adj_iff_existsUnique_cross_twoPath
      G hfree target source z w)

/-- An owner-factor edge remains inside one connected component of the
cross-block graph after embedding both endpoints on the source side. -/
theorem restrictedOwner_adj_cross_connectedComponentMk_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    {x y : source.supp}
    (hxy : (restrictedComponentOwnerGraph G source target).Adj x y) :
    (componentCrossBipartiteGraph G source target).connectedComponentMk
        (Sum.inl x) =
      (componentCrossBipartiteGraph G source target).connectedComponentMk
        (Sum.inl y) := by
  obtain ⟨_hxy, z, hz, _hunique⟩ :=
    (restrictedOwner_adj_iff_existsUnique_cross_twoPath
      G hfree source target x y).mp hxy
  exact (ConnectedComponent.connectedComponentMk_eq_of_adj hz.1).trans
    (ConnectedComponent.connectedComponentMk_eq_of_adj hz.2)

end

end Erdos85
