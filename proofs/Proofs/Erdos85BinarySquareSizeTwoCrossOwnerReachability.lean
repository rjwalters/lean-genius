import Proofs.Erdos85BinarySquareSizeTwoOwnerEdgeSubdivision

/-! # Cross-block and owner-factor reachability coincide -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem restrictedOwner_adj_of_cross_twoPath
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    {x y : source.supp} {z : target.supp} (hxy : x ≠ y)
    (hxz : (componentCrossBipartiteGraph G source target).Adj
      (Sum.inl x) (Sum.inr z))
    (hzy : (componentCrossBipartiteGraph G source target).Adj
      (Sum.inr z) (Sum.inl y)) :
    (restrictedComponentOwnerGraph G source target).Adj x y := by
  apply (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
    G source target x y).mpr
  refine ⟨hxy, ⟨z, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxz⟩
  · have hyz : G.Adj y.1 z.1 := hzy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyz⟩

private theorem cross_reflTransGen_from_left_compress
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (x : source.supp) {v : source.supp ⊕ target.supp}
    (h : Relation.ReflTransGen
      (componentCrossBipartiteGraph G source target).Adj (Sum.inl x) v) :
    match v with
    | Sum.inl y => Relation.ReflTransGen
        (restrictedComponentOwnerGraph G source target).Adj x y
    | Sum.inr z => ∃ y : source.supp,
        Relation.ReflTransGen
            (restrictedComponentOwnerGraph G source target).Adj x y ∧
          (componentCrossBipartiteGraph G source target).Adj
            (Sum.inl y) (Sum.inr z) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
    cases b with
    | inl y =>
      cases c with
      | inl w => simp [componentCrossBipartiteGraph] at hbc
      | inr z => exact ⟨y, ih, hbc⟩
    | inr z =>
      cases c with
      | inl y =>
        obtain ⟨w, hw, hwz⟩ := ih
        by_cases hwy : w = y
        · subst y
          exact hw
        · exact hw.tail
            (restrictedOwner_adj_of_cross_twoPath
              G source target hwy hwz hbc)
      | inr w => simp [componentCrossBipartiteGraph] at hbc

/-- Reachability in the restricted owner factor is exactly reachability
between the corresponding source-side vertices in the cross-block graph. -/
theorem restrictedOwner_reachable_iff_cross_inl_reachable
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (x y : source.supp) :
    (restrictedComponentOwnerGraph G source target).Reachable x y ↔
      (componentCrossBipartiteGraph G source target).Reachable
        (Sum.inl x) (Sum.inl y) := by
  rw [reachable_iff_reflTransGen, reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
      obtain ⟨_hne, z, hz, _hunique⟩ :=
        (restrictedOwner_adj_iff_existsUnique_cross_twoPath
          G hfree source target _ _).mp hbc
      exact (ih.tail hz.1).tail hz.2
  · exact cross_reflTransGen_from_left_compress G source target x

/-- Equivalently, source-side vertices have the same connected-component
partition in the owner factor and in the cross-block graph. -/
theorem restrictedOwner_connectedComponentMk_eq_iff_cross_inl
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (x y : source.supp) :
    (restrictedComponentOwnerGraph G source target).connectedComponentMk x =
        (restrictedComponentOwnerGraph G source target).connectedComponentMk y ↔
      (componentCrossBipartiteGraph G source target).connectedComponentMk
          (Sum.inl x) =
        (componentCrossBipartiteGraph G source target).connectedComponentMk
          (Sum.inl y) := by
  simp only [ConnectedComponent.eq]
  exact restrictedOwner_reachable_iff_cross_inl_reachable
    G hfree source target x y

end

end Erdos85
