import Proofs.Erdos85MuThreeKSymmetryClassificationExhaustive
import Proofs.Erdos85MuThreeMixedGridCode

/-! # From factor-cycle compatibility to sector constancy -/

namespace Erdos85

theorem RelationFactorCycleCompatible.edge_status_eq_of_reachable
    {X Y : Type*} (H K : X → Y → Prop)
    (hcycle : RelationFactorCycleCompatible H K)
    {x x' : X} {y y' : Y}
    (hxy : H x y) (hx'y' : H x' y')
    (hreach : (relationBipartiteGraph H).Reachable
      (Sum.inl x) (Sum.inl x')) :
    (K x y ↔ K x' y') := by
  let c := (relationBipartiteGraph H).connectedComponentMk (Sum.inl x)
  have hxc : Sum.inl x ∈ c.supp := by
    change (relationBipartiteGraph H).connectedComponentMk (Sum.inl x) = c
    rfl
  have hx'c : Sum.inl x' ∈ c.supp := by
    change (relationBipartiteGraph H).connectedComponentMk (Sum.inl x') = c
    exact (SimpleGraph.ConnectedComponent.sound hreach).symm
  rcases hcycle c with hall | hnone
  · exact ⟨fun _ => hall x' y' hx'y' hx'c,
      fun _ => hall x y hxy hxc⟩
  · exact ⟨fun hk => absurd hk (hnone x y hxy hxc),
      fun hk => absurd hk (hnone x' y' hx'y' hx'c)⟩

end Erdos85

#print axioms Erdos85.RelationFactorCycleCompatible.edge_status_eq_of_reachable
