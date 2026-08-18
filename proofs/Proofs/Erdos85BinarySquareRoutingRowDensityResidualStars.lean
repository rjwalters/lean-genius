import Proofs.Erdos85BinarySquareSeparatedForkRowDensity
import Proofs.Erdos85BinarySquareRoutingRowStarDecomposition

/-! # The residual of a two-center routing fragment is canonical

A two-center density witness does not merely give a cardinal lower bound.
After deleting its two displayed stars, the rest of the routing row is exactly
the disjoint union of the stars of the unused owner-centers at the same root.
This is the q-generic algebraic normal form behind the size-three and
size-four specializations.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every two-center routing-row density witness has an exact residual-star
decomposition over the unused owner-centers at its root. -/
theorem twoCenterRoutingRowDensity_residual_eq_biUnion_unusedCenters
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (source target owner :
      (secondOrderDefectGraph G).ConnectedComponent)
    (hst : source ≠ target) (x : source.supp)
    (h : HasTwoCenterRoutingRowDensity
      G hfree m source target owner hst x) :
    ∃ u₁ u₂ : owner.supp, u₁ ≠ u₂ ∧
      let C := componentCrossNeighborFinset G owner x
      let S₁ := componentCrossNeighborFinset G target u₁
      let S₂ := componentCrossNeighborFinset G target u₂
      let R := (Finset.univ : Finset target.supp).filter fun y =>
        owner = crossIntermediateComponent G hfree hst x y
      R \ (S₁ ∪ S₂) =
        (C \ {u₁, u₂}).biUnion fun u =>
          componentCrossNeighborFinset G target u := by
  classical
  rcases h with ⟨u₁, u₂, hne, hx₁, hx₂, _hdis, _hcard,
    _hsub, _hrowCard⟩
  refine ⟨u₁, u₂, hne, ?_⟩
  let C := componentCrossNeighborFinset G owner x
  let S₁ := componentCrossNeighborFinset G target u₁
  let S₂ := componentCrossNeighborFinset G target u₂
  let R := (Finset.univ : Finset target.supp).filter fun y =>
    owner = crossIntermediateComponent G hfree hst x y
  have hu₁C : u₁ ∈ C := by
    change u₁ ∈ componentCrossNeighborFinset G owner x
    rw [componentCrossNeighborFinset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hx₁⟩
  have hu₂C : u₂ ∈ C := by
    change u₂ ∈ componentCrossNeighborFinset G owner x
    rw [componentCrossNeighborFinset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hx₂⟩
  have hdecomp : R = C.biUnion fun u =>
      componentCrossNeighborFinset G target u := by
    dsimp [R, C]
    exact routingRow_eq_biUnion_componentCrossNeighborFinset
      G hfree hst owner x
  ext w
  constructor
  · intro hw
    have hwR : w ∈ R := (Finset.mem_sdiff.mp hw).1
    obtain ⟨u, huC, hwu⟩ := Finset.mem_biUnion.mp
      (hdecomp ▸ hwR)
    have huPair : u ∉ ({u₁, u₂} : Finset owner.supp) := by
      intro hu
      have hwNot : w ∉ S₁ ∪ S₂ := (Finset.mem_sdiff.mp hw).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hwNot (Finset.mem_union_left S₂ hwu)
      · exact hwNot (Finset.mem_union_right S₁ hwu)
    apply Finset.mem_biUnion.mpr
    exact ⟨u, Finset.mem_sdiff.mpr ⟨huC, huPair⟩, hwu⟩
  · intro hw
    obtain ⟨u, huUnused, hwu⟩ := Finset.mem_biUnion.mp hw
    have huC := (Finset.mem_sdiff.mp huUnused).1
    have huPair := (Finset.mem_sdiff.mp huUnused).2
    have huNe₁ : u ≠ u₁ := by
      intro heq
      apply huPair
      simp [heq]
    have huNe₂ : u ≠ u₂ := by
      intro heq
      apply huPair
      simp [heq]
    have hwR : w ∈ R := by
      rw [hdecomp]
      exact Finset.mem_biUnion.mpr ⟨u, huC, hwu⟩
    have hdis₁ := routingRow_starRows_pairwise_disjoint
      G hfree hst x huC hu₁C huNe₁
    have hdis₂ := routingRow_starRows_pairwise_disjoint
      G hfree hst x huC hu₂C huNe₂
    have hwNot₁ : w ∉ S₁ := by
      intro hw₁
      exact Finset.disjoint_left.mp hdis₁ hwu hw₁
    have hwNot₂ : w ∉ S₂ := by
      intro hw₂
      exact Finset.disjoint_left.mp hdis₂ hwu hw₂
    exact Finset.mem_sdiff.mpr ⟨hwR, by simpa [S₁, S₂] using ⟨hwNot₁, hwNot₂⟩⟩

end

end Erdos85

#print axioms Erdos85.twoCenterRoutingRowDensity_residual_eq_biUnion_unusedCenters
