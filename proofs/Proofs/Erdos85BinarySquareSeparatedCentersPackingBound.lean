import Proofs.Erdos85BinarySquareSeparatedCentersDisjointSelectors

/-! # Packing bound for separated ambient centers -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A family of centers sharing one neighbor outside a size-sixteen target
component has pairwise-disjoint target selectors.  If every selector has two
points, at most eight centers can occur. -/
theorem card_centers_le_eight_of_sharedNeighbor_twoPointSelectors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : SimpleGraph V) [DecidableEq D.ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (target : D.ConnectedComponent)
    (U : Finset V) (y : V)
    (hy : D.connectedComponentMk y ≠ target)
    (hshared : ∀ u ∈ U, G.Adj u y)
    (hselector : ∀ u ∈ U,
      (componentNeighborFinset G D target u).card = 2)
    (htarget : target.supp.ncard = 16) :
    U.card ≤ 8 := by
  classical
  let F : V → Finset V := fun u => componentNeighborFinset G D target u
  have hpair : (U : Set V).PairwiseDisjoint F := by
    intro u hu v hv huv
    exact componentNeighborFinset_disjoint_of_distinct_sharedNeighbor_outside
      G D hfree target huv (hshared u hu) (hshared v hv) hy
  have hsub : U.biUnion F ⊆ target.supp.toFinset := by
    intro z hz
    obtain ⟨u, hu, hzu⟩ := Finset.mem_biUnion.mp hz
    have hzData := Finset.mem_filter.mp hzu
    exact Set.mem_toFinset.mpr
      ((ConnectedComponent.mem_supp_iff target z).mpr hzData.2)
  have hunionCard : (U.biUnion F).card = 2 * U.card := by
    rw [Finset.card_biUnion hpair]
    calc
      (∑ u ∈ U, (F u).card) = ∑ _u ∈ U, 2 := by
        apply Finset.sum_congr rfl
        intro u hu
        exact hselector u hu
      _ = 2 * U.card := by simp [Nat.mul_comm]
  have htargetCard : target.supp.toFinset.card = 16 := by
    rw [← Set.ncard_eq_toFinset_card']
    exact htarget
  have hle := Finset.card_le_card hsub
  rw [hunionCard, htargetCard] at hle
  omega

end

end Erdos85
