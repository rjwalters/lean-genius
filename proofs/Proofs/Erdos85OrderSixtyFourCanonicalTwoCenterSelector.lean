import Proofs.Erdos85OrderSixtyFourDefectComponentEquitable
import Proofs.Erdos85BinarySquareSizeTwoCrossIndexedBlocks

/-! # Canonical normalization of two ambient centers -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Two distinct target-component neighbors exhaust a cross-selector known
to have cardinality two.  This is the normalization needed to retain the
named fork centers after a routing-row saturation is recognized as the
generic star decomposition. -/
theorem componentCrossNeighborFinset_eq_pair_of_card_two_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    {source target : (secondOrderDefectGraph G).ConnectedComponent}
    (x : source.supp) (u v : target.supp)
    (huv : u ≠ v)
    (hxu : G.Adj x.1 u.1) (hxv : G.Adj x.1 v.1)
    (hcard : (componentCrossNeighborFinset G target x).card = 2) :
    componentCrossNeighborFinset G target x = {u, v} := by
  classical
  have hu : u ∈ componentCrossNeighborFinset G target x := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxu⟩
  have hv : v ∈ componentCrossNeighborFinset G target x := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxv⟩
  have hsub : ({u, v} : Finset target.supp) ⊆
      componentCrossNeighborFinset G target x := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hu, hv⟩
  symm
  apply Finset.eq_of_subset_of_card_le hsub
  simp [huv, hcard]

/-- In the regular order-sixty-four all-sixteen branch, the cardinality-two
hypothesis is automatic from the equitable component-neighbor identity. -/
theorem orderSixtyFour_componentCrossNeighborFinset_eq_pair_of_adj
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ z, G.degree z = 8)
    {source target : (secondOrderDefectGraph G).ConnectedComponent}
    (htarget : target.supp.ncard = 16)
    (x : source.supp) (u v : target.supp)
    (huv : u ≠ v)
    (hxu : G.Adj x.1 u.1) (hxv : G.Adj x.1 v.1) :
    componentCrossNeighborFinset G target x = {u, v} := by
  apply componentCrossNeighborFinset_eq_pair_of_card_two_of_adj
    G x u v huv hxu hxv
  rw [card_componentCrossNeighborFinset_eq_componentNeighborFinset]
  have hmul := orderSixtyFour_eight_mul_componentNeighborFinset_card
    G hfree (fun z => by rw [hreg z])
      (fun {_z _w} _hzw => Or.inl (hreg _z)) target x.1
  rw [htarget] at hmul
  omega

end

end Erdos85
