import Proofs.Erdos85OrderFortyNineThreeHighTripleOrdinaryColorNeighbor
import Proofs.Erdos85OrderFortyNineThreeHighTripleBlockCapacity

/-! Actual singleton neighborhoods satisfy the local eligibility gates used by
triple-profile resolution enumeration. -/
namespace Erdos85
open SimpleGraph
noncomputable section

 theorem threeHigh_triple_ordinary_special_block_inter_le_one
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (z x s : Fin 49)
    (hxz : ¬ G.Adj x z) (hs : s ∈ threeHighTripleSpecialSet G z) :
    ((G.neighborFinset x ∩ threeHighTripleEmptySet G) ∩
      (G.neighborFinset s ∩ threeHighTripleEmptySet G)).card ≤ 1 := by
  have hxs : x ≠ s := by
    intro he
    subst x
    exact hxz (((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hs).1).symm)
  have hc := (not_containsC4_iff_forall_common_le_one G).mp hfree x s hxs
  apply (Finset.card_le_card ?_).trans hc
  intro v hv
  exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hv).1).1,
    (Finset.mem_inter.mp (Finset.mem_inter.mp hv).2).1⟩

theorem threeHigh_triple_singleton_pair_no_common_empty_neighbor
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (x : Fin 49)
    (hx : (orderFortyNineHighSupport G x).card = 1)
    {a b : Fin 49} (ha : a ∈ G.neighborFinset x ∩ threeHighTripleEmptySet G)
    (hb : b ∈ G.neighborFinset x ∩ threeHighTripleEmptySet G) (hab : a ≠ b) :
    ∀ w ∈ threeHighTripleEmptySet G, ¬ (G.Adj a w ∧ G.Adj b w) := by
  intro w hw hawb
  have hw0 := (Finset.mem_filter.mp hw).2
  have hxw : x ≠ w := by intro he; subst x; omega
  have hc := (not_containsC4_iff_forall_common_le_one G).mp hfree a b hab
  have hxc : x ∈ G.neighborFinset a ∩ G.neighborFinset b :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr
      (((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp ha).1).symm),
      (G.mem_neighborFinset _ _).mpr
      (((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hb).1).symm)⟩
  have hwc : w ∈ G.neighborFinset a ∩ G.neighborFinset b :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hawb.1,
      (G.mem_neighborFinset _ _).mpr hawb.2⟩
  exact hxw (Finset.card_le_one.mp hc x hxc w hwc)

theorem threeHigh_triple_distinct_singleton_blocks_inter_le_one
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (x y : Fin 49) (hxy : x ≠ y) :
    ((G.neighborFinset x ∩ threeHighTripleEmptySet G) ∩
      (G.neighborFinset y ∩ threeHighTripleEmptySet G)).card ≤ 1 := by
  have hc := (not_containsC4_iff_forall_common_le_one G).mp hfree x y hxy
  apply (Finset.card_le_card ?_).trans hc
  intro v hv
  exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hv).1).1,
    (Finset.mem_inter.mp (Finset.mem_inter.mp hv).2).1⟩

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_ordinary_special_block_inter_le_one
#print axioms Erdos85.threeHigh_triple_singleton_pair_no_common_empty_neighbor
#print axioms Erdos85.threeHigh_triple_distinct_singleton_blocks_inter_le_one
