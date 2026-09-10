import Proofs.Erdos85OrderFortyNineThreeHighTripleSingletonCoordinates

namespace Erdos85
open SimpleGraph

def encodedTripleBlockCap (blocks : Fin 3 → Finset (Fin 24)) (S : Finset (Fin 24)) : Bool :=
  decide (∀ k, (S ∩ blocks k).card ≤ 1)

theorem threeHigh_triple_coordinate_special_block_cap
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
    (z x s : Fin 49) (hxz : ¬ G.Adj x z)
    (hs : s ∈ threeHighTripleSpecialSet G z) :
    (threeHighSingletonCoordinates G e x ∩ threeHighSingletonCoordinates G e s).card ≤ 1 := by
  have hxs : x ≠ s := by
    intro he
    subst x
    exact hxz (((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hs).1).symm)
  exact threeHigh_triple_singleton_coordinates_inter_le_one G hfree e x s hxs

theorem threeHigh_triple_coordinate_block_gate
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
    (z x : Fin 49) (hxz : ¬ G.Adj x z)
    (roots : Fin 3 → Fin 49) (hroots : ∀ k, roots k ∈ threeHighTripleSpecialSet G z)
    (blocks : Fin 3 → Finset (Fin 24))
    (hblocks : ∀ k, blocks k = threeHighSingletonCoordinates G e (roots k)) :
    encodedTripleBlockCap blocks (threeHighSingletonCoordinates G e x) = true := by
  apply decide_eq_true_iff.mpr
  intro k
  rw [hblocks k]
  exact threeHigh_triple_coordinate_special_block_cap G hfree e z x (roots k) hxz (hroots k)

end Erdos85
#print axioms Erdos85.threeHigh_triple_coordinate_special_block_cap
#print axioms Erdos85.threeHigh_triple_coordinate_block_gate
