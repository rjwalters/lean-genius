import Proofs.Erdos85OrderFortyNineThreeHighTripleJointBlockFamilies
import Proofs.Erdos85ThreeHighPrunedJointResolution

namespace Erdos85
open SimpleGraph
noncomputable section

theorem threeHigh_triple_actual_pruned_joint_search
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj] [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (hmin : ∀ x, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (s : Fin 3 → Fin 49) (hs : ∀ k, s k ∈ threeHighTripleSpecialSet G z)
    (hsinj : Function.Injective s)
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
    (heu : (e 23).val = u)
    (hrow : ∀ k i, (e (threeHighEmptyUIndex ((@finProdFinEquiv 3 5) (k,i)))).val ∈
      G.neighborFinset (s k) ∩ threeHighTripleEmptySet G)
    (B : Fin 24 → Fin 24 → Bool)
    (hB : ∀ i j, decide (G.Adj (e i).val (e j).val) = B i j) :
    threeHighPrunedJointResolutionSearch B threeHighCanonicalResidual threeHighCanonicalRow = true := by
  obtain ⟨F,hF,hblocks,hcompat,hcap⟩ := threeHigh_triple_joint_block_families
    G hfree hmin hHigh hone z hz hu huz s hs hsinj e heu hrow B hB
  exact threeHighPrunedJointResolutionSearch_of_families B _ _ F hF hblocks
    (fun i j _ => hcompat i j) hcap

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_actual_pruned_joint_search
