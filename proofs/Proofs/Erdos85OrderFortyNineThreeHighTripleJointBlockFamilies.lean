import Proofs.Erdos85OrderFortyNineThreeHighTripleJointColorFamilies
import Proofs.Erdos85OrderFortyNineThreeHighTripleBlockFamily

namespace Erdos85
open SimpleGraph
noncomputable section

theorem threeHigh_triple_joint_block_families
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
    ∃ F : Fin 3 → Finset (Finset (Fin 24)),
      (∀ k, F k ∈ threeHighResolutionDomain B (threeHighCanonicalResidual k)) ∧
      (∀ k, ∀ S ∈ F k, encodedTripleBlockCap threeHighCanonicalRow S = true) ∧
      (∀ k l, encodedFamilyCompatibility B (F k) (F l) = true) ∧
      (∀ k l, k ≠ l → encodedFamilyIntersectionCap (F k) (F l) = true) := by
  classical
  obtain ⟨h,F,hactual,hres,hcompat,hinter⟩ := threeHigh_triple_joint_color_families
    G hfree hmin hHigh hone z hz hu huz s hs hsinj e heu hrow B hB
  refine ⟨F,hres,?_,hcompat,hinter⟩
  intro k
  obtain ⟨hh,hsh,hF⟩ := hactual k
  have hsz : G.Adj (s k) z :=
    ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp (hs k)).1).symm
  have hblocks : ∀ l, threeHighCanonicalRow l = threeHighSingletonCoordinates G e (s l) := by
    intro l
    exact (threeHigh_triple_special_coordinates_eq_row G hfree hmin hHigh hone z hz
      (hs l) e l (hrow l)).symm
  have hf := threeHigh_triple_actual_block_family G hfree hmin hHigh hone
    z (h k) (s k) hz hh ((G.mem_neighborFinset _ _).mpr hsh.symm) hsz e B hB
    s hs threeHighCanonicalRow hblocks
  rw [hF]
  exact hf.2

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_joint_block_families
