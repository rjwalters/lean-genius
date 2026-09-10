import Proofs.Erdos85OrderFortyNineThreeHighTripleCanonicalColorResiduals
import Proofs.Erdos85OrderFortyNineThreeHighTripleSpecialColors
import Proofs.Erdos85OrderFortyNineThreeHighTripleResolution

namespace Erdos85
open SimpleGraph
noncomputable section

def threeHighCanonicalResidual (k : Fin 3) : Finset (Fin 24) :=
  Finset.univ \ ({23} ∪ threeHighCanonicalRow k)

theorem threeHigh_triple_canonical_resolution
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj] [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (hmin : ∀ x, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    {s : Fin 49} (hs : s ∈ threeHighTripleSpecialSet G z)
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
    (heu : (e 23).val = u) (k : Fin 3)
    (hrow : ∀ i, (e (threeHighEmptyUIndex ((@finProdFinEquiv 3 5) (k,i)))).val ∈
      G.neighborFinset s ∩ threeHighTripleEmptySet G)
    (B : Fin 24 → Fin 24 → Bool)
    (hB : ∀ i j, decide (G.Adj (e i).val (e j).val) = B i j) :
    ∃ h ∈ orderFortyNineHighVertices G, G.Adj s h ∧
      ((G.neighborFinset h \ {z,s}).image (threeHighSingletonCoordinates G e)) ∈
        threeHighResolutionDomain B (threeHighCanonicalResidual k) := by
  classical
  obtain ⟨colors,hcolors⟩ := threeHigh_triple_special_color_equiv G hfree hmin hHigh z hz
  let h := colors ⟨s,hs⟩
  have hsh : G.Adj s h.val := (hcolors ⟨s,hs⟩ h).mpr rfl
  have hsz : G.Adj s z := ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hs).1).symm
  have hr := threeHigh_triple_coordinate_resolution_mem G hfree hmin hHigh hone z h.val s hz
    h.property ((G.mem_neighborFinset _ _).mpr hsh.symm) hsz e B hB
  have hcz := threeHigh_triple_root_coordinates_eq_singleton G hfree hmin hHigh hone z hz hu huz e heu
  have hcs := threeHigh_triple_special_coordinates_eq_row G hfree hmin hHigh hone z hz hs e k hrow
  refine ⟨h.val,h.property,hsh,?_⟩
  simpa only [hcz,hcs,threeHighCanonicalResidual] using hr

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_canonical_resolution
