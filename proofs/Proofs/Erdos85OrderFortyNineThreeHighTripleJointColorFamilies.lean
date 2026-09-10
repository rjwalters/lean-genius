import Proofs.Erdos85OrderFortyNineThreeHighTripleCanonicalResolution
import Proofs.Erdos85OrderFortyNineThreeHighTripleColorFamilyIntersection

namespace Erdos85
open SimpleGraph
noncomputable section

/-- The same three actual color families satisfy all canonical resolution and
cross-color compatibility conditions simultaneously. -/
theorem threeHigh_triple_joint_color_families
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
    ∃ (h : Fin 3 → Fin 49) (F : Fin 3 → Finset (Finset (Fin 24))),
      (∀ k, h k ∈ orderFortyNineHighVertices G ∧ G.Adj (s k) (h k) ∧
        F k = (G.neighborFinset (h k) \ {z,s k}).image (threeHighSingletonCoordinates G e)) ∧
      (∀ k, F k ∈ threeHighResolutionDomain B (threeHighCanonicalResidual k)) ∧
      (∀ k l, encodedFamilyCompatibility B (F k) (F l) = true) ∧
      (∀ k l, k ≠ l → encodedFamilyIntersectionCap (F k) (F l) = true) := by
  classical
  obtain ⟨colors,hcolors⟩ := threeHigh_triple_special_color_equiv G hfree hmin hHigh z hz
  let h : Fin 3 → Fin 49 := fun k => (colors ⟨s k,hs k⟩).val
  have hh (k) : h k ∈ orderFortyNineHighVertices G := (colors ⟨s k,hs k⟩).property
  have hsh (k) : G.Adj (s k) (h k) := (hcolors ⟨s k,hs k⟩ (colors ⟨s k,hs k⟩)).mpr rfl
  have hsN (k) : s k ∈ G.neighborFinset (h k) := (G.mem_neighborFinset _ _).mpr (hsh k).symm
  have hsz (k) : G.Adj (s k) z :=
    ((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp (hs k)).1).symm
  have hinj : Function.Injective h := by
    intro k l heq
    apply hsinj
    exact congrArg Subtype.val (colors.injective (Subtype.ext heq))
  let F : Fin 3 → Finset (Finset (Fin 24)) := fun k =>
    (G.neighborFinset (h k) \ {z,s k}).image (threeHighSingletonCoordinates G e)
  refine ⟨h,F,?_,?_,?_,?_⟩
  · intro k
    exact ⟨hh k,hsh k,rfl⟩
  · intro k
    have hr := threeHigh_triple_coordinate_resolution_mem G hfree hmin hHigh hone
      z (h k) (s k) hz (hh k) (hsN k) (hsz k) e B hB
    have hcz := threeHigh_triple_root_coordinates_eq_singleton G hfree hmin hHigh hone z hz hu huz e heu
    have hcs := threeHigh_triple_special_coordinates_eq_row G hfree hmin hHigh hone z hz (hs k) e k (hrow k)
    simpa only [F,threeHighCanonicalResidual,hcz,hcs] using hr
  · intro k l
    exact threeHigh_triple_color_family_compatibility G hfree hmin hHigh hone
      z (h k) (h l) (s k) (s l) hz (hh k) (hh l) (hsN k) (hsN l) (hsz k) (hsz l) e B hB
  · intro k l hkl
    exact threeHigh_triple_color_family_intersection_cap G hfree hmin hHigh hone
      z (h k) (h l) (s k) (s l) hz (hh k) (hh l) (fun he => hkl (hinj he))
      (hsN k) (hsN l) (hsz k) (hsz l) e

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_joint_color_families
