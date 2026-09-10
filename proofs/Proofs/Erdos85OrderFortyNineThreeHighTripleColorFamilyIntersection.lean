import Proofs.Erdos85OrderFortyNineThreeHighTripleColorFamilyCompatibility

namespace Erdos85
open SimpleGraph

def encodedFamilyIntersectionCap (F K : Finset (Finset (Fin 24))) : Bool :=
  decide (∀ S ∈ F, ∀ T ∈ K, (S ∩ T).card ≤ 1)

noncomputable section

theorem threeHigh_triple_color_family_intersection_cap
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj] [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (hmin : ∀ x, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z h₁ h₂ s₁ s₂ : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    (hh₁ : h₁ ∈ orderFortyNineHighVertices G) (hh₂ : h₂ ∈ orderFortyNineHighVertices G)
    (hne : h₁ ≠ h₂)
    (hs₁ : s₁ ∈ G.neighborFinset h₁) (hs₂ : s₂ ∈ G.neighborFinset h₂)
    (hsz₁ : G.Adj s₁ z) (hsz₂ : G.Adj s₂ z)
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49))) :
    encodedFamilyIntersectionCap
      ((G.neighborFinset h₁ \ {z,s₁}).image (threeHighSingletonCoordinates G e))
      ((G.neighborFinset h₂ \ {z,s₂}).image (threeHighSingletonCoordinates G e)) = true := by
  classical
  have hcover := threeHigh_triple_ordinary_color_cover G hfree hmin hHigh hone
    z h₁ s₁ hz hh₁ hs₁ hsz₁
  apply decide_eq_true_iff.mpr
  intro S hS T hT
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hS
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hT
  have hxy : x ≠ y := by
    intro heq
    have hx1 := (hcover.2.1 x hx).1
    have hm₁ : h₁ ∈ orderFortyNineHighSupport G x := Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp
        (Finset.mem_sdiff.mp hx).1).symm, hh₁⟩
    have hm₂ : h₂ ∈ orderFortyNineHighSupport G x := by
      rw [heq]
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr
        ((G.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp hy).1).symm, hh₂⟩
    exact hne (Finset.card_le_one.mp (le_of_eq hx1) _ hm₁ _ hm₂)
  exact threeHigh_triple_singleton_coordinates_inter_le_one G hfree e x y hxy

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_color_family_intersection_cap
