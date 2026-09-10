import Proofs.Erdos85OrderFortyNineThreeHighTripleOrdinaryCoordinateColorNeighbor
import Proofs.Erdos85OrderFortyNineThreeHighTripleOrdinaryColorCover

namespace Erdos85
open SimpleGraph

def encodedFamilyCompatibility (B : Fin 24 → Fin 24 → Bool)
    (F K : Finset (Finset (Fin 24))) : Bool :=
  decide (∀ S ∈ F, ∃ T ∈ K, encodedCrossIndependent B S T = true)

noncomputable section

theorem threeHigh_triple_color_family_compatibility
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z h₁ h₂ s₁ s₂ : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    (hh₁ : h₁ ∈ orderFortyNineHighVertices G) (hh₂ : h₂ ∈ orderFortyNineHighVertices G)
    (hs₁ : s₁ ∈ G.neighborFinset h₁) (hs₂ : s₂ ∈ G.neighborFinset h₂)
    (hsz₁ : G.Adj s₁ z) (hsz₂ : G.Adj s₂ z)
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
    (B : Fin 24 → Fin 24 → Bool)
    (hB : ∀ i j, decide (G.Adj (e i).val (e j).val) = B i j) :
    encodedFamilyCompatibility B
      ((G.neighborFinset h₁ \ {z,s₁}).image (threeHighSingletonCoordinates G e))
      ((G.neighborFinset h₂ \ {z,s₂}).image (threeHighSingletonCoordinates G e)) = true := by
  classical
  have hcover := threeHigh_triple_ordinary_color_cover G hfree hmin hHigh hone
    z h₁ s₁ hz hh₁ hs₁ hsz₁
  have hh8 : G.degree h₁ = 8 := (Finset.mem_filter.mp hh₁).2
  apply decide_eq_true_iff.mpr
  intro S hS
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hS
  have hxd := hcover.2.1 x hx
  have hx7 := orderFortyNine_neighbor_degree_seven_of_degreeEight G hfree hmin
    (Fintype.card_fin 49) hh8 ((G.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp hx).1)
  have hxnz : ¬ G.Adj x z := by
    intro ha
    have hd := threeHigh_triple_empty_neighbor_degree G hfree hmin hHigh hone z hz hx7
    change (G.neighborFinset x ∩ threeHighTripleEmptySet G).card + _ = _ at hd
    rw [hxd.1, hxd.2, if_pos ha] at hd
    omega
  obtain ⟨T, hT, hTc, hgate⟩ := threeHigh_triple_coordinate_color_compatibility
    G hfree hmin hHigh hone z hz e B hB hxd.1 hxnz hh₂ s₂ hs₂ hsz₂
  exact ⟨T,hT,hgate⟩

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_color_family_compatibility
