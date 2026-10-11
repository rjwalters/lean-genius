import Proofs.Erdos85OrderFortyNineThreeHighTripleColorFamilyCompatibility
import Proofs.Erdos85ColorCompatibilityRelabeling

/-! The H3 Python terminal requires a different ordinary singleton as a neighbor,
including within the same color. The older encodedFamilyCompatibility allows
T = S. This module retains distinctness after passing to empty-neighbor coordinates.
The companion distinct joint-witness module carries this fact through relabeling;
the complete finite census remains a separate obligation. -/

namespace Erdos85
open SimpleGraph

def encodedDistinctFamilyCompatibility (B : Fin 24 → Fin 24 → Bool)
    (F K : Finset (Finset (Fin 24))) : Bool :=
  decide (∀ S ∈ F, ∃ T ∈ K, T ≠ S ∧ encodedCrossIndependent B S T = true)

theorem encodedDistinctFamilyCompatibility_forget
    (B : Fin 24 → Fin 24 → Bool) (F K : Finset (Finset (Fin 24)))
    (h : encodedDistinctFamilyCompatibility B F K = true) :
    encodedFamilyCompatibility B F K = true := by
  apply decide_eq_true_iff.mpr
  have hh := of_decide_eq_true h
  intro S hS
  obtain ⟨T, hT, _, hST⟩ := hh S hS
  exact ⟨T, hT, hST⟩

/-- The stronger neighbor condition survives the label permutations used by the
compact orbit reductions. -/
theorem encodedDistinctFamilyCompatibility_relabel
    (B : Fin 24 → Fin 24 → Bool) (F K : Finset (Finset (Fin 24)))
    (e : Equiv.Perm (Fin 24)) :
    encodedDistinctFamilyCompatibility (fun i j => B (e.symm i) (e.symm j))
      (F.image fun S => S.image e) (K.image fun T => T.image e) =
        encodedDistinctFamilyCompatibility B F K := by
  unfold encodedDistinctFamilyCompatibility
  apply Bool.decide_congr
  constructor
  · intro h S hS
    obtain ⟨T, hT, hne, hgate⟩ := h (S.image e) (Finset.mem_image.mpr ⟨S, hS, rfl⟩)
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hT
    refine ⟨A, hA, ?_, ?_⟩
    · intro heq
      exact hne (congrArg (fun Q : Finset (Fin 24) => Q.image e) heq)
    · simpa only [encodedCrossIndependent_relabel] using hgate
  · intro h S hS
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨T, hT, hne, hgate⟩ := h A hA
    refine ⟨T.image e, Finset.mem_image.mpr ⟨T, hT, rfl⟩, ?_, ?_⟩
    · intro heq
      exact hne (Finset.image_injective e.injective heq)
    · simpa only [encodedCrossIndependent_relabel] using hgate

noncomputable section

theorem threeHigh_triple_distinct_coordinate_color_compatibility
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
    (B : Fin 24 → Fin 24 → Bool)
    (hB : ∀ i j, decide (G.Adj (e i).val (e j).val) = B i j)
    {x h : Fin 49} (hx : (orderFortyNineHighSupport G x).card = 1)
    (hxz : ¬ G.Adj x z) (hh : h ∈ orderFortyNineHighVertices G)
    (s : Fin 49) (hs : s ∈ G.neighborFinset h) (hsz : G.Adj s z) :
    ∃ T ∈ (G.neighborFinset h \ {z,s}).image (threeHighSingletonCoordinates G e),
      T ≠ threeHighSingletonCoordinates G e x ∧
      T.card = 3 ∧ encodedCrossIndependent B (threeHighSingletonCoordinates G e x) T = true := by
  classical
  obtain ⟨y, hyx, hy1, hyz, hxy, hyh, hx3, hy3, hgate⟩ :=
    threeHigh_triple_ordinary_coordinate_color_neighbor G hfree hmin hHigh hone z hz e B hB hx hxz hh
  have hyne : y ≠ z := by
    intro he
    rw [he, hz] at hy1
    contradiction
  have hyns : y ≠ s := by
    intro he
    exact hyz (he ▸ hsz)
  have hyo : y ∈ G.neighborFinset h \ {z,s} := by
    apply Finset.mem_sdiff.mpr
    refine ⟨(G.mem_neighborFinset _ _).mpr hyh.symm, ?_⟩
    simp [hyne, hyns]
  have hne : threeHighSingletonCoordinates G e y ≠ threeHighSingletonCoordinates G e x := by
    intro heq
    have hinter := threeHigh_triple_singleton_coordinates_inter_le_one G hfree e y x hyx
    rw [heq, Finset.inter_self, hx3] at hinter
    omega
  exact ⟨threeHighSingletonCoordinates G e y, Finset.mem_image.mpr ⟨y,hyo,rfl⟩,
    hne, hy3, hgate⟩


theorem threeHigh_triple_distinct_color_family_compatibility
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
    encodedDistinctFamilyCompatibility B
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
  obtain ⟨T, hT, hne, hTc, hgate⟩ := threeHigh_triple_distinct_coordinate_color_compatibility
    G hfree hmin hHigh hone z hz e B hB hxd.1 hxnz hh₂ s₂ hs₂ hsz₂
  exact ⟨T,hT,hne,hgate⟩


end
end Erdos85

#print axioms Erdos85.encodedDistinctFamilyCompatibility_forget
#print axioms Erdos85.encodedDistinctFamilyCompatibility_relabel
#print axioms Erdos85.threeHigh_triple_distinct_coordinate_color_compatibility
#print axioms Erdos85.threeHigh_triple_distinct_color_family_compatibility
