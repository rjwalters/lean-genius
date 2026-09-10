import Proofs.Erdos85OrderFortyNineThreeHighTripleSingletonCoordinates
import Proofs.Erdos85OrderFortyNineThreeHighTripleOrdinaryColorNeighbor

namespace Erdos85
open SimpleGraph

def encodedCrossIndependent (B : Fin 24 → Fin 24 → Bool) (S T : Finset (Fin 24)) : Bool :=
  decide (∀ i ∈ S, ∀ j ∈ T, B i j = false)

noncomputable section
theorem threeHigh_triple_ordinary_coordinate_color_neighbor
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
    (hxz : ¬ G.Adj x z) (hh : h ∈ orderFortyNineHighVertices G) :
    ∃ y, y ≠ x ∧ (orderFortyNineHighSupport G y).card = 1 ∧ ¬ G.Adj y z ∧
      G.Adj x y ∧ G.Adj y h ∧
      (threeHighSingletonCoordinates G e x).card = 3 ∧
      (threeHighSingletonCoordinates G e y).card = 3 ∧
      encodedCrossIndependent B (threeHighSingletonCoordinates G e x)
        (threeHighSingletonCoordinates G e y) = true := by
  classical
  obtain ⟨y, hyx, hy7, hy1, hyz, hxy, hyh, hy3, hcompat⟩ :=
    threeHigh_triple_ordinary_exists_compatible_color_neighbor G hfree hmin hHigh hone z hz hx hxz hh
  refine ⟨y, hyx, hy1, hyz, hxy, hyh, ?_, ?_, ?_⟩
  · exact threeHigh_triple_ordinary_coordinates_card G hfree hmin hHigh hone z hz e hx hxz
  · exact threeHigh_triple_ordinary_coordinates_card G hfree hmin hHigh hone z hz e hy1 hyz
  · apply decide_eq_true_iff.mpr
    intro i hi j hj
    have hxi : G.Adj x (e i).val := (G.mem_neighborFinset _ _).mp
      ((mem_finsetCoordinates _ _ _ _).mp hi)
    have hyj : G.Adj y (e j).val := (G.mem_neighborFinset _ _).mp
      ((mem_finsetCoordinates _ _ _ _).mp hj)
    have hn := hcompat (e i).val (e i).property (e j).val (e j).property hxi hyj
    rw [← hB i j]
    simp [hn]

theorem threeHigh_triple_coordinate_color_compatibility
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
  exact ⟨threeHighSingletonCoordinates G e y, Finset.mem_image.mpr ⟨y,hyo,rfl⟩, hy3, hgate⟩

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_ordinary_coordinate_color_neighbor

#print axioms Erdos85.threeHigh_triple_coordinate_color_compatibility
