import Proofs.Erdos85ThreeHighResolutionDomain
import Proofs.Erdos85OrderFortyNineThreeHighTripleCoordinateCover

namespace Erdos85
open SimpleGraph
noncomputable section

theorem threeHigh_triple_coordinate_resolution_mem
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z h s : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    (hh : h ∈ orderFortyNineHighVertices G)
    (hs : s ∈ G.neighborFinset h) (hsz : G.Adj s z)
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
    (B : Fin 24 → Fin 24 → Bool)
    (hB : ∀ i j, decide (G.Adj (e i).val (e j).val) = B i j) :
    let C := fun x => threeHighSingletonCoordinates G e x
    let O := G.neighborFinset h \ {z,s}
    O.image C ∈ threeHighResolutionDomain B (Finset.univ \ (C z ∪ C s)) := by
  classical
  let C := fun x => threeHighSingletonCoordinates G e x
  let O := G.neighborFinset h \ {z,s}
  let R := Finset.univ \ (C z ∪ C s)
  change O.image C ∈ threeHighResolutionDomain B R
  obtain ⟨hO, hd, hdis, hcover, hR⟩ :=
    threeHigh_triple_coordinate_color_cover G hfree hmin hHigh hone z h s hz hh hs hsz e
  change ∀ x ∈ O, (orderFortyNineHighSupport G x).card = 1 ∧ (C x).card = 3 at hd
  change ∀ x ∈ O, ∀ y ∈ O, x ≠ y → Disjoint (C x) (C y) at hdis
  change O.biUnion C = R at hcover
  have hinj : Set.InjOn C O := by
    intro x hx y hy heq
    by_contra hxy
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (C x).card by rw [(hd x hx).2]; omega)
    exact Finset.disjoint_left.mp (hdis x hx y hy hxy) hi (heq ▸ hi)
  apply (mem_threeHighResolutionDomain B R (O.image C)).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S hS
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hS
    apply (mem_threeHighEligibleTriples B R (C x)).mpr
    refine ⟨?_, (hd x hx).2, ?_⟩
    · intro i hi
      rw [← hcover]
      exact Finset.mem_biUnion.mpr ⟨x,hx,hi⟩
    · intro a ha b hb hab c hp
      have hn := threeHigh_triple_singleton_coordinates_no_common_neighbor
        G hfree e x (hd x hx).1 ha hb hab c
      apply hn
      constructor
      · exact of_decide_eq_true ((hB a c).trans hp.1)
      · exact of_decide_eq_true ((hB b c).trans hp.2)
  · exact (Finset.card_image_iff.mpr hinj).trans hO
  · intro S hS T hT hST
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hT
    exact hdis x hx y hy (fun heq => hST (congrArg C heq))
  · calc
      (O.image C).biUnion id = O.biUnion C := by
        ext i
        simp
      _ = R := hcover

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_coordinate_resolution_mem
