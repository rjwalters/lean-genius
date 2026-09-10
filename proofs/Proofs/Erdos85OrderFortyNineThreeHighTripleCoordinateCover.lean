import Proofs.Erdos85OrderFortyNineThreeHighTripleSingletonCoordinates
import Proofs.Erdos85OrderFortyNineThreeHighTripleOrdinaryColorCover

namespace Erdos85
open SimpleGraph
noncomputable section

/-- Each high color supplies six disjoint coordinate triples covering its 18 residual labels. -/
theorem threeHigh_triple_coordinate_color_cover
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (hmin : ∀ v, 7 ≤ G.degree v)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z h s : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    (hh : h ∈ orderFortyNineHighVertices G)
    (hs : s ∈ G.neighborFinset h) (hsz : G.Adj s z)
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49))) :
    let O := G.neighborFinset h \ {z,s}
    let C := fun x => threeHighSingletonCoordinates G e x
    let R := Finset.univ \ (C z ∪ C s)
    O.card = 6 ∧
    (∀ x ∈ O, (orderFortyNineHighSupport G x).card = 1 ∧ (C x).card = 3) ∧
    (∀ x ∈ O, ∀ y ∈ O, x ≠ y → Disjoint (C x) (C y)) ∧
    O.biUnion C = R ∧ R.card = 18 := by
  classical
  let E := threeHighTripleEmptySet G
  let O := G.neighborFinset h \ {z,s}
  let C := fun x => threeHighSingletonCoordinates G e x
  let R := Finset.univ \ (C z ∪ C s)
  obtain ⟨hO, hd, hdis, hcover, hR⟩ :=
    threeHigh_triple_ordinary_color_cover G hfree hmin hHigh hone z h s hz hh hs hsz
  have hmem (x : Fin 49) (i : Fin 24) :
      i ∈ C x ↔ (e i).val ∈ G.neighborFinset x ∩ E := by
    simp only [C, threeHighSingletonCoordinates, mem_finsetCoordinates, Finset.mem_inter]
    exact ⟨fun hi => ⟨hi, (e i).property⟩, fun hi => hi.1⟩
  change O.card = 6 ∧ (∀ x ∈ O, (orderFortyNineHighSupport G x).card = 1 ∧ (C x).card = 3) ∧
    (∀ x ∈ O, ∀ y ∈ O, x ≠ y → Disjoint (C x) (C y)) ∧ O.biUnion C = R ∧ R.card = 18
  have hc : O.biUnion C = R := by
    ext i
    have he := Finset.ext_iff.mp hcover (e i).val
    change ((e i).val ∈ O.biUnion (fun x => G.neighborFinset x ∩ E) ↔
      (e i).val ∈ E \ ((G.neighborFinset z ∩ E) ∪ (G.neighborFinset s ∩ E))) at he
    have hei : (e i).val ∈ E := (e i).property
    simpa only [R, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_biUnion, hmem, hei] using he
  refine ⟨hO, ?_, ?_, hc, ?_⟩
  · intro x hx
    refine ⟨(hd x hx).1, ?_⟩
    change (threeHighSingletonCoordinates G e x).card = 3
    rw [threeHighSingletonCoordinates, finsetCoordinates_card]
    exact (hd x hx).2
  · intro x hx y hy hxy
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact Finset.disjoint_left.mp (hdis x hx y hy hxy)
      ((hmem x i).mp hi) ((hmem y i).mp hj)
  · have hrcoords : R = finsetCoordinates E e
        (E \ ((G.neighborFinset z ∩ E) ∪ (G.neighborFinset s ∩ E))) := by
      ext i
      have hei : (e i).val ∈ E := (e i).property
      simp only [R, Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_union, hmem, mem_finsetCoordinates, hei]
    rw [hrcoords, finsetCoordinates_card, Finset.inter_eq_left.mpr Finset.sdiff_subset]
    exact hR

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_coordinate_color_cover
