import Proofs.Erdos85ThreeHighEmptyTemplate
import Proofs.Erdos85OrderFortyNineThreeHighTripleEmptyCoordinateDegrees

namespace Erdos85
open SimpleGraph
noncomputable section

theorem threeHigh_triple_empty_template_of_labelings
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (lU : Fin 15 ≃ (↑(threeHighTripleSpecialUnion G z) : Set (Fin 49)))
    (lR : Fin 8 ≃ (↑(threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)) : Set (Fin 49)))
    (RAdj : Fin 8 → Fin 8 → Bool)
    (hN : ∀ i : Fin 6, (lR (Fin.castAdd 2 i)).val ∈ G.neighborFinset u ∩ threeHighTripleEmptySet G)
    (hT : ∀ a : Fin 2, (lR (Fin.natAdd 6 a)).val ∈
      (threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)) \ (G.neighborFinset u ∩ threeHighTripleEmptySet G))
    (hR : ∀ p q, decide (G.Adj (lR p).val (lR q).val) = RAdj p q) :
    ∃ (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
      (cross : Fin 15 → Fin 8 → Bool),
      (e 23).val = u ∧
      (∀ i, (e (threeHighEmptyUIndex i)).val = (lU i).val) ∧
      (∀ p q, decide (G.Adj (e p).val (e q).val) = threeHighEmptyAdj
        (fun i j => decide (G.Adj (lU i).val (lU j).val))
        RAdj cross p q) ∧
      (∀ i, (SimpleGraph.comap e (G.induce (↑(threeHighTripleEmptySet G) : Set (Fin 49)))).degree i =
        if i = 23 then 6 else 4) := by
  classical
  let E := threeHighTripleEmptySet G
  let N := G.neighborFinset u ∩ E
  let R := E \ insert u (threeHighTripleSpecialUnion G z)
  obtain ⟨e, heU, heu, heR, hnoU⟩ := threeHigh_triple_empty_coordinates
    G hfree hmin hHigh hone z hz hu huz lU lR
  let H := SimpleGraph.comap e (G.induce (↑E : Set (Fin 49)))
  let UAdj := fun i j => decide (G.Adj (lU i).val (lU j).val)
  have hUU : ∀ i j, decide (H.Adj (threeHighEmptyUIndex i) (threeHighEmptyUIndex j)) = UAdj i j := by
    intro i j
    apply Bool.decide_congr
    change G.Adj (e (threeHighEmptyUIndex i)).val (e (threeHighEmptyUIndex j)).val ↔ G.Adj (lU i).val (lU j).val
    simp only [threeHighEmptyUIndex]
    rw [heU, heU]
  have hRR : ∀ i j, decide (H.Adj (threeHighEmptyRIndex i) (threeHighEmptyRIndex j)) = RAdj i j := by
    intro i j
    calc
      decide (H.Adj (threeHighEmptyRIndex i) (threeHighEmptyRIndex j)) =
          decide (G.Adj (lR i).val (lR j).val) := by
        apply Bool.decide_congr
        change G.Adj (e (threeHighEmptyRIndex i)).val (e (threeHighEmptyRIndex j)).val ↔ G.Adj (lR i).val (lR j).val
        simp only [threeHighEmptyRIndex]
        rw [heR, heR]
      _ = RAdj i j := hR i j
  have huU : ∀ i, ¬ H.Adj 23 (threeHighEmptyUIndex i) := hnoU
  have huR : ∀ j, H.Adj 23 (threeHighEmptyRIndex j) ↔ j.val < 6 := by
    intro j
    change G.Adj (e 23).val (e (threeHighEmptyRIndex j)).val ↔ _
    simp only [threeHighEmptyRIndex]
    rw [heu, heR]
    refine Fin.addCases (m := 6) (n := 2) (fun i => ?_) (fun a => ?_) j
    · apply iff_of_true
      · exact (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp (hN i)).1
      · exact i.isLt
    · apply iff_of_false
      · intro ha
        have ht := Finset.mem_sdiff.mp (hT a)
        apply ht.2
        exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha, (Finset.mem_sdiff.mp ht.1).1⟩
      · change ¬ 6 + a.val < 6
        omega
  let cross := fun i j => decide (H.Adj (threeHighEmptyUIndex i) (threeHighEmptyRIndex j))
  refine ⟨e, cross, heu, heU, ?_, ?_⟩
  · exact threeHighEmptyAdj_eq_graph H UAdj RAdj hUU hRR huU huR
  · exact threeHigh_triple_empty_coordinate_degrees G hfree hmin hHigh hone z hz hu huz e heu

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_empty_template_of_labelings
