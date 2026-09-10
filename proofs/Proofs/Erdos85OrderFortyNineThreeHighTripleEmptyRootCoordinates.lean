import Proofs.Erdos85OrderFortyNineThreeHighTripleEmptyCoordinates
import Proofs.Erdos85OrderFortyNineThreeHighTripleSecondaryCoordinates

namespace Erdos85
open SimpleGraph
noncomputable section

theorem threeHigh_triple_empty_root_coordinates
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (lU : Fin 15 ≃ (↑(threeHighTripleSpecialUnion G z) : Set (Fin 49))) :
    let N := G.neighborFinset u ∩ threeHighTripleEmptySet G
    let m := (G.induce (↑N : Set (Fin 49))).edgeFinset.card
    ∃ e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)),
      (∀ i, (e (Fin.castAdd 1 (Fin.castAdd 8 i))).val = (lU i).val) ∧
      (e 23).val = u ∧
      (∀ i, ¬ G.Adj (e 23).val (e (Fin.castAdd 1 (Fin.castAdd 8 i))).val) ∧
      (∀ i : Fin 6, G.Adj (e 23).val
        (e (Fin.castAdd 1 (Fin.natAdd 15 (Fin.castAdd 2 i)))).val) ∧
      (∀ j : Fin 2, ¬ G.Adj (e 23).val
        (e (Fin.castAdd 1 (Fin.natAdd 15 (Fin.natAdd 6 j)))).val) ∧
      (∀ i j : Fin 6, G.Adj
        (e (Fin.castAdd 1 (Fin.natAdd 15 (Fin.castAdd 2 i)))).val
        (e (Fin.castAdd 1 (Fin.natAdd 15 (Fin.castAdd 2 j)))).val ↔ matchingFinSixAdj m i j) := by
  classical
  let E := threeHighTripleEmptySet G
  let N := G.neighborFinset u ∩ E
  let R := E \ insert u (threeHighTripleSpecialUnion G z)
  obtain ⟨lR, hN, hT, hmatch⟩ := threeHigh_triple_secondary_coordinates
    G hfree hmin hHigh hone z hz hu huz
  obtain ⟨e, heU, heu, heR, hnoU⟩ := threeHigh_triple_empty_coordinates
    G hfree hmin hHigh hone z hz hu huz lU lR
  refine ⟨e, heU, heu, hnoU, ?_, ?_, ?_⟩
  · intro i
    rw [heu, heR]
    exact (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp (hN i)).1
  · intro j
    rw [heu, heR]
    intro ha
    have ht := Finset.mem_sdiff.mp (hT j)
    apply ht.2
    exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha, (Finset.mem_sdiff.mp ht.1).1⟩
  · intro i j
    rw [heR, heR]
    exact hmatch i j

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_empty_root_coordinates
