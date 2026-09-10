import Proofs.Erdos85OrderFortyNineThreeHighTripleEmptyCoordinates
import Proofs.Erdos85SquareOrderTwoHighTerminal

namespace Erdos85
open SimpleGraph
noncomputable section

theorem threeHigh_triple_empty_coordinate_degrees
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
    (heu : (e 23).val = u) :
    let H := SimpleGraph.comap e (G.induce (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
    ∀ i, H.degree i = if i = 23 then 6 else 4 := by
  classical
  let E := threeHighTripleEmptySet G
  let H := SimpleGraph.comap e (G.induce (↑E : Set (Fin 49)))
  change ∀ i : Fin 24, H.degree i = if i = 23 then 6 else 4
  intro i
  have hx := (e i).property
  have hx0 := (Finset.mem_filter.mp hx).2
  have hx7 : G.degree (e i).val = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin (Fintype.card_fin 49) (e i).val with h | h
    · exact h
    · exact ((Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).2
        (by simp [orderFortyNineHighVertices, h])).elim
  have hd := threeHigh_triple_empty_neighbor_degree G hfree hmin hHigh hone z hz hx7
  have hroot : (G.neighborFinset z ∩ E).card = 1 :=
    threeHigh_triple_root_empty_neighbor_count G hfree hmin hHigh hone z hz
  have huin : u ∈ G.neighborFinset z ∩ E :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr huz.symm, hu⟩
  have ha : G.Adj (e i).val z ↔ i = 23 := by
    constructor
    · intro hi
      have hin : (e i).val ∈ G.neighborFinset z ∩ E :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr hi.symm, hx⟩
      have heq := Finset.card_le_one.mp (le_of_eq hroot) _ hin _ huin
      exact e.injective (Subtype.ext (heq.trans heu.symm))
    · intro hi
      subst i
      simpa only [heu] using huz
  have hdeg : H.degree i = (G.neighborFinset (e i).val ∩ E).card := by
    exact ((SimpleGraph.Iso.comap e (G.induce (↑E : Set (Fin 49)))).degree_eq i).symm.trans
      (degree_induce_finset_eq_card_inter G E (e i))
  change H.degree i = _
  rw [hdeg]
  change (G.neighborFinset (e i).val ∩ E).card + _ = _ at hd
  rw [hx0, Nat.add_zero] at hd
  by_cases hi : i = 23
  · have hz' := ha.mpr hi
    rw [if_pos hi]
    rw [if_pos hz'] at hd
    omega
  · have hz' : ¬ G.Adj (e i).val z := fun h => hi (ha.mp h)
    simpa only [if_neg hi, if_neg hz', mul_zero, Nat.add_zero] using hd

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_empty_coordinate_degrees
