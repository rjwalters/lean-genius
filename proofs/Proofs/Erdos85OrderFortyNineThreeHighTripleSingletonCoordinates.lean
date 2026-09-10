import Proofs.Erdos85FinsetCoordinates
import Proofs.Erdos85OrderFortyNineThreeHighTripleOrdinaryEligibility

namespace Erdos85
open SimpleGraph

noncomputable def threeHighSingletonCoordinates (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49))) (x : Fin 49) : Finset (Fin 24) :=
  finsetCoordinates (threeHighTripleEmptySet G) e (G.neighborFinset x)

theorem threeHigh_triple_ordinary_coordinates_card
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj] [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (hmin : ∀ x, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
    {x : Fin 49} (hx : (orderFortyNineHighSupport G x).card = 1) (hxz : ¬ G.Adj x z) :
    (threeHighSingletonCoordinates G e x).card = 3 := by
  rw [threeHighSingletonCoordinates, finsetCoordinates_card]
  exact threeHigh_triple_ordinary_empty_degree_three G hfree hmin hHigh hone z hz hx hxz

theorem threeHigh_triple_singleton_coordinates_no_common_neighbor
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
    (x : Fin 49) (hx : (orderFortyNineHighSupport G x).card = 1)
    {a b : Fin 24} (ha : a ∈ threeHighSingletonCoordinates G e x)
    (hb : b ∈ threeHighSingletonCoordinates G e x) (hab : a ≠ b) :
    ∀ c : Fin 24, ¬ (G.Adj (e a).val (e c).val ∧ G.Adj (e b).val (e c).val) := by
  have hmem {i : Fin 24} (hi : i ∈ threeHighSingletonCoordinates G e x) :
      (e i).val ∈ G.neighborFinset x ∩ threeHighTripleEmptySet G :=
    Finset.mem_inter.mpr ⟨(mem_finsetCoordinates _ _ _ _).mp hi, (e i).property⟩
  have hne : (e a).val ≠ (e b).val := fun h => hab (e.injective (Subtype.ext h))
  intro c
  exact threeHigh_triple_singleton_pair_no_common_empty_neighbor G hfree x hx
    (hmem ha) (hmem hb) hne (e c).val (e c).property

theorem threeHigh_triple_singleton_coordinates_inter_le_one
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
    (x y : Fin 49) (hxy : x ≠ y) :
    (threeHighSingletonCoordinates G e x ∩ threeHighSingletonCoordinates G e y).card ≤ 1 := by
  rw [threeHighSingletonCoordinates, threeHighSingletonCoordinates,
    finsetCoordinates_inter, finsetCoordinates_card]
  exact (Finset.card_le_card Finset.inter_subset_left).trans
    ((not_containsC4_iff_forall_common_le_one G).mp hfree x y hxy)

end Erdos85
#print axioms Erdos85.threeHigh_triple_ordinary_coordinates_card
#print axioms Erdos85.threeHigh_triple_singleton_coordinates_no_common_neighbor
#print axioms Erdos85.threeHigh_triple_singleton_coordinates_inter_le_one
