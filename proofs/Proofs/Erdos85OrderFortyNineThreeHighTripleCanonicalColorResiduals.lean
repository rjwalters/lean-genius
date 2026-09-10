import Proofs.Erdos85OrderFortyNineThreeHighTripleSingletonCoordinates
import Proofs.Erdos85ThreeHighEmptyTemplate

namespace Erdos85
open SimpleGraph
noncomputable section

def threeHighCanonicalRow (k : Fin 3) : Finset (Fin 24) :=
  Finset.univ.image fun i : Fin 5 => threeHighEmptyUIndex ((@finProdFinEquiv 3 5) (k,i))

theorem threeHighCanonicalRow_card (k : Fin 3) : (threeHighCanonicalRow k).card = 5 := by
  have hinj : Function.Injective (fun i : Fin 5 =>
      threeHighEmptyUIndex ((@finProdFinEquiv 3 5) (k,i))) := by
    intro i j h
    have hval := congrArg Fin.val h
    have hp : (@finProdFinEquiv 3 5) (k,i) = (@finProdFinEquiv 3 5) (k,j) := Fin.ext hval
    exact congrArg Prod.snd ((@finProdFinEquiv 3 5).injective hp)
  rw [threeHighCanonicalRow, Finset.card_image_of_injective _ hinj]
  simp

theorem threeHigh_triple_special_coordinates_eq_row
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj] [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (hmin : ∀ x, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {s : Fin 49} (hs : s ∈ threeHighTripleSpecialSet G z)
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49))) (k : Fin 3)
    (hrow : ∀ i, (e (threeHighEmptyUIndex ((@finProdFinEquiv 3 5) (k,i)))).val ∈
      G.neighborFinset s ∩ threeHighTripleEmptySet G) :
    threeHighSingletonCoordinates G e s = threeHighCanonicalRow k := by
  classical
  have hs1 := (Finset.mem_filter.mp hs).2
  have hsz := ((G.mem_neighborFinset z s).mp (Finset.mem_filter.mp hs).1).symm
  have hc : (threeHighSingletonCoordinates G e s).card = 5 := by
    rw [threeHighSingletonCoordinates, finsetCoordinates_card]
    exact threeHigh_triple_special_empty_count G hfree hmin hHigh hone z hz hs1 hsz
  have hsub : threeHighCanonicalRow k ⊆ threeHighSingletonCoordinates G e s := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact (mem_finsetCoordinates _ _ _ _).mpr (Finset.mem_inter.mp (hrow i)).1
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hc, threeHighCanonicalRow_card])).symm

theorem threeHigh_triple_root_coordinates_eq_singleton
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj] [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G) (hmin : ∀ x, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
    (heu : (e 23).val = u) :
    threeHighSingletonCoordinates G e z = {23} := by
  classical
  have hc : (threeHighSingletonCoordinates G e z).card = 1 := by
    rw [threeHighSingletonCoordinates, finsetCoordinates_card]
    exact threeHigh_triple_root_empty_neighbor_count G hfree hmin hHigh hone z hz
  have hm : 23 ∈ threeHighSingletonCoordinates G e z := by
    apply (mem_finsetCoordinates _ _ _ _).mpr
    rw [heu]
    exact (G.mem_neighborFinset _ _).mpr huz.symm
  exact (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hm)
    (by simpa using le_of_eq hc)).symm

end
end Erdos85
#print axioms Erdos85.threeHighCanonicalRow_card
#print axioms Erdos85.threeHigh_triple_special_coordinates_eq_row
#print axioms Erdos85.threeHigh_triple_root_coordinates_eq_singleton
