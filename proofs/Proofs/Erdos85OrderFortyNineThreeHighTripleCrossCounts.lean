import Proofs.Erdos85OrderFortyNineThreeHighTripleBlockTwoEdges

/-! The three cross-block counts are 5,5,5 or a permutation of 4,5,5. -/
namespace Erdos85
open SimpleGraph
noncomputable section

noncomputable def threeHighTripleBlockCrossCount
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] (s t : Fin 49) : ℕ := by
  classical
  exact ∑ x ∈ G.neighborFinset t ∩ threeHighTripleEmptySet G,
    (G.neighborFinset x ∩ (G.neighborFinset s ∩ threeHighTripleEmptySet G)).card

theorem threeHighTripleBlockCrossCount_comm
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] (s t : Fin 49) :
    threeHighTripleBlockCrossCount G s t = threeHighTripleBlockCrossCount G t s :=
  sum_card_neighbor_inter_comm G _ _

theorem threeHigh_triple_cross_count_patterns
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (s t v : Fin 49) (hst : s ≠ t) (hsv : s ≠ v) (htv : t ≠ v)
    (hS : threeHighTripleSpecialSet G z = {s,t,v}) :
    let a := threeHighTripleBlockCrossCount G s t
    let b := threeHighTripleBlockCrossCount G s v
    let c := threeHighTripleBlockCrossCount G t v
    (a = 5 ∧ b = 5 ∧ c = 5) ∨ (a = 4 ∧ b = 5 ∧ c = 5) ∨
      (a = 5 ∧ b = 4 ∧ c = 5) ∨ (a = 5 ∧ b = 5 ∧ c = 4) := by
  classical
  dsimp only
  have hs : s ∈ threeHighTripleSpecialSet G z := by rw [hS]; simp
  have ht : t ∈ threeHighTripleSpecialSet G z := by rw [hS]; simp
  have hv : v ∈ threeHighTripleSpecialSet G z := by rw [hS]; simp
  have hcap (x y : Fin 49) (hx : x ∈ threeHighTripleSpecialSet G z)
      (hy : y ∈ threeHighTripleSpecialSet G z) : threeHighTripleBlockCrossCount G x y ≤ 5 := by
    exact threeHigh_triple_special_cross_incidence_le_five G hfree hmin hHigh hone z hz x y
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
      (((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hy).1).symm)
  have ha := hcap s t hs ht
  have hb := hcap s v hs hv
  have hc := hcap t v ht hv
  have hms := (threeHigh_triple_special_cross_mass_bounds G hfree hmin hHigh hone z hz hu huz hs).1
  have hmt := (threeHigh_triple_special_cross_mass_bounds G hfree hmin hHigh hone z hz hu huz ht).1
  have hmv := (threeHigh_triple_special_cross_mass_bounds G hfree hmin hHigh hone z hz hu huz hv).1
  have hmass (x : Fin 49) : threeHighTripleBlockCrossMass G z x =
      ∑ y ∈ (threeHighTripleSpecialSet G z).erase x, threeHighTripleBlockCrossCount G x y := rfl
  rw [hmass s] at hms
  rw [hmass t] at hmt
  rw [hmass v] at hmv
  have hes : (threeHighTripleSpecialSet G z).erase s = {t,v} := by
    ext x
    simp only [hS, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have het : (threeHighTripleSpecialSet G z).erase t = {s,v} := by
    ext x
    simp only [hS, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hev : (threeHighTripleSpecialSet G z).erase v = {s,t} := by
    ext x
    simp only [hS, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  rw [hes] at hms
  rw [het] at hmt
  rw [hev] at hmv
  simp only [Finset.sum_pair htv] at hms
  simp only [Finset.sum_pair hsv] at hmt
  simp only [Finset.sum_pair hst] at hmv
  rw [threeHighTripleBlockCrossCount_comm G t s] at hmt
  rw [threeHighTripleBlockCrossCount_comm G v s, threeHighTripleBlockCrossCount_comm G v t] at hmv
  omega

end
end Erdos85
#print axioms Erdos85.threeHighTripleBlockCrossCount_comm
#print axioms Erdos85.threeHigh_triple_cross_count_patterns
