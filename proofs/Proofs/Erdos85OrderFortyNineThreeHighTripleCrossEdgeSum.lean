import Proofs.Erdos85OrderFortyNineThreeHighTripleCrossCounts
import Proofs.Erdos85OrderFortyNineThreeHighTripleUnionEdges
import Proofs.Erdos85OrderFortyNineThreeHighTripleEdgeLedger

/-! The labeled cross counts determine the special-union edge count. -/
namespace Erdos85
open SimpleGraph
noncomputable section
private theorem erase_three_labels {V : Type*} [DecidableEq V]
    (s t v : V) (hst : s ≠ t) (hsv : s ≠ v) (htv : t ≠ v) :
    ({s,t,v} : Finset V).erase s = {t,v} ∧
      ({s,t,v} : Finset V).erase t = {s,v} ∧
      ({s,t,v} : Finset V).erase v = {s,t} := by
  constructor
  · ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  constructor
  · ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  · ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop

variable (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  (hfree : ¬ containsC4 (Fin 49) G)
  (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
  (hHigh : (orderFortyNineHighVertices G).card = 3)
  (hone : orderFortyNineHighIncidenceCount G 3 = 1)
  (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
  {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
  (s t v : Fin 49) (hst : s ≠ t) (hsv : s ≠ v) (htv : t ≠ v)
  (hS : threeHighTripleSpecialSet G z = {s,t,v})
include hfree hmin hHigh hone hz hu huz hst hsv htv hS

theorem threeHigh_triple_union_edges_eq_six_add_cross_counts :
    (G.induce (↑(threeHighTripleSpecialUnion G z) : Set (Fin 49))).edgeFinset.card =
      6 + threeHighTripleBlockCrossCount G s t + threeHighTripleBlockCrossCount G s v +
      threeHighTripleBlockCrossCount G t v := by
  classical
  let S := threeHighTripleSpecialSet G z
  let U := threeHighTripleSpecialUnion G z
  let block := fun x => G.neighborFinset x ∩ threeHighTripleEmptySet G
  have hd : (↑S : Set (Fin 49)).Pairwise (fun x y => Disjoint (block x) (block y)) := by
    intro x hx y hy hxy
    exact threeHigh_triple_special_empty_blocks_disjoint G hfree hmin hHigh z hz hxy
      (((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hx).1).symm)
      (((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hy).1).symm)
  have hsum : (∑ x ∈ U, (G.neighborFinset x ∩ U).card) =
      ∑ x ∈ S, (4 + threeHighTripleBlockCrossMass G z x) := by
    rw [show (∑ x ∈ U, (G.neighborFinset x ∩ U).card) =
      ∑ y ∈ S, ∑ x ∈ block y, (G.neighborFinset x ∩ U).card from Finset.sum_biUnion hd]
    apply Finset.sum_congr rfl
    intro x hx
    exact threeHigh_triple_special_union_incidence G hfree hmin hHigh hone z hz hu huz hx
  have hh := sum_internalNeighbor_card_eq_twice_induced_edges G U
  simp only [Finset.filter_mem_eq_inter] at hh
  rw [hsum] at hh
  have hlabels := erase_three_labels s t v hst hsv htv
  have hes : S.erase s = {t,v} := by simpa only [S, hS] using hlabels.1
  have het : S.erase t = {s,v} := by simpa only [S, hS] using hlabels.2.1
  have hev : S.erase v = {s,t} := by simpa only [S, hS] using hlabels.2.2
  have hmass (x : Fin 49) : threeHighTripleBlockCrossMass G z x =
      ∑ y ∈ S.erase x, threeHighTripleBlockCrossCount G x y := rfl
  have hms : threeHighTripleBlockCrossMass G z s =
      threeHighTripleBlockCrossCount G s t + threeHighTripleBlockCrossCount G s v := by
    rw [hmass, hes, Finset.sum_pair htv]
  have hmt : threeHighTripleBlockCrossMass G z t =
      threeHighTripleBlockCrossCount G s t + threeHighTripleBlockCrossCount G t v := by
    rw [hmass, het, Finset.sum_pair hsv, threeHighTripleBlockCrossCount_comm G t s]
  have hmv : threeHighTripleBlockCrossMass G z v =
      threeHighTripleBlockCrossCount G s v + threeHighTripleBlockCrossCount G t v := by
    rw [hmass, hev, Finset.sum_pair hst, threeHighTripleBlockCrossCount_comm G v s,
      threeHighTripleBlockCrossCount_comm G v t]
  have hS' : S = {s,t,v} := hS
  rw [hS', Finset.sum_insert (by simp [hst,hsv]), Finset.sum_pair htv, hms, hmt, hmv] at hh
  change (G.induce (↑U : Set (Fin 49))).edgeFinset.card = _
  omega

theorem threeHigh_triple_four_secondary_edges_all_cross_five
    (hr : (G.induce (↑(threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)) :
      Set (Fin 49))).edgeFinset.card = 4) :
    threeHighTripleBlockCrossCount G s t = 5 ∧ threeHighTripleBlockCrossCount G s v = 5 ∧
      threeHighTripleBlockCrossCount G t v = 5 := by
  have hl := (threeHigh_triple_union_secondary_edge_ledger G hfree hmin hHigh hone z hz hu huz).1
  have hs := threeHigh_triple_union_edges_eq_six_add_cross_counts G hfree hmin hHigh hone z hz
    hu huz s t v hst hsv htv hS
  have hp := threeHigh_triple_cross_count_patterns G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS
  dsimp only at hl hp
  rw [hr] at hl
  omega

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_union_edges_eq_six_add_cross_counts
#print axioms Erdos85.threeHigh_triple_four_secondary_edges_all_cross_five
