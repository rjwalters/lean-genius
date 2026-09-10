import Proofs.Erdos85OrderFortyNineThreeHighTripleBlockTwoEdges
import Proofs.Erdos85ThreeLevelEigenSupportEdgeCensus

/-! The special union has exactly twenty or twenty-one edges. -/
namespace Erdos85
open SimpleGraph
noncomputable section
variable (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  (hfree : ¬ containsC4 (Fin 49) G)
  (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
  (hHigh : (orderFortyNineHighVertices G).card = 3)
  (hone : orderFortyNineHighIncidenceCount G 3 = 1)
  (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
  {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)

include hfree hmin hHigh hz in
private theorem special_blocks_pairwise_disjoint :
    (↑(threeHighTripleSpecialSet G z) : Set (Fin 49)).Pairwise (fun s t =>
      Disjoint (G.neighborFinset s ∩ threeHighTripleEmptySet G)
        (G.neighborFinset t ∩ threeHighTripleEmptySet G)) := by
  intro s hs t ht hst
  exact threeHigh_triple_special_empty_blocks_disjoint G hfree hmin hHigh z hz hst
    (((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hs).1).symm)
    (((G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp ht).1).symm)

include hfree hmin hHigh hone hz hu huz

theorem threeHigh_triple_special_union_incidence
    {s : Fin 49} (hs : s ∈ threeHighTripleSpecialSet G z) :
    (∑ x ∈ G.neighborFinset s ∩ threeHighTripleEmptySet G,
      (G.neighborFinset x ∩ threeHighTripleSpecialUnion G z).card) =
      4 + threeHighTripleBlockCrossMass G z s := by
  classical
  let B := G.neighborFinset s ∩ threeHighTripleEmptySet G
  let S := threeHighTripleSpecialSet G z
  let U := threeHighTripleSpecialUnion G z
  let block := fun t => G.neighborFinset t ∩ threeHighTripleEmptySet G
  change (∑ x ∈ B, (G.neighborFinset x ∩ U).card) = 4 + _
  rw [sum_card_neighbor_inter_comm G B U]
  have hd := special_blocks_pairwise_disjoint G hfree hmin hHigh z hz
  have hsum : (∑ x ∈ U, (G.neighborFinset x ∩ B).card) =
      ∑ t ∈ S, ∑ x ∈ block t, (G.neighborFinset x ∩ B).card := Finset.sum_biUnion hd
  rw [hsum]
  have he := Finset.sum_erase_add S (fun t => ∑ x ∈ block t, (G.neighborFinset x ∩ B).card) hs
  have hi : (∑ x ∈ block s, (G.neighborFinset x ∩ B).card) = 4 := by
    have hh := sum_internalNeighbor_card_eq_twice_induced_edges G B
    have ha := threeHigh_triple_special_internal_edges_eq_two G hfree hmin hHigh hone z hz hu huz hs
    change (G.induce (↑B : Set (Fin 49))).edgeFinset.card = 2 at ha
    rw [ha] at hh
    simpa only [Finset.filter_mem_eq_inter] using hh
  rw [hi] at he
  change (∑ t ∈ S, ∑ x ∈ block t, (G.neighborFinset x ∩ B).card) =
    4 + (∑ t ∈ S.erase s, ∑ x ∈ block t, (G.neighborFinset x ∩ B).card)
  omega

theorem threeHigh_triple_special_union_edges_twenty_or_twentyOne :
    let U := threeHighTripleSpecialUnion G z
    (G.induce (↑U : Set (Fin 49))).edgeFinset.card = 20 ∨
      (G.induce (↑U : Set (Fin 49))).edgeFinset.card = 21 := by
  classical
  let S := threeHighTripleSpecialSet G z
  let U := threeHighTripleSpecialUnion G z
  let block := fun t => G.neighborFinset t ∩ threeHighTripleEmptySet G
  let f := fun t => ∑ x ∈ block t, (G.neighborFinset x ∩ U).card
  change (G.induce (↑U : Set (Fin 49))).edgeFinset.card = 20 ∨
    (G.induce (↑U : Set (Fin 49))).edgeFinset.card = 21
  have hSc : S.card = 3 := threeHigh_triple_special_singleton_count G hfree hmin hHigh z hz
  have hf (s : Fin 49) (hs : s ∈ S) : 13 ≤ f s ∧ f s ≤ 14 := by
    have hi := threeHigh_triple_special_union_incidence G hfree hmin hHigh hone z hz hu huz hs
    have hc := threeHigh_triple_special_cross_mass_bounds G hfree hmin hHigh hone z hz hu huz hs
    change f s = 4 + threeHighTripleBlockCrossMass G z s at hi
    omega
  have hlo : 39 ≤ ∑ s ∈ S, f s := by
    calc
      39 = ∑ _s ∈ S, 13 := by simp [hSc]
      _ ≤ _ := Finset.sum_le_sum (fun s hs => (hf s hs).1)
  have hhi : (∑ s ∈ S, f s) ≤ 42 := by
    calc
      _ ≤ ∑ _s ∈ S, 14 := Finset.sum_le_sum (fun s hs => (hf s hs).2)
      _ = 42 := by simp [hSc]
  have hsum : (∑ x ∈ U, (G.neighborFinset x ∩ U).card) = ∑ s ∈ S, f s :=
    Finset.sum_biUnion (special_blocks_pairwise_disjoint G hfree hmin hHigh z hz)
  have hh := sum_internalNeighbor_card_eq_twice_induced_edges G U
  simp only [Finset.filter_mem_eq_inter] at hh
  rw [hsum] at hh
  omega

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_special_union_incidence
#print axioms Erdos85.threeHigh_triple_special_union_edges_twenty_or_twentyOne
