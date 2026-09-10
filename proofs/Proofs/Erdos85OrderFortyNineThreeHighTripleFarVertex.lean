import Proofs.Erdos85OrderFortyNineThreeHighTripleSecondaryMatching

/-! Three-block capacity forces each far secondary vertex to hit the secondary set. -/
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
include hfree hmin hHigh hone

theorem threeHigh_triple_empty_special_union_neighbor_bound
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {v : Fin 49} (hv : v ∈ threeHighTripleEmptySet G) :
    (G.neighborFinset v ∩ threeHighTripleSpecialUnion G z).card ≤ 3 := by
  classical
  let S := threeHighTripleSpecialSet G z
  let E := threeHighTripleEmptySet G
  have hS : S.card = 3 := threeHigh_triple_special_singleton_count G hfree hmin hHigh z hz
  have heq : G.neighborFinset v ∩ threeHighTripleSpecialUnion G z =
      S.biUnion (fun s => G.neighborFinset v ∩ (G.neighborFinset s ∩ E)) := by
    ext x
    simp only [threeHighTripleSpecialUnion, Finset.mem_inter, Finset.mem_biUnion, S, E]
    aesop
  rw [heq]
  calc
    _ ≤ ∑ s ∈ S, (G.neighborFinset v ∩ (G.neighborFinset s ∩ E)).card := Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ S, 1 := by
      apply Finset.sum_le_sum
      intro s hs
      have hs1 := (Finset.mem_filter.mp hs).2
      have hv0 := (Finset.mem_filter.mp hv).2
      apply neighbor_block_inter_card_le_one G hfree s _ Finset.inter_subset_left
      intro heq
      subst v
      omega
    _ = 3 := by simp [hS]

theorem threeHigh_triple_far_vertex_has_secondary_neighbor
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    {v : Fin 49}
    (hv : v ∈ (threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)) \
      (G.neighborFinset u ∩ threeHighTripleEmptySet G)) :
    ∃ w ∈ threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z), G.Adj v w := by
  classical
  let E := threeHighTripleEmptySet G
  let U := threeHighTripleSpecialUnion G z
  let R := E \ insert u U
  have hvR : v ∈ R := (Finset.mem_sdiff.mp hv).1
  have hvE : v ∈ E := (Finset.mem_sdiff.mp hvR).1
  have hvu : v ≠ u := by
    intro heq
    subst v
    exact (Finset.mem_sdiff.mp hvR).2 (Finset.mem_insert_self _ _)
  have hvnotu : ¬ G.Adj v u := by
    intro ha
    exact (Finset.mem_sdiff.mp hv).2
      (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset u v).mpr ha.symm, hvE⟩)
  have hv0 := (Finset.mem_filter.mp hvE).2
  have hv7 : G.degree v = 7 := by
    have hvlow := (Finset.mem_filter.mp hvE).1
    rcases orderFortyNine_degree_eq_seven_or_eight G hfree hmin (Fintype.card_fin 49) v with h | h
    · exact h
    · exact ((Finset.mem_sdiff.mp hvlow).2 (by simp [orderFortyNineHighVertices, h])).elim
  have hvnotz : ¬ G.Adj v z := by
    intro ha
    have hc := threeHigh_triple_root_empty_neighbor_count G hfree hmin hHigh hone z hz
    change (G.neighborFinset z ∩ E).card = 1 at hc
    have hvm : v ∈ G.neighborFinset z ∩ E :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z v).mpr ha.symm, hvE⟩
    have hum : u ∈ G.neighborFinset z ∩ E :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z u).mpr huz.symm, hu⟩
    exact hvu (Finset.card_le_one.mp hc.le v hvm u hum)
  have hdegree : (G.neighborFinset v ∩ E).card = 4 := by
    have h := threeHigh_triple_empty_neighbor_degree G hfree hmin hHigh hone z hz hv7
    simpa [E, threeHighTripleEmptySet, hv0, hvnotz] using h
  have hcap := threeHigh_triple_empty_special_union_neighbor_bound G hfree hmin hHigh hone z hz hvE
  by_contra hnone
  have hsub : G.neighborFinset v ∩ E ⊆ G.neighborFinset v ∩ U := by
    intro x hx
    have hparts := Finset.mem_inter.mp hx
    have hxnotR : x ∉ R := by
      intro hxR
      exact hnone ⟨x, hxR, (G.mem_neighborFinset v x).mp hparts.1⟩
    have hxin : x ∈ insert u U := by
      by_contra hnot
      exact hxnotR (Finset.mem_sdiff.mpr ⟨hparts.2, hnot⟩)
    refine Finset.mem_inter.mpr ⟨hparts.1, ?_⟩
    rcases Finset.mem_insert.mp hxin with heq | hxU
    · subst x
      exact (hvnotu ((G.mem_neighborFinset v u).mp hparts.1)).elim
    · exact hxU
  have hc := Finset.card_le_card hsub
  change (G.neighborFinset v ∩ U).card ≤ 3 at hcap
  rw [hdegree] at hc
  omega


theorem threeHigh_triple_far_parameter_lower_bound
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (v w : Fin 49)
    (hT : (threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)) \
      (G.neighborFinset u ∩ threeHighTripleEmptySet G) = {v, w}) :
    1 ≤ (G.neighborFinset v ∩ (G.neighborFinset u ∩ threeHighTripleEmptySet G)).card +
      (if G.Adj v w then 1 else 0) := by
  classical
  let R := threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)
  let N := G.neighborFinset u ∩ threeHighTripleEmptySet G
  change R \ N = {v, w} at hT
  have hvT : v ∈ R \ N := by rw [hT]; simp
  obtain ⟨x, hxR, hvx⟩ := threeHigh_triple_far_vertex_has_secondary_neighbor
    G hfree hmin hHigh hone z hz hu huz hvT
  by_cases hxN : x ∈ N
  · have hp : 0 < (G.neighborFinset v ∩ N).card := by
      apply Finset.card_pos.mpr
      exact ⟨x, Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v x).mpr hvx, hxN⟩⟩
    change 1 ≤ (G.neighborFinset v ∩ N).card + _
    omega
  · have hxT : x ∈ R \ N := Finset.mem_sdiff.mpr ⟨hxR, hxN⟩
    rw [hT] at hxT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
    rcases hxT with rfl | rfl
    · exact (hvx.ne rfl).elim
    · rw [if_pos hvx]
      omega

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_empty_special_union_neighbor_bound
#print axioms Erdos85.threeHigh_triple_far_vertex_has_secondary_neighbor

#print axioms Erdos85.threeHigh_triple_far_parameter_lower_bound
