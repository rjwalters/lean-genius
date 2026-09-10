import Proofs.Erdos85OrderFortyNineThreeHighTripleBlockCapacity
import Proofs.Erdos85OrderFortyNineThreeHighTripleSecondaryPartition
import Proofs.Erdos85BranchDeficitSymmetry

/-! The actual special block sends at most seven edges to the secondary set. -/
namespace Erdos85
open SimpleGraph
noncomputable section

theorem neighbor_block_secondary_incidence_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (s u : V) (B R N : Finset V)
    (hB : B ⊆ G.neighborFinset s) (hN : N ⊆ G.neighborFinset u)
    (hNR : N ⊆ R) (hu : u ∉ B) (hs : s ∉ R) :
    (∑ x ∈ B, (G.neighborFinset x ∩ R).card) ≤ B.card + (R \ N).card := by
  classical
  have hn := neighbor_block_incidence_le_card G hfree u N B hN hu
  have ht := neighbor_block_incidence_le_card G hfree s B (R \ N) hB
    (fun h => hs (Finset.mem_sdiff.mp h).1)
  rw [sum_card_neighbor_inter_comm G B R]
  have hpart : R = N ∪ (R \ N) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hx
      by_cases hn : x ∈ N
      · exact Or.inl hn
      · exact Or.inr ⟨hx, hn⟩
    · rintro (hx | hx)
      · exact hNR hx
      · exact hx.1
  have hd : Disjoint N (R \ N) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 hx
  conv_lhs => rw [hpart]
  rw [Finset.sum_union hd]
  rw [← sum_card_neighbor_inter_comm G B N]
  exact Nat.add_le_add hn ht

theorem threeHigh_triple_special_secondary_incidence_le_seven
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    {s : Fin 49} (hs : s ∈ threeHighTripleSpecialSet G z) :
    let E := threeHighTripleEmptySet G
    let B := G.neighborFinset s ∩ E
    let R := E \ insert u (threeHighTripleSpecialUnion G z)
    (∑ x ∈ B, (G.neighborFinset x ∩ R).card) ≤ 7 := by
  classical
  let E := threeHighTripleEmptySet G
  let B := G.neighborFinset s ∩ E
  let R := E \ insert u (threeHighTripleSpecialUnion G z)
  let N := G.neighborFinset u ∩ E
  change (∑ x ∈ B, (G.neighborFinset x ∩ R).card) ≤ 7
  have hp := threeHigh_triple_secondary_partition G hfree hmin hHigh hone z hz hu huz
  have hs1 : (orderFortyNineHighSupport G s).card = 1 := (Finset.mem_filter.mp hs).2
  have hsz : G.Adj s z := ((G.mem_neighborFinset z s).mp (Finset.mem_filter.mp hs).1).symm
  have hBc : B.card = 5 := threeHigh_triple_special_empty_count G hfree hmin hHigh hone z hz hs1 hsz
  have huB : u ∉ B := by
    intro hm
    have huU : u ∈ threeHighTripleSpecialUnion G z := Finset.mem_biUnion.mpr ⟨s, hs, hm⟩
    exact hp.2.1 huU
  have hsR : s ∉ R := by
    intro hm
    have hs0 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hm).1).2
    omega
  have hb := neighbor_block_secondary_incidence_bound G hfree s u B R N
    Finset.inter_subset_left Finset.inter_subset_left hp.2.2.2.1 huB hsR
  rw [hBc, hp.2.2.2.2.2] at hb
  exact hb

end
end Erdos85
#print axioms Erdos85.neighbor_block_secondary_incidence_bound
#print axioms Erdos85.threeHigh_triple_special_secondary_incidence_le_seven
